// this is based on the algorithm 𝓘 described in
// http://moscova.inria.fr/~maranget/papers/warn/warn.pdf.

use std::collections::VecDeque;
use std::fmt::{self, Display};

use fxhash::FxHashSet;
use num::{BigUint, FromPrimitive};

use crate::ast;
use crate::ast::visit::{AstRecurse, DefaultVisitor};
use crate::diag::DiagCtx;

use super::ty::TyKind;
use super::{Module, PatId, Result, SemaError, TyId};

#[derive(Debug, Clone)]
struct DeconstructedPat {
    ty_id: TyId,
    cons: Cons,
    fields: Vec<DeconstructedPat>,
}

impl DeconstructedPat {
    fn wild(ty_id: TyId) -> Self {
        Self {
            ty_id,
            cons: Cons::Wild,
            fields: vec![],
        }
    }

    fn display(&self, m: &Module<'_>) -> impl Display {
        struct Formatter<'a, 'm, 'ast>(&'a DeconstructedPat, &'m Module<'ast>);

        impl Display for Formatter<'_, '_, '_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let ty = &self.1.tys[self.0.ty_id].kind;

                match &self.0.cons {
                    Cons::Variant(idx) => {
                        let TyKind::Variant(ty) = ty else {
                            unreachable!()
                        };

                        write!(f, "<| {}", ty.elems[*idx].0)?;

                        if let Some(pat) = self.0.fields.first() {
                            write!(f, ": {}", pat.display(self.1))?;
                        }

                        write!(f, " |>")
                    }

                    Cons::Inl => write!(f, "inl({})", self.0.fields[0].display(self.1)),
                    Cons::Inr => write!(f, "inr({})", self.0.fields[0].display(self.1)),

                    Cons::Cons => {
                        let mut elems = vec![];
                        let mut pat = self.0;

                        while pat.cons == Cons::Cons && pat.fields[1].cons == Cons::Cons {
                            elems.push(&pat.fields[0]);
                            pat = &pat.fields[1];
                        }

                        if pat.fields[1].cons == Cons::EmptyList {
                            write!(f, "[")?;

                            for (idx, elem) in elems.iter().enumerate() {
                                if idx > 0 {
                                    write!(f, ", ")?;
                                }

                                write!(f, "{}", elem.display(self.1))?;
                            }

                            write!(f, "]")
                        } else {
                            for elem in &elems {
                                write!(f, "cons({}", elem.display(self.1))?;
                            }

                            write!(
                                f,
                                "cons({}, {})",
                                pat.fields[0].display(self.1),
                                pat.fields[1].display(self.1),
                            )?;

                            for _ in 0..elems.len() {
                                write!(f, ")")?;
                            }

                            Ok(())
                        }
                    }

                    Cons::Succ => write!(f, "succ({})", self.0.fields[0].display(self.1)),

                    Cons::Tuple => {
                        write!(f, "{{")?;

                        for (idx, elem) in self.0.fields.iter().enumerate() {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }

                            write!(f, "{}", elem.display(self.1))?;
                        }

                        write!(f, "}}")
                    }

                    Cons::Record => {
                        let TyKind::Record(ty) = ty else {
                            unreachable!()
                        };

                        write!(f, "{{")?;

                        for (idx, ((field, _), pat)) in
                            ty.elems.iter().zip(&self.0.fields).enumerate()
                        {
                            if idx > 0 {
                                write!(f, ", ")?;
                            }

                            write!(f, "{field}: {}", pat.display(self.1))?;
                        }

                        write!(f, "}}")
                    }

                    Cons::EmptyList => write!(f, "[]"),
                    Cons::Bool(v) => write!(f, "{v}"),
                    Cons::Unit => write!(f, "unit"),
                    Cons::Int(n) => write!(f, "{n}"),
                    Cons::Wild => write!(f, "_"),
                }
            }
        }

        Formatter(self, m)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
enum Cons {
    Variant(usize),
    Inl,
    Inr,
    #[allow(clippy::enum_variant_names, reason = "false positive")]
    Cons,
    Succ,
    Tuple,
    Record,
    EmptyList,
    Bool(bool),
    Unit,
    Int(BigUint),

    #[default]
    Wild,
}

impl Cons {
    fn arity(&self, m: &Module<'_>, ty_id: TyId) -> usize {
        let ty = &m.tys[ty_id].kind;

        match self {
            Cons::Variant(idx) => {
                let TyKind::Variant(ty) = ty else {
                    unreachable!()
                };

                if ty.elems[*idx].1.is_some() { 1 } else { 0 }
            }

            Cons::Inl | Cons::Inr => 1,
            Cons::Cons => 2,
            Cons::Succ => 1,

            Cons::Tuple => {
                let TyKind::Tuple(ty) = ty else {
                    unreachable!()
                };

                ty.elems.len()
            }

            Cons::Record => {
                let TyKind::Record(ty) = ty else {
                    unreachable!()
                };

                ty.elems.len()
            }

            Cons::EmptyList => 0,
            Cons::Bool(_) => 0,
            Cons::Unit => 0,
            Cons::Int(_) => 0,
            Cons::Wild => 0,
        }
    }

    fn field_ty_ids(&self, m: &Module<'_>, ty_id: TyId) -> Vec<TyId> {
        let ty = &m.tys[ty_id].kind;

        match self {
            Cons::Variant(idx) => {
                let TyKind::Variant(ty) = ty else {
                    unreachable!()
                };

                if let Some(inner_ty_id) = ty.elems[*idx].1 {
                    vec![inner_ty_id]
                } else {
                    vec![]
                }
            }

            Cons::Inl => {
                let &TyKind::Sum(lhs_ty_id, _) = ty else {
                    unreachable!()
                };

                vec![lhs_ty_id]
            }

            Cons::Inr => {
                let &TyKind::Sum(_, rhs_ty_id) = ty else {
                    unreachable!()
                };

                vec![rhs_ty_id]
            }

            Cons::Cons => {
                let &TyKind::List(elem_ty_id) = ty else {
                    unreachable!()
                };

                vec![elem_ty_id, ty_id]
            }

            Cons::Succ => {
                vec![m.well_known_tys.nat]
            }

            Cons::Tuple => {
                let TyKind::Tuple(ty) = ty else {
                    unreachable!()
                };

                ty.elems.clone()
            }

            Cons::Record => {
                let TyKind::Record(ty) = ty else {
                    unreachable!()
                };

                ty.elems.iter().map(|&(_, elem_ty_id)| elem_ty_id).collect()
            }

            Cons::EmptyList => vec![],
            Cons::Bool(_) => vec![],
            Cons::Unit => vec![],
            Cons::Int(_) => vec![],
            Cons::Wild => vec![],
        }
    }

    fn wilds(&self, m: &Module<'_>, ty_id: TyId) -> Vec<DeconstructedPat> {
        self.field_ty_ids(m, ty_id)
            .into_iter()
            .map(DeconstructedPat::wild)
            .collect()
    }
}

#[derive(Debug, Clone)]
struct PatMat {
    rows: Vec<PatMatRow>,
    ty_ids: VecDeque<TyId>,
}

impl PatMat {
    fn first_conses<'a>(&'a self, m: &Module<'_>) -> (FxHashSet<&'a Cons>, Option<Cons>) {
        let mut present = FxHashSet::default();

        for row in &self.rows {
            if row.pats[0].cons != Cons::Wild {
                present.insert(&row.pats[0].cons);
            }
        }

        let missing = match &m.tys[self.ty_ids[0]].kind {
            TyKind::Error => unreachable!(),

            TyKind::Unit => [Cons::Unit].into_iter().find(|c| !present.contains(c)),

            TyKind::Bool => [Cons::Bool(false), Cons::Bool(true)]
                .into_iter()
                .find(|c| !present.contains(c)),

            TyKind::Nat => (0..)
                .map(|n| Cons::Int(BigUint::from_u64(n).unwrap()))
                .find(|c| !present.contains(c)),

            TyKind::Sum(_, _) => [Cons::Inl, Cons::Inr]
                .into_iter()
                .find(|c| !present.contains(c)),

            TyKind::Fn(_) => unreachable!(),

            TyKind::Tuple(_) => [Cons::Tuple].into_iter().find(|c| !present.contains(c)),

            TyKind::Record(_) => [Cons::Record].into_iter().find(|c| !present.contains(c)),

            TyKind::Variant(ty) => (0..ty.elems.len())
                .map(Cons::Variant)
                .find(|c| !present.contains(c)),

            TyKind::List(_) => [Cons::Cons, Cons::EmptyList]
                .into_iter()
                .find(|c| !present.contains(c)),
        };

        (present, missing)
    }

    fn make_default(mut self) -> Self {
        self.ty_ids.pop_front();
        self.rows.retain_mut(|row| {
            if row.pats[0].cons == Cons::Wild {
                row.pats.pop_front();

                true
            } else {
                false
            }
        });

        self
    }

    fn specialize(&self, m: &Module<'_>, cons: &Cons) -> Self {
        let head_ty_id = self.ty_ids[0];
        let mut ty_ids = cons.field_ty_ids(m, head_ty_id);
        ty_ids.extend(self.ty_ids.iter().skip(1).copied());

        let mut result = Self {
            rows: vec![],
            ty_ids: ty_ids.into(),
        };

        for row in &self.rows {
            let mut new_row = match &row.pats[0].cons {
                Cons::Wild => cons.wilds(m, head_ty_id),
                c if c == cons => row.pats[0].fields.clone(),
                _ => continue,
            };

            new_row.extend(row.pats.iter().skip(1).cloned());
            result.rows.push(PatMatRow {
                pats: new_row.into(),
            });
        }

        result
    }
}

#[derive(Debug, Clone)]
pub struct PatMatRow {
    pats: VecDeque<DeconstructedPat>,
}

impl PatMatRow {
    fn apply(&self, m: &Module<'_>, cons: Cons, head_ty_id: TyId) -> Self {
        let arity = cons.arity(m, head_ty_id);
        let mut result = vec![DeconstructedPat {
            ty_id: head_ty_id,
            cons,
            fields: self.pats.iter().take(arity).cloned().collect(),
        }];
        result.extend(self.pats.iter().skip(arity).cloned());

        Self {
            pats: result.into(),
        }
    }
}

impl Module<'_> {
    pub(super) fn check_exhaustiveness(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }
}

struct Pass<'ast, 'm, D> {
    m: &'m mut Module<'ast>,
    diag: &'m mut D,
}

impl<'ast, 'm, D: DiagCtx> Pass<'ast, 'm, D> {
    fn new(m: &'m mut Module<'ast>, diag: &'m mut D) -> Self {
        Self { m, diag }
    }

    fn run(mut self) -> Result {
        let decl_ids = self.m.root_decl_ids().collect::<Vec<_>>();
        let mut walker = Walker {
            pass: &mut self,
            result: Ok(()),
        };

        for decl_id in decl_ids {
            walker.visit_decl(walker.pass.m.decls[decl_id].def);
        }

        walker.result
    }

    fn deconstruct_pat(&mut self, pat_id: PatId) -> DeconstructedPat {
        let (cons, fields) = match &self.m.pats[pat_id].def.kind {
            ast::PatKind::Dummy => panic!("encountered a dummy pattern {pat_id:?}"),

            ast::PatKind::Variant(p) => {
                let TyKind::Variant(ty) = &self.m.tys[self.m.pats[pat_id].ty_id].kind else {
                    unreachable!()
                };
                let variant_idx = ty.labels[p.label.as_str()];

                (
                    Cons::Variant(variant_idx),
                    p.pat
                        .as_ref()
                        .map(|pp| self.deconstruct_pat(pp.id))
                        .into_iter()
                        .collect(),
                )
            }

            ast::PatKind::Cons(p) => (
                match p.cons {
                    ast::Cons::Inl => Cons::Inl,
                    ast::Cons::Inr => Cons::Inr,
                    ast::Cons::Cons => Cons::Cons,
                    ast::Cons::Succ => Cons::Succ,
                },
                p.args
                    .iter()
                    .map(|pp| self.deconstruct_pat(pp.id))
                    .collect(),
            ),

            ast::PatKind::Tuple(p) => (
                match self.m.tys[self.m.pats[pat_id].ty_id].kind {
                    TyKind::Tuple(_) => Cons::Tuple,
                    TyKind::Record(_) => Cons::Record,
                    _ => unreachable!(),
                },
                p.elems
                    .iter()
                    .map(|pp| self.deconstruct_pat(pp.id))
                    .collect(),
            ),

            ast::PatKind::Record(p) => {
                let TyKind::Record(ty) = &self.m.tys[self.m.pats[pat_id].ty_id].kind else {
                    unreachable!()
                };

                let mut fields = p.fields.iter().collect::<Vec<_>>();
                fields.sort_unstable_by_key(|field| ty.fields[field.name.as_str()]);

                (
                    Cons::Record,
                    fields
                        .into_iter()
                        .map(|field| self.deconstruct_pat(field.pat.id))
                        .collect(),
                )
            }

            ast::PatKind::List(p) => {
                let ty_id = self.m.pats[pat_id].ty_id;

                // convert fixed-length array patterns to `cons(_, cons(..., cons(_, [])))`.
                p.elems
                    .iter()
                    .rfold((Cons::EmptyList, vec![]), |(cons, fields), elem| {
                        (
                            Cons::Cons,
                            vec![
                                self.deconstruct_pat(elem.id),
                                DeconstructedPat {
                                    ty_id,
                                    cons,
                                    fields,
                                },
                            ],
                        )
                    })
            }

            ast::PatKind::Bool(p) => (Cons::Bool(p.value), vec![]),
            ast::PatKind::Unit(_) => (Cons::Unit, vec![]),
            ast::PatKind::Int(p) => (Cons::Int(p.value.clone()), vec![]),
            ast::PatKind::Name(_) => (Cons::Wild, vec![]),
            ast::PatKind::Ascription(p) => return self.deconstruct_pat(p.pat.id),
            ast::PatKind::Cast(_) => unimplemented!(),
        };

        DeconstructedPat {
            ty_id: self.m.pats[pat_id].ty_id,
            cons,
            fields,
        }
    }

    fn check_exhaustiveness(
        &mut self,
        pat_ids: &[PatId],
        ty_id: TyId,
    ) -> Result<(), DeconstructedPat> {
        let pats = pat_ids
            .iter()
            .map(|&pat_id| self.deconstruct_pat(pat_id))
            .collect::<Vec<_>>();
        let mat = PatMat {
            ty_ids: vec![ty_id].into(),
            rows: pats
                .into_iter()
                .map(|pat| PatMatRow {
                    pats: vec![pat].into(),
                })
                .collect(),
        };

        if let Some(row) = self.do_check_exhaustiveness(mat, 1) {
            Err(row.pats.into_iter().next().unwrap())
        } else {
            Ok(())
        }
    }

    fn do_check_exhaustiveness(&mut self, mat: PatMat, arity: usize) -> Option<PatMatRow> {
        if arity == 0 {
            return if mat.rows.is_empty() {
                Some(PatMatRow {
                    pats: Default::default(),
                })
            } else {
                None
            };
        }

        let (present, missing) = mat.first_conses(self.m);
        let head_ty_id = mat.ty_ids[0];

        if let Some(missing) = missing {
            let present_empty = present.is_empty();
            let mut subrow = self.do_check_exhaustiveness(mat.make_default(), arity - 1)?;

            if present_empty {
                subrow.pats.push_front(DeconstructedPat {
                    ty_id: head_ty_id,
                    cons: Cons::Wild,
                    fields: vec![],
                });
            } else {
                let fields = missing.wilds(self.m, head_ty_id);

                subrow.pats.push_front(DeconstructedPat {
                    ty_id: head_ty_id,
                    cons: missing,
                    fields,
                });
            }

            Some(subrow)
        } else {
            for cons in present {
                let cons_arity = cons.arity(self.m, head_ty_id);
                let smat = mat.specialize(self.m, cons);

                let Some(row) = self.do_check_exhaustiveness(smat, arity + cons_arity - 1) else {
                    continue;
                };

                return Some(row.apply(self.m, cons.clone(), head_ty_id));
            }

            None
        }
    }
}

struct Walker<'ast, 'm, 'p, D> {
    pass: &'p mut Pass<'ast, 'm, D>,
    result: Result,
}

impl<'ast, D: DiagCtx> DefaultVisitor<'ast, 'ast> for Walker<'ast, '_, '_, D> {
    fn visit_expr(&mut self, expr: &'ast ast::Expr<'ast>) {
        match &expr.kind {
            ast::ExprKind::Dummy
            | ast::ExprKind::Bool(_)
            | ast::ExprKind::Unit(_)
            | ast::ExprKind::Int(_)
            | ast::ExprKind::Name(_)
            | ast::ExprKind::Field(_)
            | ast::ExprKind::Fix(_)
            | ast::ExprKind::Apply(_)
            | ast::ExprKind::Ascription(_)
            | ast::ExprKind::Fn(_)
            | ast::ExprKind::Tuple(_)
            | ast::ExprKind::Record(_)
            | ast::ExprKind::Variant(_)
            | ast::ExprKind::List(_)
            | ast::ExprKind::If(_)
            | ast::ExprKind::Seq(_)
            | ast::ExprKind::Unary(_)
            | ast::ExprKind::Binary(_) => {}

            ast::ExprKind::Match(e) => {
                let pat_ids = e.arms.iter().map(|arm| arm.pat.id).collect::<Vec<_>>();

                if let Err(witness) = self
                    .pass
                    .check_exhaustiveness(&pat_ids, self.pass.m.exprs[e.expr.id].ty_id)
                {
                    self.result = Err(());
                    self.pass.diag.emit(SemaError::NonExhaustiveMatchPatterns {
                        location: expr.location,
                        scrutinee_location: e.expr.location,
                        witness: witness.display(self.pass.m).to_string(),
                    });
                }
            }

            ast::ExprKind::Let(e) => {
                for binding in &e.bindings {
                    if let Err(witness) = self.pass.check_exhaustiveness(
                        &[binding.pat.id],
                        self.pass.m.pats[binding.pat.id].ty_id,
                    ) {
                        self.result = Err(());
                        self.pass.diag.emit(SemaError::NonIrrefutableLetPattern {
                            location: binding.pat.location,
                            witness: witness.display(self.pass.m).to_string(),
                        });
                    }
                }
            }

            ast::ExprKind::Address(_) => unimplemented!(),
            ast::ExprKind::Panic(_) => unimplemented!(),
            ast::ExprKind::Throw(_) => unimplemented!(),
            ast::ExprKind::TryCatch(_) => unimplemented!(),
            ast::ExprKind::TryCast(_) => unimplemented!(),
            ast::ExprKind::Fold(_) => unimplemented!(),
            ast::ExprKind::Unfold(_) => unimplemented!(),
            ast::ExprKind::TyApply(_) => unimplemented!(),
            ast::ExprKind::Cast(_) => unimplemented!(),
            ast::ExprKind::Generic(_) => unimplemented!(),
        }

        expr.recurse(self);
    }
}
