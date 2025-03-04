pub trait AstRecurse<'src> {
    fn recurse<'ast, V: Visitor<'src, 'ast> + ?Sized>(&'ast self, visitor: &mut V)
    where
        'src: 'ast;

    fn recurse_mut<'ast, V: VisitorMut<'src, 'ast> + ?Sized>(&'ast mut self, visitor: &mut V)
    where
        'src: 'ast;
}

macro_rules! define_visitor {
    {
        use<$src:lifetime, $ast:lifetime>;

        $(
            $kind:ident {
                $(
                    $name:ident($arg:ident: $ty:ty);
                )+
            }
        )+
    } => {
        pub trait Visitor<$src, $ast>
        where
            $src: $ast,
        {
            $(
                $(
                    fn $name(&mut self, $arg: &$ast $ty);
                )+
            )+
        }

        pub trait VisitorMut<$src, $ast>
        where
            $src: $ast,
        {
            $(
                $(
                    fn $name(&mut self, $arg: &$ast mut $ty);
                )+
            )+
        }

        pub trait DefaultVisitor<$src, $ast>
        where
            $src: $ast,
        {
            $(
                define_visitor!(@ $kind {
                    $(
                        $name($arg: &$ast $ty) = recurse;
                    )+
                });
            )+
        }

        #[diagnostic::do_not_recommend]
        impl<$src, $ast, T: ?Sized> Visitor<$src, $ast> for T
        where
            $src: $ast,
            T: DefaultVisitor<$src, $ast>,
        {
            $(
                $(
                    fn $name(&mut self, $arg: &$ast $ty) {
                        <Self as DefaultVisitor<$src, $ast>>::$name(self, $arg);
                    }
                )+
            )+
        }

        pub trait DefaultVisitorMut<$src, $ast>
        where
            $src: $ast,
        {
            $(
                define_visitor!(@ $kind {
                    $(
                        $name($arg: &$ast mut $ty) = recurse_mut;
                    )+
                });
            )+
        }

        #[diagnostic::do_not_recommend]
        impl<$src, $ast, T: ?Sized> VisitorMut<$src, $ast> for T
        where
            $src: $ast,
            T: DefaultVisitorMut<$src, $ast>,
        {
            $(
                $(
                    fn $name(&mut self, $arg: &$ast mut $ty) {
                        <Self as DefaultVisitorMut>::$name(self, $arg);
                    }
                )+
            )+
        }
    };

    (@ rec {
        $(
            $name:ident($arg:ident: $ty:ty) = $recurse:ident;
        )+
    }) => {
        $(
            fn $name(&mut self, $arg: $ty) {
                $arg.$recurse(self);
            }
        )+
    };

    (@ leaf {
        $(
            $name:ident($arg:ident: $ty:ty) = $recurse:ident;
        )+
    }) => {
        $(
            #[allow(unused_variables)]
            fn $name(&mut self, $arg: $ty) {}
        )+
    };
}

define_visitor! {
    use<'src, 'ast>;

    rec {
        visit_decl(decl: super::Decl<'src>);
        visit_ty_expr(ty_expr: super::TyExpr<'src>);
        visit_expr(expr: super::Expr<'src>);
        visit_pat(pat: super::Pat<'src>);
    }

    leaf {
        visit_binding(binding: super::Binding<'src>);
    }
}
