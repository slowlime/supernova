# Supernova
*Like Stella but with explosions.*

This is a simple type checker for a subset of the Stella language.

In addition to the core language, the following extensions are also supported:

- `#arithmetic-operations`
- `#comparison-operations`
- `#fixpoint-combinator`
- `#let-bindings`
- `#let-patterns`
- `#letrec-bindings`
- `#lists`
- `#multiparameter-functions`
- `#natural-literals`
- `#nested-function-declarations`
- `#nullary-functions`
- `#nullary-variant-labels`
- `#pairs`
- `#pattern-ascriptions`
- `#records`
- `#sequencing`
- `#structural-patterns`
- `#sum-types`
- `#tuples`
- `#type-ascriptions`
- `#unit-type`
- `#variants`

## Building
*Supernova* is written in Rust, so, like most Rust projects, it uses `cargo` as its build system.
To compile *Supernova*, run:

```
cargo build
```

If everything goes well, you'll find the compiled binary at `target/debug/supernova`.

## Usage
Just give it a path to a Stella file as a command-line argument:

```
target/debug/supernova nats-are-nuts.stella
```

If you don't give it any arguments, it'll read the program from stdin.

If *Supernova* finds an issue with your code, it'll report a diagnostic message (or messages, for extra-naughty files) to stderr and exit with a non-zero code.
Otherwise it'll just finish silently.
