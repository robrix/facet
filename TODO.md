# TODO

_Caveat lector: there are no guarantees of correctness or completeness on the contents of this file._


## Architecture

- Now that we’ve got HOAS (more or less) under control, can we parse into it?

- Can we skip adding `Span` annotations to the AST and instead carry it around in a `Reader` by parsing and elaborating in a single context?

  - Same question re: preserving comments during formatting.

- Provide a more systematic treatment of types/expressions in (meta)context.

- LSP.

- Enriched intermediate languages for optimization.

- Definition-level incremental computation.
  - Definition-level dependency tracking.

- Self-host.

- ✅ Can we eliminate metavariable substitution by instantiating globals against a spine of values directly?


## Language

### General

- Records.

- Some means to distinguish synonyms from definitions (structural vs. nominal typing).

  - Possibly `=`.


### Core

- `let` bindings.

- `letrec` bindings.

- Represent the elaboration of modules with a `letrec` binding a record of definitions.

- ✅ Computations.

- ✅ Effects.

- Eliminate `PAll` patterns, since they complicate the theory enormously by introducing variables which can be of either computation or value type at any particular instantiation.

- Separate effect & value patterns in lambdas. A little more work at elaboration time will make it much easier to deal with the separate computation and value matching.

- Annotate `Expr` with `Span`s for error reporting.

  - Initially, decorate `Expr` itself.

  - Eventually, encode debug info as an effect.

  - Ideally, emit DWARF data.

- Type patterns, for use with type lambdas & probably quantifiers.

- Dictionary patterns, to bind the operations of an effect interface in the scope of a handler.


### Surface

- `let` bindings.

- Effects.

- Group quantifiers of different kinds in a single set of braces.

- Allow binding operator names as local variables.

- Warn if binding a variable with the same name as an in-scope constructor in a pattern match? We can still write `true` when we mean to write `(true)` and be surprised at the results, it just can’t break out from under us.

- First-class documentation.

- First-class literate programming?

- Operator sections using underscores as placeholders: `(_ >> f)`.

- Function sections using underscores as placeholders: `f _ a b`.

- Explicit type applications. Ideally using syntax like `{A}`, but we might need to be careful about this being mistaken for a computation. (E.g. both lambdas and function types use `->`.)

- Explicit type abstractions?

  These aren’t usually necessary due to type variables bound in the signature necessarily being in scope in the body, but there might be cases where you’d want them.

- ✅ Ascription.

- Restore nested, chained pattern matching.

- Support quantifying over effect variables.

- `do`–style notation for lexically flattening nested syntax in CPS.


### Modules

- ✅ Imports.

- Submodules.

- Design the relationship between files and modules. Currently thinking of a file as a metalanguage “script” which _constructs_ a module.

  - Regardless, how does the compiler know where to find the file for any particular import? I want `:load` to load (transitive) dependencies; do we have to relate module names and file paths like `ghc`?

  - For that matter, how does the programmer know?

- ✅ Do we need to wrap the whole file in braces?

- Do we need to declare a module header with every file?

  - A header could be useful for stuff like language levels, versions, etc.

- How do we specify exports?

  - Export nothing by default.

- Are modules “just” records?

- Datatypes and interfaces should introduce local modules, preserved on export.

  cf https://github.com/goldfirere/ghc-proposals/blob/local-modules/proposals/0000-local-modules.rst

- Module parameters.

  - Although note that there’s some relationship between these and effects that should be explored.

- Module (and submodule) -level ambient effects.

  - Extends ubiquitous tools à la “`printf` debugging” to be precisely scoped w/ minimal boilerplate.

  - Extend to module hierarchies/compilation targets?


## Components

### Parser

- ✅ Extend the precedence table for mixfix operators.


### Elaborator

- Emit warnings.

- Continue after errors on a declaration-by-declaration basis.

- Add entire composite patterns to contexts. One entry for the whole pattern at type A, with sub-entries for each sub-pattern at decomposed types.


### Pretty-printer

- ✅ Preserve comments in surface syntax 😱

- Parenthesize operators occurring free in expressions.

- Can we deal with precedence in a more modular way, à la the approach the parser takes (cf https://ptival.github.io/2017/02/25/modular-parser-combinators/)?

- Increase the size of source excerpts so binding sites are visible; alternatively, have multiple excerpts when binding sites are far away.


### Driver

- Formatting.

- Running.

- Compilation.

- LSP.

- Linting.


### Tests

- Should exist 😅
