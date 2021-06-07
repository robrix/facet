# Handlers

Handlers have the general form:

    handle : C̅ -> [E̅] A -> B

Typically, `A` will be parametric, and `B` can be viewed as a function of `A` and the context type(s) `C̅`. We will call `A` the incremental return type—that is, the return type of the action—and `B` the eventual return type—the return type of the handler itself.


Handlers are defined by providing a list of clauses for the constructors in `E̅` and a list of clauses for non-effect values at type `A`. The former define a dictionary for `E̅`, and the latter define a continuation with which to run the body. Ignoring for the moment any context arguments of type `C̅`, that gives us:

    { [o̅ x̅ ; k̅] -> b̅
    , a̅         -> b̅ }

where

    o̅ : X̅ -> X′
    x̅ : X̅
    k̅ : X′ -> [E̅] A
    a̅ : A
    b̅ : B

Note that since `k̅` returns in `[E̅] A`, clauses which use the continuation must call the handler recursively on the result. The sole exception is that if `B` is `[E̅] A`, they can technically call the continuation without calling the handler recursively. Note however that this would be _extremely_ strange as it would amount to handling only the first operation within an effect and allowing the remainder to be handled by the calling context.

For example, we have the following types for the operations of `State S`, `Reader R`, and `Empty`:

```facet
# State S
get : [State S] S
put : S -> [State S] Unit

# Reader R
ask : [Reader R] R
local : {X : Type} -> (R -> R) -> [Reader R] X -> [Reader R] X

# Empty
empty : {X : Type} -> [Empty] X
```

Note that all of these return computation types.

Translating them into CPS yields:

```facet
# State S
get : (S -> [State S] A) -> B
put : S -> (Unit -> [State S] A) -> B

# Reader R
ask : (R -> [Reader R] A) -> B
local : {X : Type} -> (R -> R) -> [Reader R] X -> (X -> [Reader R] A) -> B

# Empty
empty : {X : Type} -> [Empty] X
```


Scoped operations like `local` and `catch` themselves contain `E̅`-actions.


Handlers must be able to:

1. return a value of type `B` directly, without calling the continuation `k`. This implies that the type of handlers must not be universally quantified with respect to its eventual return type.

2. return a value of type `X′` by calling the continuation `k`, thus producing a result of type `A` with effects in `E̅`, which it must therefore handle by calling itself recursively.
