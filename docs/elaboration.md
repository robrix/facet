# Elaboration

Elaboration takes a syntactically valid surface program (resp. declaratio, definition, type, expression, etc) and either yields a semantically valid core program, or fails with an error (hopefully clear and informative enough to suggest a solution). The type language is simple enough that we’re going to ignore it for now and instead focus on the term language, which has some deviations from a standard bidirectional typechecker which warrant discussion.


## Syntax

The syntax is mostly unsurprising, featuring such diverse elements as contexts:

```
Γ ::= ◊           (empty contexts)
    | Γ, x : τ    (term variable assumption)
    | Γ, X : κ    (type variable assumption)
```

Kinds:

```
κ ::= Type         (the kind of types)
    | Interface    (the kind of interfaces)
    | κ -> κ       (type constructor kind)
```

Types:

```
τ ::= {X : κ} -> τ    (universal quantification)
    | X               (type variable)
    | τ -> τ          (function type)
    | [ι̅] τ           (computation type)
    | τ τ             (type constructor application)
    | {τ}             (thunk type)
```

Negative types:

```
N ::= P -> N          (function type)
    | [ι̅] P           (computation type)
```

Positive types:

```
P ::= {X : κ} -> P    (universal quantification)
    | X               (type variable)
    | P P             (type constructor application)
    | {N}             (thunk type)
```

Expressions:

```
e ::= "…"           (string)
    | x             (term variable)
    | { ρ̅ -> e }    (lambda)
    | e e           (application)
```

Patterns:

```
ρ ::= _            (wildcard)
    | x            (variable)
    | (c ρ̅)        (constructor)
    | [e ρ̅ ; k̅]    (effect operation)
    | [x]          (catch-all)
```


## Judgements

Elaboration occurs on both terms and types. The type level elaboration proceeds first, relating well-kinded surface types to core types. These core types are then used to inform the elaboration of terms. Note also that since Facet’s type system is quite simple, we enjoy an entirely inferred kinding judgement.

Elaboration of terms is _specified_ as a single judgement relating surface terms to core terms at a core type. However, it is _performed_ bidrectionally, and thus in practice consists of two judgements, checking and synthesis. We’ll give rules for each of these as convenience allows.


### Typing

```
Γ ⊢ S ~~> T ==> K
```

This judgement describes the elaboration of surface types `S` to core types `T` with synthesized kinds `K`. (The kind language is particularly simple, consisting of the base kinds `Type` and `Interface`, and arrow kinds.)

Note that the same symbols this judgement employs are also used by the term-level synthesis judgement, below. The term and type languages are disjoint, so we are free to overload the symbols without ambiguity (if not _necessarily_ without confusion).

As described above, our kinds are quite simple, so we can elaborate types entirely in synthesis mode. However, it is nevertheless convenient in the implementation to operate bidirectionally in the small, by synthesizing a type’s kind and then immediately checking it against our expectation using the ubiquitous switch rule. For that reason, we can also reference type elaboration in checking mode in premises:

```
Γ ⊢ S ~~> T <== K
```

with the understanding that proof search will immediately switch (as this is the only checking-mode conclusion in the type elaboration judgement) and check the kinds for equality:

```
Γ ⊢ S ~~> T ==> K′   K ≡ K′
---------------------------
     Γ ⊢ S ~~> T <== K
```

(where equality of kinds is syntactic.)


### Elaboration

```
Γ ⊢ M ~~> V : τ
```

This judgement can be recovered by “erasing” the directionality of the two bidirectional judgements by replacing the `<==`/`==>` symbols with `:`. Note that this judgement is in general nondeterministic, and thus should not be considered as specifying an algorithm. (That’s what the bidirectional judgements are for.)


### Checking

```
Γ ⊢ M ~~> V <== τ
```

This judgement is used to elaborate syntax where we need to know the type in advance.


### Synthesis

```
Γ ⊢ M ~~> V ==> τ
```

This judgement is used to elaborate syntax where we can deduce the type from the term itselr, perhaps requiring that we are able to deduce some or all of it from its components.


### Syntax- vs. type-directed

Bidirectional typecheckers are typically _syntax-directed_, meaning that we can typecheck by walking over the input syntax and alternately checking/synthesizing according to what piece of syntax we’re looking at. This has the nice property that there are no _choices_, i.e. no points at which there might be two ways to arrive at a result, each of which could fail independent of the other, and which would therefore require wasteful backtracking.

In Facet’s case, matters are muddied slightly by computations, which are not explicit in the surface syntax for terms, but are instead indicated by the type. That is, a term at type `A` may well elaborate differently than the same syntactic term at type `[…] A`. Note that I’m saying `[…] A`, which embeds `A`, and not (for example) some unrelated type `B`; the distinction is solely on the presence or absence of a computation type around the result type.


### Computation types

Computation types are computations in the CBPV/polarization sense, i.e. negative, and thus are lazily evaluated. The elaborator models this by treating them as a kind of function type mapping products of operations—dictionaries—to the computed result.


## Strategy

Computation types arise in arguments and returns.


### Positive terms

Facet’s implementation isn’t currently polarized, but it’s a good model for thinking about the structure of the system. (The primary difference in the implementation is that we don’t distinguish thunk types; nullary computations are instead encoded as functions from unit.)


#### String literals

```
--------------------------
Γ ⊢ "…" ~~> "…" ==> String
```


#### Thunks

Technically these can’t appear in the surface syntax right now, but here’s the proposed rule. (It bidirectionalizes trivially by replacing `:` with `<==`/`==>` in both premise and conclusion.)

```
     Γ ⊢ M ~~> M′ : T
--------------------------
Γ ⊢ {M} ~~> {M′} : Thunk T
```

Thunks are eliminated by forcing:

```
Γ ⊢ M ~~> M′ : Thunk T
----------------------
  Γ ⊢ M! ~~> M′! : T
```


### Negative terms

#### Functions

Functions are defined using curly braces containing pattern matching clauses. These define not only functions in the typical sense, but also effect handlers, making them (paraphrasing the Frank paper, _Do Be Do Be Do_) a more general sort of coroutining construct. Here’s the pure case (functions without effect handlers), ignoring (for the moment) non-variable patterns, nested lambdas, and multiple clauses:

```
        Γ, x : S ⊢ M ~~> M′ <== T
-----------------------------------------
Γ ⊢ { x -> M } ~~> { x -> M′ } <== S -> T
```

Pure applications, likewise, just distribute the elaboration of the terms while synthesizing the type:

```
Γ ⊢ M ~~> M′ ==> S -> T   Γ ⊢ N ~~> N′ <== S
--------------------------------------------
          Γ ⊢ M N ~~> M′ N′ ==> T
```


### Computations

Things get more interesting once we start talking about arguments and returns at computation types. The critical observation for the elaboration of computations is that a computation type `[σ̅] T` intuitively represents a promise to produce `T`s given facilities for the operations in `σ̅`. Further decomposing that, we have “a promise to produce `T` given _something_,” and “facilities for the operations in `σ̅`.” We already have a connective for producing `T` given _something_: `something -> T` represents precisely such a promise. And for the latter component, we can represent the facilities for an effect’s operations by a dictionary of the operations’ implementations, as provided by a handler.

Thus, we elaborate computation _types_ into functions from dictionaries of effect handlers to the return type:

```
Γ ⊢ σ̅ ~~> σ̅′ <== Interface   Γ ⊢ T ~~> T′ <== Type
--------------------------------------------------
        Γ ⊢ [σ̅] T ~~> [σ̅′] -> T′ ==> Type
```

where `[σ̅]` (to the right of the `~~>`) can now be understood as an n-ary type constructor named `[]` taking zero or more interfaces to a type. (We do not show a type formation rule for this type since it cannot appear in the surface syntax except composed into a computation type, which is already covered by the elaboration judgements.)

The meat of this approach centres on terms. Unlike other types, terms at computation type:

1. have (almost) no corresponding explicit term-level syntax;
2. implicitly embed positive terms by returning them à la CBPV; and
3. propagate part of the context into (some) subterms

The first point means that we can no longer elaborate with a purely syntax-directed algorithm, because the syntax alone doesn’t suffice to determine what sort of term should be output. Instead, a string literal elaborated at `[σ̅] String` should first be elaborated as a `String` before being lifted into the computation via a return; this is an example of the second point in action.

The third point is subtler, and can be decomposed by analyzing the various pieces of syntax which introduce and eliminate dictionaries.


#### Introduction

Introduction of dictionaries occurs when terms are given computation types bringing one or more interfaces into scope. The simplest case is a top-level definition explicitly annotated with a computation type:

```facet
incr2 : [State Int] Int
{ incr ; incr }
```

where `incr : [State Int] Int` increments the mutable variable managed by `State` and returns the new value, and `_ ; _ : {A, B : Type} -> A -> B -> B` is the definition given in `Data.Function`.

Since `incr2` is typed as `[State Int] Int`, we can see that its elaboration must be a function effectively of type `[State Int] -> Int`. Thus, the elaborated definition must wrap the elaborated contents in a lambda binding the dictionary:

```facet
incr2 : [State Int] -> Int
{ [get, put] -> … }
```

Note that the dictionary is fully decomposed into its operations; this implies that effect operations like `get` and `put` are not distinguished constructs (e.g. field projections), but are rather local variables.

Dictionaries are constructed, but not brought into scope, by effect handlers, which can now be understood as functions applying computations (higher-order functions from dictionaries) to the dictionary consisting of their elaborated effect cases.


#### Elimination

Dictionaries’ members are only brought into scope by the elaborated syntax, and are thus implicit in the surface syntax. Therefore, consumption of these dictionaries must also be implicit, part of the elaboration of the body of the computation.

Terms of computation type within the body will have been elaborated to functions from dictionaries, and thus we must resolve the requested dictionaries with any provided by the context, applying them to eliminate the computation.

Continuing with the example from above, we recall that `incr` has type `[State Int] Int`, and is thus such a function. `_ ; _`, on the other hand, is not. Since `_ ; _` is the outermost term, we must therefore propagate the dictionaries as elaboration proceeds inwards. This is in a sense alredy taken care of by the fact that we extended the context (and do not e.g. contract it in the premises of applications), so now all that is left is to ensure that the operands of `_ ; _` are elaborated s.t. they are applied to the appropriate dictionary.

As noted above, the dictionary is brought into scope piecewise; therefore when elaborating the body, we reconstruct (sub-)dictionaries to pass to any terms consuming effects. (This allows them to receive only the operations they require, rather than the dictionary for the entire signature, potentially at the cost of some allocation.) In full, we now have:

```facet
incr2 : [State Int] -> Int
{ [get, put] -> incr [get = get, put = put] ; incr [get = get, put = put] }
```

where the `[x̅ = y̅]` notation in the body is a record (in this case, a dictionary) giving field `x` the value `y`.

Note however that we’ve only looked at function operands; are there other positions where terms of computation type must be eliminated? And how do we account for effect handlers as shadowing outer handlers for the same effect at the same type?

_TBD_


#### Judgements

In order to accomplish this, we need to:

1. elaborate subterms at computation types into applications of the elaborated subterm to the dictionary of operations they require, discovered in the local environment. However, if the position is itself a handler, this is subtler still as the innermost handler should provide the dictionaries, not the outermost.

2. elaborate lambda bodies at computation type into one more lambda binding the dictionary of required operations.


```
Γ, [Dict(σ̅)] ⊢ M ~~> M′ : T
-------------------------------------
Γ ⊢ M ~~> { [Dict(σ̅)] -> M′ } : [σ̅] T
```

Function/value application is standard (i.e. this rule only differs from the standard typechecking rule in using the elaboration judgements in its premise):

```
Γ ⊢ M ~~> M′ : S -> T   Γ ⊢ N ~~> N′ : S
----------------------------------------
Γ ⊢ M N ~~> M′ N′ : T
```

Handler/computation application is standard:

```
Γ ⊢ M ~~> M′ : [σ̅] S -> T   Γ ⊢ N ~~> N′ : [σ̅] S
------------------------------------------------
           Γ ⊢ M N ~~> M′ N′ : T
```

Handler/value application is standard except for a shift of the parameter:

```
Γ ⊢ M ~~> M′ : [σ̅] S -> T   Γ ⊢ N ~~> N′ : S
--------------------------------------------
           Γ ⊢ M N ~~> M′ (↑N′) : T
```

where we can read the negative shift `↑` on terms as sugar for `return` in the CBPV sense, or in practical terms, the constant function sending all inputs to `N′`. (Were this fully polarized, it would additionally require an enclosing thunk; this discussion leaves thunking as an exercise for the code generator.)

Function/computation application is standard except for passing the requirements of the operand through to the conclusion, which in turn means that the elaborated term is itself now a computation lambda.

```
     Γ ⊢ M ~~> M′ : S -> T   Γ ⊢ N ~~> N′ : [σ̅] S
------------------------------------------------------
Γ ⊢ M N ~~> { [Dict(σ̅)] -> M′ (N′ [Dict(σ̅)]) } : [σ̅] T
```

As described thus far, this strategy will result in a lot of unnecessary redices (applications of computation lambdas to dictionaries at intermediate positions within terms). We could certainly rely on normalization to eliminate any non-essential computation lambdas, or we could lean on the context instead.

This requires pushing dictionaries onto the context when elaborating terms at computation type (like any other bound pattern), and then finding them again. Applying a dictionary filling each field with the variable of the same name (e.g. `[get = get, put = put]`) will do this.

Eliminating free computations using the dictionary bound in the context:

```
Γ ⊢ M ~~> { [Dict(σ̅)] -> M′ } : [σ̅] T   Γ ∋ [Dict(σ̅)]
-----------------------------------------------------
     Γ ⊢ M ~~> { [Dict(σ̅)] -> M′ } [Dict(σ̅)] : T
```


#### Examples

1. `modify`

    ```facet
    modify : {S : Type} -> (f : S -> S) -> [State S] Unit
    { put (f get) }
    ```

    ~~>

    ```facet
    modify : {S : Type} -> (S -> S) -> [State S] -> Unit
    { f [get, put] -> put (f get) }
    ```

2. `modify`, with effects in the higher-order function

    ```facet
    modify : {S : Type} -> (f : S -> S) -> [State S] Unit
    { put (f get) }
    ```

    ~~>

    ```facet
    modify : {σ : Interface} -> {S : Type} -> (S -> [σ] -> S) -> [State S, σ] -> Unit
    { f [get, put, σ] -> put (f [σ] get) }
    ```

    Note that this effectively reinstates implicit effect polymorphism.

3. `toOption`

    ```facet
    toOption : {A : Type} -> [Empty] A -> Option A
    { [empty ; _] -> none
    , a           -> some a }
    ```

    ~~>

    ```facet
    toOption : {A : Type} -> ([Empty] -> (A -> Option A) -> Option A) -> Option A
    { a -> a [empty = { _ -> none }] { a -> some a } }
    ```

4. `guard`

    ```facet
    guard : (c : Bool) -> [Empty] Unit
    { if c { unit } { empty } }
    ```

    ~~>

    ```facet
    guard : Bool -> [Empty] -> Unit
    { c [empty] -> if c { unit } { empty } }
    ```

5. `bool`

    ```facet
    bool : {A : Type} -> (e : {A}) -> (t : {A}) -> Bool -> A
    { (true)  -> t!
    , (false) -> e! }
    ```

    ~~>

    ```facet
    bool : {σ : Interface} -> {A : Type} -> {[σ] -> A} -> {[σ] -> A} -> Bool -> [σ] -> A
    { _ t (true)  -> t!
    , e _ (false) -> e! }
    ```

6. `if`

    ```facet
    if : {A : Type} -> (c : Bool) -> (t : {A}) -> (e : {A}) -> A
    { bool e t c }
    ```

    ~~>

    ```facet
    if : {σ : Interface} -> {A : Type} -> Bool -> {[σ] -> A} -> {[σ] -> A} -> [σ] -> A
    { c t e -> bool e t c }
    ```


#### Questions

1. Should `id incr` elaborate to `id (incr dict)` or `id incr dict`?

2. Do the two above potential elaborations of `id incr` differ observationally?

3. What should the strategy be for applying these? Can we do it in `check`, or at least `checkExpr`?

4. We want to elaborate terms at type `[σ̅] T` into lambdas at type `[σ̅] -> T`. What about when the term in question is already at type `[σ̅] T`?

    - We should probably expand thus only when in checking mode.


#### Observations

Elaboration visits the entire tree. Thus, we shouldn’t need to search around the input term for places to apply the rules, but rather apply them as we get to them, suggesting that `checkExpr` and `synthExpr` might be reasonable places to start. Since elaboration is necessarily semantics-preserving, we will have sufficient information at the nested positions to take the necessary actions.
