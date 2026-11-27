# Run your first s(CASP) query in Lean

Start in the repository root. For the Prolog commands you need SWI-Prolog with the s(CASP) pack installed (`?- pack_install(scasp).`). For Lean you need `elan` and one initial `lake build`. Each example can run on either side independently.

## Who is allowed?

```prolog
person(ann).
person(bob).
blocked(ann).
allowed(X) :- person(X), not blocked(X).
```

```sh
swipl scasp --query='allowed(X)' Examples/prolog/blocked.pl
lake env lean Examples/Blocked.lean
```

SWI prints `X = bob`. In Lean the corresponding expression is

```lean
#eval (search [] policy 0 ask!{allowed(X)}).1
-- [[("X", "bob")]]
```

`policy` is the same four clauses inside `fo!{…}`, with semicolons separating clauses. Variables still begin with uppercase letters. The first argument `[]` supplies extra domain names. The program already supplies `ann` and `bob`. The integer `0` sets the guard parameter, which these rules never inspect. Search returns a pair of substitutions and planner statistics. Lean's `.1` selects the substitutions. The outer list contains one answer, and its inner list binds one variable. An empty outer list means no answers. A single empty substitution, `[[]]`, means a ground query succeeded. [Prolog source](../Examples/prolog/blocked.pl) · [Lean source](../Examples/Blocked.lean)

## What if X is free under negation?

```sh
swipl scasp --query='not blocked(X)' Examples/prolog/blocked.pl
```

SWI shows a residual constraint (printed as `X ∉ [ann]` in the classic engine). The variable can take any value compatible with that constraint. The second Lean query returns `bob`, the only other name in this program's active domain. The third query explicitly adds `cy` to that domain and returns both `bob` and `cy`. Adding a name gives the solver a possible binding. It does not establish `person(cy)`, so the original rule still only allows Bob. The comparison harness checks agreement by projecting the Prolog answers onto the Lean domain. [Comparison method](../comparison/README.md)

## What does a proof tell me?

In SWI you can inspect the partial model supporting Bob's answer, including `person(bob)` and `not blocked(bob)`, or request a justification tree. The Lean example finishes with a different query for the type checker:

```lean
example : Answers [] policy 0 ask!{allowed(X)} [("X","bob")] := by casp
```

Read this as “there exists a stable model of this finite program in which Bob is allowed.” The tactic supplies a witness and Lean checks it against the source semantics. This proves that one answer is possible. To claim it is the only answer requires an argument covering every other binding. [Lean query interfaces and proof guarantees](library.md)

Next, [run the dispatch example](propagator.md) to see what happens when a constraint becomes a search procedure.
