# From an integrity constraint to a proved propagator

A UI consumer depends on a store. Call the order `forward(ui)` if the store runs first, and `reverse(ui)` if the UI runs first. Start with ordinary s(CASP). The program contains `eligible(ui).` and two default rules.

```prolog
forward(X) :- consumer(X), eligible(X), not reverse(X).
reverse(X) :- consumer(X), eligible(X), not forward(X).
```

Either order is possible. Now impose the scheduler rule that a consumer sharing a synchronous drain with its dependency cannot run first. The full constraint fits on one line in a second file.

```prolog
:- sameDrain(ui,store), dependsOn(ui,store), reverse(ui).
```

Run these from the repository root with the s(CASP) pack installed. The first query succeeds with `X = ui`. Loading the order constraint eliminates that answer, and the third query shows the surviving order.

```sh
swipl scasp --query='reverse(X)' Examples/prolog/dispatch.pl
swipl scasp --query='reverse(X)' Examples/prolog/dispatch.pl Examples/prolog/order.pl
swipl scasp --query='forward(X)' Examples/prolog/dispatch.pl Examples/prolog/order.pl
lake env lean Examples/Dispatch.lean
```

The Lean file first runs all three queries with the same eligibility fact and denial. Then it repeats them with two extensions. The answers in each run mean `X = ui`, no answers, and `X = ui`, respectively. [Prolog rules](../Examples/prolog/dispatch.pl) · [Denial](../Examples/prolog/order.pl) · [Lean example and proofs](../Examples/Dispatch.lean)

## Compute a fact in Lean

The application already knows which consumers are eligible. In the second run, `eligible` is a Lean predicate whose declaration says what success means: the supplied name is a member of an immutable snapshot. For the snapshot `["ui"]`, asking about `ui` succeeds. Change the snapshot to `[]` and neither order has support. The host interface takes a ground name, so an open CASP query can lead to several distinct calls. Lean proves that eager, on-demand and cached decisions fill the same prepared slice identically. The cache type records the snapshot used to obtain the answers. [Predicate interface and proofs](../Casp/Theory.lean)

## Why implement a denial twice?

The ordinary denial specifies which complete models are allowed. Now consider a *partial* branch holding `sameDrain(ui,store)` and `dependsOn(ui,store)`, where the order is still unknown. Every completion containing `reverse(ui)` violates the denial. The solver can therefore exclude that one atom immediately. This conclusion alone does not derive `forward(ui)`. The program's own rules still determine whether the remaining choice has support.

`Order.exclude_sound` proves this reasoning for every admissible completion extending the positive assignments. `Order.conflict_sound` handles the case where all three atoms already hold. Backtracking restores the branch assignments. If a premise disappears, its earlier exclusion has no force on the sibling branch. The program can also run with just final validation. That gives us a way to measure what early checking buys. [Detector, strategies and proofs](../Casp/Order.lean)

## What if two extensions touch the same choice?

Suppose one constraint permits only the forward witness while a second permits only the reverse witness. Each constraint tested separately has a solution. Together they have none. This is why the composition theorem in the example fixes **one model**: a model satisfies the combined lists of denials exactly when it is a base stable model accepted by both lists. Overlapping atoms are allowed. The implementation connects the affected search groups so backtracking can revisit a choice that affects both.

This theorem covers the declared denials. Applying an external scheduler theorem would additionally require proving that its events, dependencies, and dispatch order correspond to the program's atoms. The optimized ground solver proves soundness of returned witnesses. Completeness of optimized search and general equivalence of first-order slicing to full grounding remain open. [Composition theorem](../Examples/Dispatch.lean) · [Guarantees by interface](../README.md#what-lean-checks)

## Did the extra reasoning save time?

Run `lake exe caspTheoryBench`. Compare `finalOnly` and `watched` on the same workload. In the eight-choice no-answer example, one early exclusion removes 255 branch points. In the four-choice first-answer example, both strategies visit 11 branch points, and the watched strategy took longer in the published run. Count detector calls and avoided choices alongside elapsed time. For an interpreted predicate, also count distinct requested arguments and the cost of deciding one call. [Measurements and workload definitions](../README.md#reasoning-about-cost)
