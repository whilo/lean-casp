# Lean CASP

Lean CASP is a runnable experiment in extending answer set programs with logic written in Lean. An application can give a predicate a decidable meaning in Lean, declare which combinations of atoms are admissible, and use proved properties of that declaration to prune search. The demo implements finite-domain, function-free normal programs with default negation, integrity constraints, and guards over one integer parameter.

## Write a logic program inside Lean

`fo!{…}` embeds rules directly in a Lean file. `ask!{…}` embeds a query. Both expand to typed Lean data, so a program can be a function argument, can be assembled with `++`, and can appear in a theorem.

```lean
import Casp
open Casp.FO

def topology := fo!{
  needs(api,worker); needs(worker,db); needs(api,cache);
  prerequisite(S,D) :- needs(S,D);
  prerequisite(S,D) :- needs(S,M), prerequisite(M,D)
}

def health := fo!{
  service(api); service(worker); service(db); service(cache);
  blocked(S) :- incident(S);
  blocked(S) :- prerequisite(S,D), incident(D);
  ready(S) :- service(S), not blocked(S)
}

def outage := topology ++ health ++ fo!{incident(db)}

#eval (search [] outage 0 ask!{ready(S)}).1
-- [[("S", "cache")]]
```

The API has no direct dependency on the database. The recursive rule still finds a path through the worker. Adding one incident therefore withdraws three earlier readiness conclusions. The [full rollout case study](docs/rollout.md) follows the same program through two competing release modes, a freeze, the actual size of the query slice, and a kernel-checked witness. The [syntax guide](docs/syntax.md) shows exactly what each form expands to.

## What the implementation can do

| If you want to… | Run or inspect |
| --- | --- |
| Query recursive rules, join relations, negate a goal with local variables, and change the policy by adding clauses | [Rollout program](Examples/Rollout.lean) |
| Compute all matching stable models of a ground program and prove the enumeration sound and complete | [Reference semantics and solver](Casp/Reference.lean) |
| Find a first witness by searching from the query and checking independent components | [Ground search](Casp/Search.lean) and [finite-domain query planner](Casp/FirstOrder.lean) |
| Compute all integer intervals satisfying a query and prove a result for infinitely many parameter values | [Deployment windows](Examples/Windows.lean) |
| Give a predicate a decidable Lean meaning and prune search with a verified constraint | [Dispatch program and composition theorem](Examples/Dispatch.lean) |
| Turn a successful source-level query into a Lean theorem with `by casp` | [Witness replay tactic](Casp/Tactic.lean) |

The current scope is a finite-domain CASP research library. First-order variables range over names. Arithmetic guards share one integer parameter. SWI s(CASP) also supports structured terms, general residual constraints, and justification trees beyond the interfaces demonstrated here. The exhaustive solver has completeness proofs. General completeness of the optimized query path remains open. [Guarantees by interface](#what-lean-checks)

## Coming from Prolog?

Given `person(ann).`, `person(bob).`, `blocked(ann).`, and the rule below, who is allowed?

```prolog
allowed(X) :- person(X), not blocked(X).
```

SWI s(CASP) answers `allowed(X)` with `X = bob`. The equivalent Lean query
`#eval (search [] policy 0 ask!{allowed(X)}).1` prints `[[("X", "bob")]]`,
one substitution binding `X` to `bob`. Drop the `person(X)` guard and ask
`not blocked(X)` directly, and the difference between a constrained variable
and a finite-domain answer becomes visible.

1. [Run the same clauses in SWI and Lean](docs/from-prolog.md). Start here for syntax, open queries, and how to read the answers.
2. [Turn a denial into a proved propagator](docs/propagator.md). Start here if you already know how to express an integrity constraint and want to see what Lean adds.

## Run the dispatch example

With the Lean toolchain manager `elan` installed, run the following commands. The repository pins Lean 4.36.0 and uses its standard library.

```sh
git clone https://github.com/whilo/lean-casp.git
cd lean-casp
lake build
lake env lean Examples/Dispatch.lean
lake env lean Examples/Rollout.lean
lake env lean Examples/Windows.lean
lake test
```

The example models a UI consumer that depends on a store. A Lean snapshot determines eligibility. Two default rules permit either dispatch order for an eligible consumer. A separate declaration says that a consumer in the same synchronous drain as its dependency cannot run first. The file evaluates three queries with facts and repeats them with a Lean predicate and then asks Lean to check the surviving witness and a general composition theorem. [Runnable example](Examples/Dispatch.lean)

| Query | Enabled constraint | Substitutions |
| --- | --- | --- |
| `reverse(X)` | None | `X = ui` |
| `reverse(X)` | Same-drain dependency order | No answers |
| `forward(X)` | Same-drain dependency order | `X = ui` |

## How the extensions compose

**Give a predicate a meaning.** A `Theory.Predicate σ` supplies a name, a proposition `holds : σ → String → Prop`, and a decision procedure for each snapshot and argument. In the example, `eligible(ui)` means membership in the snapshot. One specification evaluates the predicate over the full active domain and adds its true instances as ordinary facts. The query planner can instead evaluate only the arguments reached by the query and its consistency checks. For a fixed prepared slice, Lean proves that eager evaluation, on-demand evaluation, and reuse of a cache indexed by predicate and snapshot produce the same program. [Predicate implementation and proofs](Casp/Theory.lean)

**State what a valid model must satisfy.** The dispatch constraint forbids the conjunction of three ground atoms. It has a direct translation into an ordinary headless CASP rule. For a base program `P`, guard parameter `x`, model `M`, and any list of these constraints `C`, Lean proves

```text
Stable(P ++ denials(C), x, M)
  ↔ Stable(P, x, M) ∧ every constraint in C accepts M.
```

This gives a composition rule. If two extensions each declare a list of such constraints, the combined program accepts exactly the base stable models that both accept. The lists can share atoms. Both must accept **the same model**. Two separately successful searches could return incompatible witnesses. The runnable example proves this law for arbitrary lists in `DispatchDemo.combine`. It applies to constraints with this denial semantics. A new extension that also derives atoms needs a semantics and a corresponding proof. [Composition theorem](Examples/Dispatch.lean) · [Stable-model equivalence](Casp/Order.lean)

**Use the theorem during search.** Suppose the branch already contains the same-drain and dependency atoms. Every admissible completion must exclude the reverse order. Lean's `exclude_sound` proves this conclusion about all such completions. If all three atoms are present, `conflict_sound` rules out every completion of the branch. The executable detector uses these two cases. Its exclusion remains local to the branch. Constraints that connect choices also connect their search groups so that backtracking can revisit an earlier choice. [Detector and search](Casp/Order.lean)

To apply this pattern to another system, prove the bridge from the program's atoms to that system's invariant. For example, using an existing scheduler theorem would require showing that the encoded drain, dependency, and order atoms refer to the events quantified by that theorem. Here the order condition is declared directly. The implemented interfaces cover one fixed unary Lean predicate per search and lists of ground order constraints.

## What Lean checks

| Question | Evidence |
| --- | --- |
| Does the exhaustive extended evaluator return exactly the specified answers? | `Order.reference_iff` proves both directions against independent full grounding. |
| Can a detector conflict or exclusion discard a valid completion? | `conflict_sound` and `exclude_sound` quantify over models extending the branch's positive assignments. |
| Is a model returned by optimized ground search admissible and does it match the query? | `Order.solve_sound` proves both for either strategy. |
| Can an application obtain a theorem about a particular source answer? | `by casp` replays a witness against full source semantics. See the `Order.Answers` example. |
| Can the optimized path miss an answer? | General completeness of optimized ground search and equivalence of first-order slicing to full grounding remain open. The tests compare complete model and substitution sets on finite corpora. |

The SWI comparison covers the shared finite fragment. It compares 32 verdicts and eleven open-query binding sets (six original fixtures and five tutorial queries) against two pinned s(CASP) engines. The Lean extension tests use the project's independent exhaustive reference. [Regression tests](TheoryTests.lean) · [SWI comparison and reproduction instructions](comparison/README.md)

## Reasoning about cost

Run `lake exe caspTheoryBench` to compare two strategies on identical programs. Both validate complete candidates. The watched strategy also indexes constraints by atom, batches changes to relevant positive assignments, and checks before a choice or at a candidate. With no declarations, ground search dispatches directly to its ordinary implementation. [Benchmark source](TheoryBench.lean)

| Synthetic workload | Final validation only | Watched pruning | What explains the difference |
| --- | ---: | ---: | --- |
| No answer, eight binary choices | 3.81 ms | 0.20 ms | One exclusion cuts branch points from 255 to zero. |
| First answer, four binary choices | 84 µs | 105 µs | Both visit 11 branch points. The watches add work. |
| Registered detector stays dormant | 7.7 µs | 8.9 µs | Zero detector calls. Indexing and dispatch still cost time. |

These are example native medians over nine calls. Compare branch points, literal attempts, detector calls and final checks alongside local wall-clock measurements. Those counts distinguish avoided search from the cost of inspecting a branch. The predicate benchmark separately measures the cost of filling an already prepared slice. On a domain of 1,024 names, the selective query requires 1,024 eager decisions, one on demand, and zero with a warm cache.

For a new extension, account for the cost of the Lean decision procedure, the number of distinct arguments reached, the number of constraints watching a changed atom, and any formerly independent choices its declarations connect. Even a cheap detector can make a first-witness search more expensive when it forces two large groups to search together. These measurements characterize specific workloads. A general asymptotic bound for the composed algorithm is open.

See the [library guide](docs/library.md) for the query language, stable-model reference solver, integer guards, and proof-producing tactic.
