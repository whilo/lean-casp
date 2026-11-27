# Which services can deploy during a database incident?

Run `lake build` and `lake env lean Examples/Rollout.lean`. The file checks its displayed answers and ends with a Lean proof. The model asks two different questions: which services are ready, and which release modes can be chosen together? [Complete program](../Examples/Rollout.lean)

## From direct dependencies to readiness

The API needs a worker and a cache. The worker needs a database. The two rules for `prerequisite` take the transitive closure of those edges. Asking `prerequisite(api,S)` returns `cache`, `db`, and `worker`. The recursive rule finds the database by joining `needs(api,worker)` with `prerequisite(worker,db)`.

A service is blocked either by its own incident or by one affecting any prerequisite. In the second rule, `D` occurs only in the body. To satisfy `not blocked(api)`, every possible witness for that rule must fail and the direct incident rule must also fail, all in the same model. Finding one healthy dependency is insufficient. Here is how the answers change when the only new clause is `incident(db)`.

| Query | Healthy program | With database incident |
| --- | --- | --- |
| `ready(S)` | api, cache, db, worker | cache |
| `canary` | possible | no answer |
| `immediate` | possible | no answer |

The database has a direct incident, the worker has an affected prerequisite, and the API has an affected indirect prerequisite. The cache survives. The incident adds a fact while withdrawing previously available conclusions, because readiness depends on default negation.

## One successful query can disagree with another

```lean
def modes := fo!{
  canary :- ready(api), not immediate;
  immediate :- ready(api), not canary
}
```

With the API healthy, either release mode can be supported. Yet `ask!{canary, immediate}` has no answer. Each rule needs the other atom to be absent. Searching the two goals separately and combining their witnesses would produce an invalid deployment plan.

The maintenance scenario appends `fo!{changeFreeze; :- changeFreeze, immediate}` to the healthy program. The denial removes the immediate model. The canary model survives because it already had support from its rule. In the outage scenario neither mode survives, since both rules require API readiness.

## How much work did the query planner actually avoid?

The last printed pair is `(23, 114)`. For `ready(S)` during the incident, the indexed planner emits 23 rules. Instantiating the entire same program over the same four names yields 114 rule instances. The three-variable recursive rule alone has 64 possible assignments before filtering on edges. Indexing, joining facts and following demand reduce the ground program sent to search. Global consistency still matters: definitions containing default negation and denials can require work beyond the positive dependencies of the query. Rule counts measure the input to ground search. They do not give a running-time ratio. [First-order planner](../Casp/FirstOrder.lean)

The final `by casp` proof uses full grounding to check that the cache answer has a stable witness. It proves existence for this substitution. The exhaustive reference can answer completeness questions; extending its general completeness guarantee to the indexed evaluator is still an open proof obligation. [Reference guarantees](library.md#query-interfaces)

## A different kind of query: for which integers?

Run `lake env lean Examples/Windows.lean`. This example has two ways to support deployment: a routine window on `[9,17)` and a repair window on `[20,22)`. Asking for the absence of deployment gives three intervals, covering all integers below 9, from 17 through 19, and at least 22. Both rules refer to the same integer parameter. The solver partitions the integer line at the guard thresholds and checks a representative of each cell. The file proves `Possible policy x closed` for **every** integer `x ≥ 22` by applying the interval soundness theorem. [Runnable interval example and proof](../Examples/Windows.lean)
