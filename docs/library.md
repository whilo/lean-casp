# Lean CASP

A Lean library for finite-domain, function-free normal logic programs with
default negation, integrity constraints, and an independent integer guard parameter. Requires Lean 4.36.0 and its standard library.

    lake build
    lake test

```lean
import Casp
open Casp

def choice : Program := [
  { head := some "ada", neg := ["ben"] },
  { head := some "ben", neg := ["ada"] }]

example : Possible choice 0 {pos := ["ada"]} := by casp

def safe : Program := [
  { head := some "safe", guards := [.ge 1, .lt 10] }]

#eval firstByRegion safe {neg := ["safe"]}
-- Two answers with the empty model: x < 1 and x ≥ 10.
```

## First-order programs

```lean
import Casp
open Casp.FO

def policy := fo!{person(ann); person(bob); edge(ann, broken); faulty(broken);
                  blocked(X) :- edge(X,Y), faulty(Y)}
def allowed := ask!{person(X), not blocked(X)}

#eval (search [] policy 0 allowed).1  -- [[("X", "bob")]]
example : Answers [] policy 0 allowed [("X","bob")] := by casp
```

Uppercase identifiers denote variables scoped to one rule or query. Lowercase
arguments and quoted strings denote constants. Semicolons separate rules.
The active domain is the union of supplied values and program constants.
A substitution binds all query variables, in reverse first-occurrence order
(positive literals precede negative literals). A conjunction requires one
stable model for all of its literals. Each returned substitution may have
a different witness.

`FO.prepare` indexes ground facts by predicate, arity, and argument value;
matches rule heads against demanded atoms; joins positive extensional literals;
and enumerates the remaining local variables. Denials and rules with default
negation seed global checks even when the query cannot reach them. Its stats
count visited ground atoms and emitted ground rules. `FO.search` runs the
prepared query. `FO.reference` independently grounds every source rule;
`reference_iff` proves that it returns exactly the source-level answers.
`FO.certified` replays indexed substitutions against that full grounding and
`certified_sound` proves every retained substitution. General equivalence
of the indexed evaluator to full grounding remains to be proved.

For `not blocked(X)`, a body-local `Y` is universally quantified in the dual.
The evaluator requires a false body literal in every applicable ground rule
instance in the same model. `negative_coverage` proves this obligation for
any negative literal of a successfully replayed query. For a unary query,
`complement` returns the domain and its excluded values using indexed search.
`exactResidual` uses exhaustive search and supplies an iff theorem for both
inclusion and exclusion. These complements range over a finite set of names.
Term constructors and relations between multiple arithmetic variables would
require extending the term and constraint languages.

## Lean predicates and order constraints

A unary predicate can take its meaning from a decidable Lean proposition. Its
arguments are active-domain names. A snapshot fixes the interpretation throughout
one search. The predicate name and arity are reserved in rule heads.

```lean
import Casp
open Casp

def applicable : Theory.Predicate (List String) where
  name := "applicable"
  holds snapshot action := action ∈ snapshot
  decision := fun _ _ => inferInstance

def actions := fo!{candidate(a); candidate(b);
  allowed(X) :- candidate(X), applicable(X)}
#eval Theory.search applicable ["b"] [] actions 0 ask!{allowed(X)}
-- .ok [[("X","b")]]
example : Theory.Answers applicable ["b"] [] actions 0 ask!{allowed(X)} [("X","b")] := by casp
```

The planner requests a decision for each distinct interpreted argument reached
after extensional filtering. `Theory.prepareCached` can reuse those decisions
across queries at the same predicate and snapshot. `eager_eq_demand` and
`cached_eq_demand` prove that all three ways of filling a prepared query give the
same ground program.

An `Order.Declaration` gives three ground atoms that cannot jointly hold.
For example, suppose a dependency within a synchronous drain forbids running
its consumer before its producer.

```lean
def orderRule : Order.Declaration :=
  ⟨⟨"sameDrain", ["a","b"]⟩, ⟨"dependsOn", ["b","a"]⟩, ⟨"runsBefore", ["b","a"]⟩⟩
#eval Order.search applicable ["b"] [] actions 0 ask!{allowed(X)} [orderRule]
```

Declaring this condition adds an integrity constraint. `Order.stable_denials_iff`
proves its stable-model meaning. The optional watched strategy sees new positive
assignments to the three atoms. Two can force exclusion of the third. Three give
a conflict. Checks batch before a choice and at a candidate. Both strategies
validate final candidates and can backtrack across choices linked by a declaration.
Ordinary CASP queries use their existing search path.

`Order.reference_iff` characterizes answers from independent full grounding and
exhaustive model filtering. `Order.Answers` goals can be proved with `by casp`.
The optimized ground search has a soundness theorem. Completeness of optimized
search and equivalence of first-order slicing to full grounding are tested
against the reference and remain open proof obligations.

Run `lake exe caspTheoryBench` for first-answer and no-answer timings, branch
and wakeup counts, and cold and warm interpreted-predicate call counts.

## Ground programs

Each atom is a ground name. All guards refer to the same integer parameter.
A rule with head `none` is an integrity constraint. Query literals are
checked together in each model.

## Query interfaces

| Entry point | Result | Guarantee |
| --- | --- | --- |
| `firstAt p x q` | One complete witness at a given integer, or `none` | `firstAt_sound` certifies each returned witness |
| `firstByRegion p q` | Up to one witness per integer interval | `firstByRegion_sound` covers every integer in the returned interval |
| `solveAt p x q` | All matching stable models at a given integer | `solveAt_sound`, `solveAt_complete` |
| `solve p q` | All matching interval/model pairs | `solve_sound`, `solve_complete` |

Completeness is extensional. Every matching stable model occurs up to atom
membership, which is independent of list order and duplicate names.
`possible_iff_result` also lets an empty reference result establish
`¬ Possible p x q`.

The tactic runs first-witness search on closed goals in compiled Lean. It
embeds the resulting atom list into a proof using `check_sound` and kernel
reduction of the witness and query checks. The search trace stays outside
the proof. For open goals that reduce by computation the tactic can use the
reference path.

## Execution

`Casp.Reference` enumerates choices for default-negated atoms and computes
the least closure of each positive reduct. It partitions the integer line
at guard thresholds. The coverage proof relates every integer to a cell
on which every guard has constant truth value.

`Casp.Search` starts from query literals. A positive goal chooses a supporting
rule. A negative goal requires at least one false body literal in each
defining rule. Revisiting an assigned atom is provisional until reduct checking
establishes stability. Rules that share an atom, including atoms in integrity
constraints, are grouped together. Search finds one witness per independent
group and checks their union against the original program. This avoids
enumerating the product of independent choices. Within a connected component
the search can still require exponential time.

The first-witness evaluator has a soundness proof. Agreement on existence with
the complete reference solver is tested across 729 two-rule programs and eight
queries per program. A general completeness proof for this optimized search
remains open. This ground layer also serves as the specification for the
first-order source language.

## Benchmark

Run `lake exe caspBench` for native timings. Each row reports median solver
time over eleven calls, in microseconds. The fixed query asks for a single
fact. The workload adds independent even cycles and optionally an unrelated
odd cycle which makes the whole program inconsistent. The reference column
times `(solveAt p x q).head?`, including materializing its full answer list.
Reference measurements stop at six pairs. Timings exclude tactic elaboration
and kernel proof replay.

The final benchmark section keeps `reach(start,Y)` fixed while adding unrelated
edges. It reports actual emitted rules against the size of full grounding
computed from the workload's rule arities. The SWI comparison has its own
[reproduction instructions and measured results](../comparison/README.md).

## Reference

The choice-cycle, denial, and interval tests are informed by the upstream
[SWI-Prolog/sCASP differential suite](https://github.com/SWI-Prolog/sCASP/blob/ebfa1708f6edf2adadaf752f459a0afff473fdfb/test/test_differential.pl)
and [CLP(Q) tests](https://github.com/SWI-Prolog/sCASP/blob/ebfa1708f6edf2adadaf752f459a0afff473fdfb/test/test_clpq.pl).
Our interval examples use integers. The upstream interval examples use rationals.
See [Constraint Answer Set Programming without Grounding](https://arxiv.org/abs/1804.11162)
for constructive duals, coinduction, and global checks in goal-directed search.
