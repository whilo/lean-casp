import TheoryTests
import FirstOrderTests
import Casp

open Casp

namespace CaspTests

def choice : Program := [
  { head := some "p", neg := ["q"] },
  { head := some "q", neg := ["p"] }]

example : Possible choice 0 {pos := ["p"]} := by casp
example : Possible choice 0 {pos := ["q"]} := by casp
#guard (solveAt choice 0 {pos := ["p", "q"]}).isEmpty
#guard (solveAt choice 0 {}).length == 2
#guard solveAt (choice ++ [{head := none, pos := ["p"]}]) 0 {} == [["q"]]
#guard (solveAt [{head := some "p"}, {head := some "z", neg := ["z"]}] 0 {pos := ["p"]}).isEmpty
#guard solveAt [{head := some "p", pos := ["p"]}] 0 {} == [[]]
#guard solveAt [] 0 {} == [[]]
#guard (solveAt [{head := none}] 0 {}).isEmpty

-- Integer counterpart of upstream between_(X) :- X #> 1, X #< 5.
def between : Program := [{head := some "between", guards := [.ge 2, .lt 5]}]
def outside : Query := {neg := ["between"]}
#guard solve between outside == [(⟨none, some 2⟩, []), (⟨some 5, none⟩, [])]
#guard solve between {pos := ["between"]} == [(⟨some 2, some 5⟩, ["between"])]

example (x : Int) (h : 5 ≤ x) : Possible between x outside := by
  refine ⟨[], solve_sound (cell := ⟨some 5, none⟩) (by
    rw [show solve between outside = [(⟨none, some 2⟩, []), (⟨some 5, none⟩, [])] by cbv]
    simp) ?_⟩
  simp [Region.Contains, h]

-- Compare with exhaustive candidate-model checking on a small program corpus.
private def exhaustive (p : Program) (x : Int) (q : Query) :=
  [[], ["p"], ["q"], ["p", "q"]].filter fun m => check p x m && q.matches m

private def rules : List Rule :=
  [none, some "p", some "q"].flatMap fun h =>
    [[], ["p"], ["q"]].flatMap fun ps =>
      [[], ["p"], ["q"]].map fun ns => {head := h, pos := ps, neg := ns}

#guard rules.all fun a => rules.all fun b => Id.run do
  let expected := exhaustive [a,b] 0 {}
  let actual := (solveAt [a,b] 0 {}).map List.mergeSort
  return expected.length == actual.length && expected.all actual.contains

-- Both valid negative queries and incompatible positive/negative requirements.
private def queries : List Query := [
  {}, {pos := ["p"]}, {neg := ["p"]}, {pos := ["p", "q"]},
  {pos := ["p"], neg := ["q"]}, {pos := ["p"], neg := ["p"]},
  {pos := ["missing"]}, {neg := ["missing"]}]

#guard rules.all fun a => rules.all fun b => queries.all fun q =>
  (firstAt [a,b] 0 q).isSome == !(solveAt [a,b] 0 q).isEmpty

-- Bridge two formerly disconnected groups by a denial; search must backtrack.
private def linked : Program := choice ++ [
  {head := some "a", neg := ["b"]}, {head := some "b", neg := ["a"]},
  {head := none, pos := ["p", "a"]}]
#guard (firstAt linked 0 {pos := ["p", "b"]}).isSome
#guard (firstAt linked 0 {pos := ["p", "a"]}).isNone
#guard (firstAt (choice ++ [{head := some "z", neg := ["z"]}]) 0 {pos := ["p"]}).isNone
#guard (firstAt [{head := none}] 0 {}).isNone
#guard [1,2,4,5].all fun x =>
  (firstAt between x outside).isSome == !(solveAt between x outside).isEmpty

#guard firstByRegion between outside == solve between outside
example (x : Int) : Possible choice x {pos := ["p"]} := by casp

example : ¬ Possible choice 0 {pos := ["p", "q"]} := by
  rw [possible_iff_result]
  decide

end CaspTests
