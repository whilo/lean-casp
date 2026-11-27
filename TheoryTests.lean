import Casp
open Casp

namespace TheoryTests

def applicable : Theory.Predicate (List String) where
  name := "applicable"
  holds snap a := a ∈ snap
  decision := fun _ _ => inferInstance

def policy := fo!{ candidate(a); candidate(b); other(c); other(d);
  allowed(X) :- candidate(X), applicable(X);
  second(X) :- candidate(X), applicable(X) }

private def results (r : Except String (List FO.Subst)) :=
  match r with | .ok xs => some xs | .error _ => none

private def calls (p : FO.Program) (q : FO.Body) :=
  match Theory.prepare applicable ["a"] [] p 0 q with
  | .ok (_,n) => some n | .error _ => none

#guard calls policy ask!{allowed(a),second(a)} == some 1
#guard calls policy ask!{allowed(outside)} == some 0
#guard calls policy ask!{other(X)} == some 0
#guard calls policy ask!{not applicable(X)} == some 4
#guard results (Theory.search applicable ["b"] [] policy 0 ask!{allowed(X)}) == some [[("X","b")]]
#guard results (Theory.search applicable ["a"] [] policy 0 ask!{allowed(X)}) == some [[("X","a")]]
#guard results (Theory.search applicable [] [] fo!{applicable(X)} 0 ask!{}) == none

private def agreeSource (p : FO.Program) (q : FO.Body) (snap : List String) : Bool := Id.run do
  let .ok eager := Theory.materialize applicable snap ["a","b"] p | return false
  let .ok xs := Theory.search applicable snap ["a","b"] p 0 q | return false
  let ys := FO.reference ["a","b"] eager 0 q
  return xs.length == ys.length && xs.all ys.contains

private def foRules := fo!{p(X) :- applicable(X); p(X) :- not applicable(X);
  p(X) :- not q(X); q(X) :- not p(X); q(a); :- applicable(b),p(b);
  p :- q(Y), not applicable(Y)}
#guard [[],["a"],["a","b"]].all fun snap => foRules.all fun r => foRules.all fun t =>
  [ask!{},ask!{p(X)},ask!{not p(X)},ask!{applicable(X),not q(X)},ask!{not p}].all
    fun q => agreeSource [r,t] q snap

def forbid : Order.Constraint := ⟨"sync","depends","reverse"⟩

private def pair (a b : String) : Program :=
  [{head := some a, neg := [b]}, {head := some b, neg := [a]}]

private def facts (xs : List String) : Program := xs.map fun a => {head := some a}

private def normalize (ms : List Model) := (ms.map List.mergeSort).mergeSort

private def compareAll (p : Program) (q : Query) (cs : List Order.Constraint) : Bool :=
  let ref := normalize ((solveAt p 0 q).filter fun m => cs.all (·.accepts m))
  [Order.Strategy.finalOnly,.watched].all fun mode =>
    let all := (Order.solve p 0 q cs mode true).1
    let first := (Order.solve p 0 q cs mode).1
    normalize all == ref && first.isEmpty == ref.isEmpty &&
      first.all (fun m => ref.contains m.mergeSort)

private def threeChoices := pair "sync" "async" ++ pair "depends" "independent" ++ pair "reverse" "forward"
#guard compareAll threeChoices {} [forbid]
#guard (Order.solve threeChoices 0 {} [forbid] .watched true).1.length == 7
#guard compareAll (pair "reverse" "forward" ++ facts ["sync","depends"]) {} [forbid]
#guard compareAll (facts ["sync","depends","reverse","unrelated"]) {pos := ["unrelated"]} [forbid]
#guard compareAll threeChoices {pos := ["async","depends","reverse"]} [forbid]
#guard compareAll threeChoices {pos := ["sync","depends","reverse"]} [forbid]
#guard compareAll threeChoices {neg := ["sync"]} [forbid,forbid]
#guard compareAll threeChoices {} [⟨"sync","sync","sync"⟩,⟨"sync","depends","depends"⟩]
#guard compareAll threeChoices {} [⟨"absent","depends","reverse"⟩]
#guard compareAll (threeChoices ++ [{head := some "odd", neg := ["odd"]}]) {} [forbid]
#guard compareAll [] {} [forbid]
#guard (Order.solve (facts ["sync","depends","reverse"]) 0 {} [forbid]).1.isEmpty
#guard (Order.solve threeChoices 0 {} []).1 == (firstAt threeChoices 0 {}).toList

-- Ground constraint joins even otherwise disconnected query slices.
def dispatch : Order.Declaration := ⟨⟨"sync",[]⟩,⟨"depends",[]⟩,⟨"reverse",[]⟩⟩
def program := fo!{ candidate(b); sync; depends; reverse :- applicable(b);
  allowed(X) :- candidate(X), applicable(X) }
#guard results (Order.search applicable ["b"] [] program 0 ask!{candidate(b)} [dispatch]) == some []
#guard results (Order.search applicable [] [] program 0 ask!{candidate(b)} [dispatch]) == some [[]]
#guard results (Order.search applicable ["b"] [] program 0 ask!{allowed(X)} []) == some [[("X","b")]]

private def smallRules : Program := [
  {head := some "sync"}, {head := some "reverse", neg := ["sync"]},
  {head := some "sync", neg := ["reverse"]}, {head := some "depends", pos := ["sync"]},
  {head := some "depends", neg := ["reverse"]}, {head := none, neg := ["depends"]},
  {head := some "reverse", pos := ["reverse"]}, {head := some "reverse", guards := [.ge 1]}]
#guard smallRules.all fun a => smallRules.all fun b => smallRules.all fun c =>
  compareAll [a,b,c] {} [forbid] && compareAll [a,b,c] {neg := ["reverse"]} [forbid]

example : Theory.Answers applicable ["b"] [] policy 0 ask!{allowed(X)} [("X","b")] := by casp

example : Order.Answers applicable [] [] program 0 ask!{candidate(b)} [dispatch] [] := by casp

-- The independent reference treats an unqueried but inconsistent drain as global.
#guard results (Order.reference applicable ["b"] [] program 0 ask!{candidate(b)} [dispatch]) == some []
private def cross : FO.Program := fo!{sync :- not async; async :- not sync;
  depends :- not free; free :- not depends; reverse :- not forward; forward :- not reverse;
  candidate(a); candidate(b); usable(X) :- candidate(X), applicable(X)}
#guard [[],["a"],["b"],["a","b"]].all fun snap =>
  [ask!{usable(X)}, ask!{sync,depends,reverse}, ask!{async,depends,reverse},
   ask!{not usable(X)}, ask!{not forward,not free}].all fun q =>
    [Order.Strategy.finalOnly,.watched].all fun mode =>
      results (Order.search applicable snap [] cross 0 q [dispatch] mode) ==
      results (Order.reference applicable snap [] cross 0 q [dispatch])

#guard calls (fo!{candidate(a); blocked(a); usable(X) :- candidate(X), not blocked(X), applicable(X)}) ask!{usable(a)} == some 0
#guard calls policy ask!{applicable(a), not other(c)} == some 0

private def repeatedCalls : Except String (Nat × Nat × Nat) := do
  let start := Theory.Cache.empty applicable ["a"]
  let (_, cache, n) ← Theory.prepareCached start [] policy 0 ask!{allowed(a)}
  let (_, cache, m) ← Theory.prepareCached cache [] policy 0 ask!{second(a)}
  let (_, _, k) ← Theory.prepareCached cache [] policy 0 ask!{allowed(b)}
  return (n,m,k)

#guard (match repeatedCalls with | .ok (1,0,1) => true | _ => false)

-- A three-drain chain shares a dependency across scopes. Models that satisfy
-- the first constraint may require a different witness in the overlapping group.
#guard compareAll threeChoices {} [forbid, ⟨"async","depends","forward"⟩, ⟨"async","independent","reverse"⟩]

-- The fixed predicate can be watched directly. Both the disconnected scope and
-- its specific argument have to reach the CASP slice even for a ground query.
private def arm (d : String) : Order.Declaration :=
  ⟨⟨"sync",[d]⟩, ⟨"applicable",[d]⟩, ⟨"reversed",[d]⟩⟩
private def twoDrains := fo!{goal; sync(d1); sync(d2); reversed(d2)}
#guard results (Order.search applicable ["d1"] [] twoDrains 0 ask!{goal} [arm "d1",arm "d2"]) == some [[]]
#guard results (Order.search applicable ["d2"] [] twoDrains 0 ask!{goal} [arm "d1",arm "d2"]) == some []
#guard results (Order.search applicable ["d2"] [] twoDrains 0 ask!{goal} [arm "d1"]) == some [[]]

-- Guarded model equivalence with a source-level denial, including an unknown order atom.
#guard normalize (Order.solve threeChoices 0 {} [forbid] .watched true).1 ==
  normalize (solveAt (threeChoices ++ [forbid.denial]) 0 {})
#guard (Order.solve threeChoices 0 {} [forbid] .watched true).2.exclusions > 0
#guard (Order.solve threeChoices 0 {} [forbid] .finalOnly true).2.wakeups == 0

end TheoryTests
