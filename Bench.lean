import Casp.Syntax

open Casp

private def workload (n : Nat) (odd : Bool) : Program :=
  [{head := some "goal"}] ++ (List.range n).flatMap (fun i =>
    let a := s!"p{i}"
    let b := s!"q{i}"
    [{head := some a, neg := [b]}, {head := some b, neg := [a]}]) ++
    (if odd then [{head := some "odd", neg := ["odd"]}] else [])

@[noinline] private def timeWitness (run : Unit → Option Model) : IO (Nat × Bool) := do
  let start ← IO.monoNanosNow
  let result := run ()
  let elapsed := (← IO.monoNanosNow) - start
  return (elapsed / 1000, result.isSome)

private def medianTime (run : Unit → Option Model) (expected : Bool) : IO Nat := do
  let mut samples := #[]
  for _ in [:11] do
    let (us, found) ← timeWitness run
    unless found == expected do throw (IO.userError "unexpected solver result")
    samples := samples.push us
  return (samples.qsort (· < ·))[5]!

/-- Keep the queried component fixed while extending the domain with unrelated edges. -/
private def reachability : IO Unit := do
  IO.println "unrelated_edges,domain,full_rule_instances,emitted_rules,visited_atoms,bindings,prepare_us"
  for n in [0, 8, 32, 64] do
    let noise : FO.Program := (List.range n).map fun i =>
      {head := some ⟨"edge", [.const s!"u{i}", .const s!"v{i}"]⟩}
    let p := fo!{edge(start,b); edge(b,c); reach(X,Y) :- edge(X,Y);
      reach(X,Y) :- edge(X,Z), reach(Z,Y)} ++ noise
    let q := ask!{reach(start,Y)}
    let start ← IO.monoNanosNow
    let plan := FO.prepare [] p 0 q
    let elapsed := (← IO.monoNanosNow) - start
    let found := plan.candidates.filter plan.accepts
    unless found.length == 2 && found.contains [("Y","b")] && found.contains [("Y","c")] do
      throw (IO.userError "selective query returned incorrect bindings")
    let d := (FO.activeDomain [] p).length
    -- n+2 facts, two distinct variables in the base rule, three in the recursive rule.
    let full := n + 2 + d*d + d*d*d
    if n == 0 && full != (FO.ground [] p).length then
      throw (IO.userError "incorrect full-grounding count")
    IO.println s!"{n},{d},{full},{plan.stats.emittedRules},{plan.stats.visitedAtoms},{found.length},{elapsed/1000}"

def main : IO Unit := do
  IO.println "pairs,odd,first_us,reference_us"
  for n in [0, 2, 4, 6, 32, 128] do
    for odd in [false, true] do
      let p := workload n odd
      let q := {pos := ["goal"] : Query}
      let us ← medianTime (fun _ => firstAt p 0 q) (!odd)
      let mut reference := ""
      if n ≤ 6 then
        let refUs ← medianTime (fun _ => (solveAt p 0 q).head?) (!odd)
        reference := toString refUs
      IO.println s!"{n},{odd},{us},{reference}"
  reachability
