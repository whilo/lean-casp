import Casp.Order

open Casp

private def forbidden : Order.Constraint := ⟨"sync","depends","reverse"⟩

private def workload (n : Nat) (hasFallback : Bool) : Program := Id.run do
  let choices := (List.range n).map fun i => s!"selected{i}"
  let mut p := [
    {head := some "goal", pos := ["sync","depends"] ++ choices ++ ["reverse"]},
    {head := some "sync", neg := ["async"]}, {head := some "async", neg := ["sync"]},
    {head := some "depends"}, {head := some "reverse"}]
  for (key,i) in choices.zipIdx do
    let l := s!"left{i}"
    let r := s!"right{i}"
    p := p ++ [{head := some key, pos := [l]}, {head := some key, pos := [r]},
      {head := some l, neg := [r]}, {head := some r, neg := [l]}]
  if hasFallback then p := p ++ [{head := some "goal", pos := ["async"]}]
  return p

@[noinline] private def sample (run : Unit → List Model × Order.Stats) :
    IO (Nat × List Model × Order.Stats) := do
  let start ← IO.monoNanosNow
  let (ms,s) := run ()
  let elapsed := (← IO.monoNanosNow) - start
  return (elapsed,ms,s)

private def report (label : String) (p : Program) (cs : List Order.Constraint) (expected : Bool) :
    IO Unit := do
  for mode in [Order.Strategy.finalOnly,.watched] do
    let mut times := #[]
    let mut stats := {}
    for _ in [:9] do
      let (ns, ms, s) ← sample fun _ => Order.solve p 0 {pos := ["goal"]} cs mode
      unless !ms.isEmpty == expected do throw (IO.userError s!"unexpected verdict for {label}")
      stats := s
      times := times.push ns
    IO.println s!"{label},{repr mode},{(times.qsort (· < ·))[4]!},{stats.branchPoints},{stats.assignments},{stats.batches},{stats.wakeups},{stats.exclusions},{stats.conflicts},{stats.finalChecks},{stats.ordinaryGroups}"

private def eligible : Theory.Predicate (Std.HashSet String) where
  name := "applicable"
  holds snapshot a := a ∈ snapshot
  decision := fun _ _ => inferInstance

@[noinline] private def timePlan (run : Unit → FO.Prepared) : IO Nat := do
  let mut times := #[]
  for _ in [:9] do
    let start ← IO.monoNanosNow
    let result := run ()
    let elapsed := (← IO.monoNanosNow) - start
    if result.program.isEmpty then throw (IO.userError "missing prepared rule")
    times := times.push elapsed
  return (times.qsort (· < ·))[4]!

private def predicateBench : IO Unit := do
  let domain := (List.range 1024).map (fun i => s!"node{i}")
  let snapshot := Std.HashSet.ofList domain
  let p : FO.Program := [
    {head := some ⟨"candidate",[.const "node0"]⟩},
    {head := some ⟨"allowed",[.var "X"]⟩,
     pos := [⟨"candidate",[.var "X"]⟩, ⟨"applicable",[.var "X"]⟩]}]
  IO.println "domain,requested,eager_calls,demand_calls,warm_cache_calls,eager_ns,demand_ns,cached_ns"
  for name in ["allowed","candidate"] do
    let q : FO.Body := {pos := [⟨name,[.const "node0"]⟩]}
    let tmpl ← IO.ofExcept (Theory.template "applicable" domain p 0 q)
    let (_, cache, coldMisses) := tmpl.resolveCached (Theory.Cache.empty eligible snapshot)
    let (_, _, warmMisses) := tmpl.resolveCached cache
    let eager ← timePlan fun _ => tmpl.resolveEager (eligible.test snapshot)
    let demand ← timePlan fun _ => tmpl.resolve (eligible.test snapshot)
    let cached ← timePlan fun _ => (tmpl.resolveCached cache).1
    IO.println s!"{domain.length},{name},{tmpl.domain.length},{coldMisses},{warmMisses},{eager},{demand},{cached}"

def main : IO Unit := do
  IO.println "workload,strategy,median_ns,branch_points,assignments,batches,detector_calls,units,early_conflicts,final_checks,plain_groups"
  for n in [0,4,8] do
    report s!"no-answer-{n}" (workload n false) [forbidden] false
    report s!"first-answer-{n}" (workload n true) [forbidden] true
  -- A present detector with live heads, in the same group as the queried fact.
  -- All watched literals stay false on the accepting path.
  let dormant : Program := [{head := some "goal"}, {head := some "sync", pos := ["sync","goal"]},
    {head := some "depends", pos := ["depends"]}, {head := some "reverse", pos := ["reverse"]}]
  report "never-wakes" dormant [forbidden] true
  report "irrelevant-scope" (workload 4 true) [⟨"missing","depends","reverse"⟩] true
  report "ordinary" (workload 4 true) [] true
  predicateBench
