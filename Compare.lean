import Casp
import Lean

open Lean Casp
namespace Compare

deriving instance Lean.ToExpr for Bound
deriving instance Lean.ToExpr for Casp.Rule
deriving instance Lean.ToExpr for Query

structure InputAtom where
  pred : String
  args : List String
  deriving FromJson

structure InputRule where
  head : Option InputAtom
  pos : List InputAtom
  neg : List InputAtom
  deriving FromJson

structure Fixture where
  enumerate : Bool := false
  name : String
  rules : List InputRule
  pos : List InputAtom
  neg : List InputAtom
  deriving FromJson

def InputAtom.read (a : InputAtom) : FO.Atom :=
  ⟨a.pred, a.args.map fun s => if s.toList.head!.isUpper then .var s else .const s⟩

def InputRule.read (r : InputRule) : FO.Rule :=
  {head := r.head.map InputAtom.read, pos := r.pos.map InputAtom.read, neg := r.neg.map InputAtom.read}

@[noinline] private def timed (run : Unit → α) : IO (Nat × α) := do
  let start ← IO.monoNanosNow
  let value := run ()
  let finish ← IO.monoNanosNow
  return (finish - start, value)

private def kernelMedian (env : Environment) (gp : Program) (q : Query) (m : Model) : IO Nat := do
  let args := #[toExpr gp, toExpr (0 : Int), toExpr q]
  let yes := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true)
  let decl := Declaration.thmDecl {
    name := `comparisonWitness, levelParams := [],
    type := mkAppN (mkConst ``Possible) args,
    value := mkAppN (mkConst ``possible_of_checked) (args ++ #[toExpr m, yes, yes])}
  let mut times := #[]
  for _ in [:5] do
    let (elapsed, result) ← timed fun _ => env.toKernelEnv.addDeclCore 0 100000 decl none
    if let .error _ := result then throw (IO.userError "kernel rejected comparison witness")
    times := times.push elapsed
  return (times.qsort (· < ·))[2]!

def run (file : String) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let fixtures ← IO.ofExcept (fromJson? (α := List Fixture) json)
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Casp.Tactic}] {}
  for f in fixtures do
    let p := f.rules.map InputRule.read
    let q : FO.Body := ⟨f.pos.map InputAtom.read, f.neg.map InputAtom.read⟩
    if f.enumerate then
      let rows := (FO.search [] p 0 q).1
      let oracle := FO.reference [] p 0 q
      unless rows.length == oracle.length && oracle.all rows.contains do
        throw (IO.userError s!"reference binding disagreement: {f.name}")
      let values := rows.map fun s => q.vars.filterMap (fun v => s.lookup v)
      IO.println s!"{f.name}\t{(toJson values).compress}"
      continue
    let mut prep := #[]
    let mut warm := #[]
    let mut found := false
    for _ in [:7] do
      let (a, plan) ← timed fun _ => FO.prepare [] p 0 q
      let (_, coldAnswer) ← timed fun _ => plan.candidates.any plan.accepts
      let (b, answer) ← timed fun _ => plan.candidates.any plan.accepts
      unless coldAnswer == answer do throw (IO.userError "unstable Lean verdict")
      found := answer
      prep := prep.push a
      warm := warm.push b
    unless found == !(FO.reference [] p 0 q).isEmpty do
      throw (IO.userError s!"reference disagreement: {f.name}")
    let mut replayNs := "-"
    if found then
      let some m := FO.replay [] p 0 q [] | throw (IO.userError "missing whole-program witness")
      let some gq := FO.instantiateQuery q [] | throw (IO.userError "benchmark expects ground queries")
      replayNs := toString (← kernelMedian env (FO.ground [] p) gq m)
    IO.println s!"{f.name}\t{found}\t{(prep.qsort (· < ·))[3]!}\t{(warm.qsort (· < ·))[3]!}\t{replayNs}"

end Compare

def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "usage: lake exe caspCompare fixtures.json")
  Compare.run file
