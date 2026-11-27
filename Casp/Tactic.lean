import Casp.Order
import Lean

namespace Casp

theorem possible_of_checked {p x q} (m : Model)
    (hc : check p x m = true) (hq : q.matches m = true) : Possible p x q :=
  ⟨m, check_sound hc, hq⟩

open Lean Meta Elab Tactic

/-- Run search in compiled Lean and replay only the returned witness in the kernel. -/
elab "casp_ground" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``Possible 3 do
    throwError "casp expects a goal of the form Casp.Possible program integer query"
  let #[p, x, q] := target.getAppArgs | unreachable!
  let searchTerm ← mkAppM ``firstAt #[p, x, q]
  if searchTerm.hasFVar || searchTerm.hasMVar then
    evalTactic (← `(tactic| exact possible_of_result (by rfl)))
    return
  let result ← unsafe evalExpr (Option Model) (← mkAppM ``Option #[mkConst ``Model]) searchTerm
  let some m := result | throwError "casp found no stable model satisfying this query"
  let yes ← mkEqRefl (mkConst ``Bool.true)
  let proof := mkAppN (mkConst ``possible_of_checked) #[p, x, q, toExpr m, yes, yes]
  unless ← (← getMainGoal).checkedAssign proof do
    throwError "kernel replay of the CASP witness failed"
  replaceMainGoal []

elab "casp" : tactic => withMainContext do
  let target ← getMainTarget
  if target.isAppOfArity ``Order.Answers 9 then
    evalTactic (← `(tactic| (refine Order.answers_of_possible (by rfl) (by decide +kernel) (by rfl) ?_; casp_ground)))
  else if target.isAppOfArity ``Theory.Answers 8 then
    evalTactic (← `(tactic| (refine Exists.intro _ ⟨by rfl, ?_⟩; refine FO.answers_of_possible (by decide +kernel) (by rfl) ?_; casp_ground)))
  else if target.isAppOfArity ``FO.Answers 5 then
    evalTactic (← `(tactic| (refine FO.answers_of_possible (by decide +kernel) (by rfl) ?_; casp_ground)))
  else evalTactic (← `(tactic| casp_ground))

end Casp
