import Casp

open Casp

namespace Windows

-- Both windows refer to the same integer, supplied by the caller.
def policy : Program := [
  {head := some "routine", guards := [.ge 9, .lt 17]},
  {head := some "repair", guards := [.ge 20, .lt 22]},
  {head := some "deploy", pos := ["routine"]},
  {head := some "deploy", pos := ["repair"]}]

def closed : Query := {neg := ["deploy"]}
def gaps : List (Region × Model) := [(⟨none, some 9⟩, []), (⟨some 17, some 20⟩, []),
             (⟨some 22, none⟩, [])]

#eval solve policy closed
#guard solve policy closed == gaps

-- One checked interval covers every integer at and beyond the last cutoff.
example (x : Int) (late : 22 ≤ x) : Possible policy x closed := by
  refine ⟨[], solve_sound (cell := ⟨some 22, none⟩) ?_ ?_⟩
  · rw [show solve policy closed = gaps by cbv]
    simp [gaps]
  · simp [Region.Contains, late]

end Windows
