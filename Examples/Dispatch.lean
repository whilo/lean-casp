import Casp

open Casp

namespace DispatchDemo

/-- An immutable snapshot lists the consumers eligible for this dispatch. -/
def eligible : Theory.Predicate (List String) where
  name := "eligible"
  holds snapshot consumer := consumer ∈ snapshot
  decision := fun _ _ => inferInstance

def dispatch := fo!{
  consumer(ui); sameDrain(ui,store); dependsOn(ui,store);
  forward(X) :- consumer(X), eligible(X), not reverse(X);
  reverse(X) :- consumer(X), eligible(X), not forward(X)
}

def order : Order.Declaration :=
  ⟨⟨"sameDrain", ["ui","store"]⟩, ⟨"dependsOn", ["ui","store"]⟩, ⟨"reverse", ["ui"]⟩⟩

private def query (q : FO.Body) (ds : List Order.Declaration) :=
  Order.search eligible ["ui"] [] dispatch 0 q ds

-- Read each output as the substitutions that hold in some admissible stable model.
#eval query ask!{reverse(X)} []
#eval query ask!{reverse(X)} [order]
#eval query ask!{forward(X)} [order]

example : Order.Answers eligible ["ui"] [] dispatch 0 ask!{forward(X)} [order] [("X","ui")] := by
  casp

-- Two independently authored lists may constrain the same atoms.
theorem combine {p : Program} {x : Int} {m : Model} (left right : List Order.Constraint) :
    Stable (p ++ (left ++ right).map Order.Constraint.denial) x m ↔
      Order.Admissible p x left m ∧ Order.Admissible p x right m := by
  rw [Order.stable_denials_iff]
  constructor
  · rintro ⟨stable, valid⟩
    exact ⟨⟨stable, fun c hc => valid c (List.mem_append_left _ hc)⟩,
           ⟨stable, fun c hc => valid c (List.mem_append_right _ hc)⟩⟩
  · rintro ⟨⟨stable, hl⟩, ⟨_, hr⟩⟩
    exact ⟨stable, fun c hc => (List.mem_append.mp hc).elim (hl c) (hr c)⟩

end DispatchDemo
