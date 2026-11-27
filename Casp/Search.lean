import Casp.Reference

namespace Casp
namespace GroundSearch

structure Literal where
  atom : Atom
  value : Bool
  deriving BEq

def body (r : Rule) : List Literal :=
  r.pos.map (⟨·, true⟩) ++ r.neg.map (⟨·, false⟩)

/-- To falsify a rule body, at least one literal must have the opposite value. -/
def blockers (r : Rule) : List Literal :=
  (body r).map fun l => {l with value := !l.value}

structure Component where
  atoms : List Atom
  rules : Program

/-- Group rules sharing any atom, including body-only atoms and those in denials. -/
def components (p : Program) : List Component :=
  p.foldl (init := []) fun groups r => Id.run do
    let atoms := r.head.toList ++ r.pos ++ r.neg
    let (linked, others) := groups.partition fun g => atoms.any g.atoms.contains
    return ⟨(atoms ++ linked.flatMap Component.atoms).eraseDups,
            r :: linked.flatMap Component.rules⟩ :: others

structure Assignment where
  yes : Model := []
  no : Model := []

def Assignment.has (s : Assignment) (l : Literal) : Bool :=
  (if l.value then s.yes else s.no).contains l.atom

def Assignment.add (s : Assignment) (l : Literal) : Assignment :=
  if l.value then {s with yes := l.atom :: s.yes} else {s with no := l.atom :: s.no}

/-- The next unresolved disjunction, or none at a complete assignment. -/
@[inline] def nextChoice (g : Component) (s : Assignment) (pending : List (List Literal)) :
    Option (List Literal × List (List Literal)) :=
  let needed := pending.filter fun clause => !clause.any s.has
  let unassigned := fun a => !s.yes.contains a && !s.no.contains a
  match needed with
    | clause :: rest => some (clause.filter (fun (l : Literal) => unassigned l.atom), rest)
    | [] => (g.atoms.find? unassigned).map fun a => ([⟨a, false⟩, ⟨a, true⟩], [])

/-- A pending clause is a disjunction. A positive goal chooses a supporting
rule; a negative goal needs a blocker for every defining rule. Revisited
literals use the current assignment. Reduct checking rejects unfounded cycles. -/
def search (g : Component) (x : Int) (fuel : Nat) (s : Assignment)
    (pending : List (List Literal)) : Option Model := Id.run do
  let next := nextChoice g s pending
  let some (choices, rest) := next | return if check g.rules x s.yes then some s.yes else none
  match fuel with
  | 0 => return none
  | n+1 =>
    return choices.findSome? fun lit =>
      let defs := g.rules.filter fun (r : Rule) => r.head == some lit.atom
      let s' := s.add lit
      if lit.value then
        defs.findSome? fun rule =>
          search g x n s' ((body rule).map ([·]) ++ rest)
      else search g x n s' (defs.map blockers ++ rest)

end GroundSearch
open GroundSearch

private def witness (p : Program) (x : Int) (q : Query) : Option Model := do
  let groups := components (p.filter fun r => r.guards.all (Bound.test x))
  let goals : List Literal := q.pos.map (⟨·, true⟩) ++ q.neg.map (⟨·, false⟩)
  if !q.pos.all (fun a => groups.any (fun g => g.atoms.contains a)) then none else
    let (relevant, global) := groups.partition fun g => goals.any (fun l => g.atoms.contains l.atom)
    let mut m := []
    for g in relevant ++ global do
      let queryGoals := goals.filter fun l => g.atoms.contains l.atom
      let denials := g.rules.filter fun r => r.head.isNone
      let part ← search g x g.atoms.length {} (queryGoals.map ([·]) ++ denials.map blockers)
      m := part ++ m
    return m

/-- Find one complete witness, starting at the query. Validate the assembled
model against the original program, including inactive rules and all denials. -/
def firstAt (p : Program) (x : Int) (q : Query) : Option Model :=
  (witness p x q).filter fun m => q.matches m && check p x m

theorem firstAt_sound {p x q m} (h : firstAt p x q = some m) :
    Stable p x m ∧ q.matches m = true := by
  unfold firstAt at h
  cases he : witness p x q with
  | none => simp [he] at h
  | some v =>
    simp only [he, Option.filter_some] at h
    split at h <;> simp_all [Bool.and_eq_true, check_sound]

/-- At most one model per satisfiable cell, with the same residual integer bounds as solve. -/
def firstByRegion (p : Program) (q : Query) : List (Region × Model) :=
  ((regions p).filter (uniform p)).filterMap fun c => (firstAt p c.sample q).map (c, ·)

theorem firstByRegion_sound {p q cell m x} (h : (cell,m) ∈ firstByRegion p q)
    (hx : cell.Contains x) : Stable p x m ∧ q.matches m = true := by
  obtain ⟨c, hc, hm⟩ := List.mem_filterMap.mp h
  obtain ⟨model, hfound, he⟩ := Option.map_eq_some_iff.mp hm
  cases he
  obtain ⟨hs, hq⟩ := firstAt_sound hfound
  exact ⟨(Region.stable_iff_sample (List.mem_filter.mp hc).2 hx).mpr hs, hq⟩

theorem possible_of_first {p x q} (h : (firstAt p x q).isSome = true) :
    Possible p x q := by
  cases he : firstAt p x q with
  | none => simp [he] at h
  | some m => exact ⟨m, firstAt_sound he⟩


end Casp
