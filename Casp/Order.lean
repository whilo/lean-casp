import Casp.Theory

namespace Casp.Order
open GroundSearch

/-- A scoped order constraint. When the first two atoms hold, the final
atom (the opposite dispatch order) must be absent. -/
structure Constraint where
  sameDrain : Atom
  dependency : Atom
  reverseOrder : Atom
  deriving BEq, Repr

def Constraint.atoms (c : Constraint) := [c.sameDrain, c.dependency, c.reverseOrder].eraseDups

def Constraint.accepts (c : Constraint) (m : Model) := !c.atoms.all m.contains

def Admissible (p : Program) (x : Int) (cs : List Constraint) (m : Model) : Prop :=
  Stable p x m ∧ ∀ c ∈ cs, c.accepts m = true

def Constraint.denial (c : Constraint) : Rule := {head := none, pos := c.atoms}

private theorem closed_append {p x m s} {cs : List Constraint} :
    Closed (p ++ cs.map Constraint.denial) x m s ↔
      Closed p x m s ∧ ∀ c ∈ cs, ¬ ∀ a ∈ c.atoms, s a := by
  constructor
  · intro h
    refine ⟨fun r hr => h r (List.mem_append_left _ hr), ?_⟩
    intro c hc hbody
    exact h c.denial (List.mem_append_right _ (List.mem_map.mpr ⟨c,hc,rfl⟩)) rfl hbody
  · rintro ⟨hc, denies⟩ r hr he hb
    rcases List.mem_append.mp hr with inProg | inCs
    · exact hc r inProg he hb
    · obtain ⟨c, h, rfl⟩ := List.mem_map.mp inCs
      exact denies c h hb

/-- Positive denials filter exactly the admissible stable models and add no support. -/
theorem stable_denials_iff {p x m} {cs : List Constraint} :
    Stable (p ++ cs.map Constraint.denial) x m ↔ Admissible p x cs m := by
  constructor
  · rintro ⟨hc, least⟩
    obtain ⟨base, forbids⟩ := closed_append.mp hc
    refine ⟨⟨base, ?_⟩, ?_⟩
    · intro s hs a ha
      let both := fun a => s a ∧ a ∈ m
      have closedBoth : Closed p x m both := by
        intro r hr he body
        have l := hs r hr he (fun k hk => (body k hk).1)
        have r' := base r hr he (fun k hk => (body k hk).2)
        cases eq : r.head <;> simp_all [both]
      have noBad : ∀ c ∈ cs, ¬ ∀ k ∈ c.atoms, both k :=
        fun c h all => forbids c h (fun k hk => (all k hk).2)
      exact (least both (closed_append.mpr ⟨closedBoth,noBad⟩) a ha).1
    · intro c h
      simpa [Constraint.accepts, List.all_eq_true] using forbids c h
  · rintro ⟨⟨base, least⟩, good⟩
    refine ⟨closed_append.mpr ⟨base, ?_⟩, fun s hs => least s (closed_append.mp hs).1⟩
    intro c h
    simpa [Constraint.accepts, List.all_eq_true] using good c h

inductive Advice where
  | quiet
  | conflict
  | exclude (atom : Atom)
  deriving BEq, Repr

def inspect (c : Constraint) (s : Assignment) : Advice :=
  if c.atoms.any s.no.contains then .quiet else
  match c.atoms.filter (fun a => !s.yes.contains a) with
  | [] => .conflict
  | [a] => .exclude a
  | _ => .quiet

private theorem remaining {c : Constraint} {s : Assignment} {a}
    (ha : a ∈ c.atoms) (h : a ∉ s.yes) :
    a ∈ c.atoms.filter (fun b => !s.yes.contains b) := by simp [ha, h]

/-- The reason is the originating constraint; the detector never needs any
assumption outside its literals. All descendants preserve positive assignments. -/
theorem conflict_sound {c s} (h : inspect c s = .conflict) {m : Model}
    (extendsYes : s.yes ⊆ m) : c.accepts m = false := by
  unfold inspect at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i empty
  simp only [Constraint.accepts, Bool.not_eq_false', List.all_eq_true, List.contains_iff_mem]
  intro a ha
  apply extendsYes
  by_cases known : a ∈ s.yes
  · exact known
  · have bad := remaining ha known
    rw [empty] at bad
    contradiction

theorem exclude_sound {c s a} (h : inspect c s = .exclude a) {m : Model}
    (extendsYes : s.yes ⊆ m) (valid : c.accepts m = true) : a ∉ m := by
  unfold inspect at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i b single
  cases h
  intro hb
  have allIn : c.atoms.all m.contains := List.all_eq_true.mpr (by
    intro k hk
    apply List.contains_iff_mem.mpr
    by_cases known : k ∈ s.yes
    · exact extendsYes known
    · have := remaining hk known
      rw [single] at this
      have eq : k = a := by simpa using this
      exact eq ▸ hb)
  simp [Constraint.accepts, allIn] at valid

inductive Strategy where
  | finalOnly
  | watched
  deriving BEq, Repr

structure Stats where
  assignments : Nat := 0
  branchPoints : Nat := 0
  batches : Nat := 0
  wakeups : Nat := 0
  conflicts : Nat := 0
  exclusions : Nat := 0
  finalChecks : Nat := 0
  ordinaryGroups : Nat := 0
  deriving Repr

private structure Group extends Component where
  constraints : List Constraint := []

/-- Each constraint is a hyperedge connecting only the groups containing its
three literals. An atom with no live rule head cannot participate in a conflict. -/
private def groups (p : Program) (cs : List Constraint) : List Group := Id.run do
  let mut result := (components p).map fun g => (⟨g, []⟩ : Group)
  let heads := Std.HashSet.ofList (p.filterMap Rule.head)
  for c in cs do
    unless c.atoms.all heads.contains do continue
    let (linked, rest) := result.partition fun g => c.atoms.any g.atoms.contains
    let merged : Group := {
      atoms := linked.flatMap (·.atoms)
      rules := linked.flatMap (·.rules)
      constraints := c :: linked.flatMap (·.constraints) }
    result := merged :: rest
  return result

private abbrev Watches := Std.HashMap Atom (List Constraint)

private def watches (cs : List Constraint) : Watches := Id.run do
  let mut index := {}
  for c in cs do
    for a in c.atoms do
      index := index.alter a fun old => some (c :: old.getD [])
  return index

private abbrev Clauses := List (List Literal)

/-- Inspect each dirty constraint once at the checkpoint. -/
private def wake (cs : List Constraint) (s : Assignment) : StateM Stats (Option Clauses) := do
  modify fun t => {t with batches := t.batches + 1}
  let mut units := []
  for c in cs do
    modify fun t => {t with wakeups := t.wakeups + 1}
    match inspect c s with
    | .quiet => pure ()
    | .conflict =>
      modify fun t => {t with conflicts := t.conflicts + 1}
      return none
    | .exclude a =>
      modify fun t => {t with exclusions := t.exclusions + 1}
      units := [⟨a,false⟩] :: units
  return some units

/-- Multiple supporting rules and multiple alternatives both create search branches. -/
private def branching (g : Group) (next : Option (List Literal × Clauses)) : Bool :=
  match next with
  | some ([lit], _) => lit.value && ((g.rules.filter (fun r => r.head == some lit.atom)).length > 1)
  | some (_ :: _ :: _, _) => true
  | _ => false

private def explore (g : Group) (x : Int) (watch : Watches) (all : Bool)
    (fuel : Nat) (s : Assignment) (pending : Clauses)
    (dirty : List Constraint) : StateM Stats (List Model) := do
  let mut next := nextChoice g.toComponent s pending
  let mut queued := dirty
  if !dirty.isEmpty && (next.isNone || branching g next) then
    let some units ← wake dirty s | return []
    queued := []
    if !units.isEmpty then next := nextChoice g.toComponent s (units ++ pending)
  let some (choices, rest) := next | do
    modify fun t => {t with finalChecks := t.finalChecks + 1}
    if g.constraints.all (·.accepts s.yes) && check g.rules x s.yes then return [s.yes]
    return []
  if branching g next then modify fun t => {t with branchPoints := t.branchPoints + 1}
  match fuel with
  | 0 => return []
  | n+1 =>
    let mut results := []
    for lit in choices do
      modify fun t => {t with assignments := t.assignments + 1}
      let s' := s.add lit
      let nextDirty := if lit.value then
          match watch[lit.atom]? with
          | some affected => (affected ++ queued).eraseDups
          | none => queued
        else queued
      let defs := g.rules.filter (fun r => r.head == some lit.atom)
      if lit.value then
        for r in defs do
          let found ← explore g x watch all n s' ((body r).map ([·]) ++ rest) nextDirty
          if !all && !found.isEmpty then return found
          results := found ++ results
      else
        let found ← explore g x watch all n s' (defs.map blockers ++ rest) nextDirty
        if !all && !found.isEmpty then return found
        results := found ++ results
    return results

private def run (p : Program) (x : Int) (q : Query) (cs : List Constraint)
    (strategy : Strategy) (all : Bool) : StateM Stats (List Model) := do
  let gs := groups (p.filter fun r => r.guards.all (Bound.test x)) cs
  if !q.pos.all (fun a => gs.any (fun g => g.atoms.contains a)) then return []
  let goals := q.pos.map (⟨·,true⟩) ++ q.neg.map (⟨·,false⟩)
  let (relevant, other) := gs.partition fun g => goals.any (fun l => g.atoms.contains l.atom)
  let mut models : List Model := [[]]
  for g in relevant ++ other do
    let required := goals.filter (fun l => g.atoms.contains l.atom)
    let pending := required.map ([·]) ++ (g.rules.filter (·.head.isNone)).map blockers
    let found ← if g.constraints.isEmpty && !all then do
        modify fun t => {t with ordinaryGroups := t.ordinaryGroups + 1}
        pure (GroundSearch.search g.toComponent x g.atoms.length {} pending).toList
      else
        explore g x (if strategy == .watched then watches g.constraints else {})
          all g.atoms.length {} pending []
    if found.isEmpty then return []
    let unique := if all then (found.map List.mergeSort).eraseDups else found
    models := models.flatMap fun m => unique.map (· ++ m)
  return models

def solve (p : Program) (x : Int) (q : Query) (cs : List Constraint)
    (strategy := Strategy.watched) (all := false) : List Model × Stats := Id.run do
  if cs.isEmpty then
    return (if all then solveAt p x q else (firstAt p x q).toList, {})
  let result := (run p x q cs strategy all).run {}
  return (result.1.filter (fun m => q.matches m && check p x m && cs.all (·.accepts m)), result.2)

theorem solve_sound {p x q cs strategy all m} (h : m ∈ (solve p x q cs strategy all).1) :
    Admissible p x cs m ∧ q.matches m = true := by
  cases cs with
  | nil =>
    cases all <;> simp [solve] at h
    · obtain ⟨hs, hq⟩ := firstAt_sound h
      exact ⟨⟨hs, by simp⟩, hq⟩
    · obtain ⟨hs, hq⟩ := solveAt_sound h
      exact ⟨⟨hs, by simp⟩, hq⟩
  | cons c cs =>
    simp only [solve, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Id.run, pure,
      List.mem_filter, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨⟨check_sound h.2.1.2, h.2.2⟩, h.2.1.1⟩

end Casp.Order

namespace Casp.Order

/-- Dependency declarations use ordinary source-level predicate names and arguments. -/
structure Declaration where
  sameDrain : FO.Ground
  dependency : FO.Ground
  reverseOrder : FO.Ground
  deriving Inhabited

def Declaration.compile (d : Declaration) : Constraint :=
  let key := fun (g : FO.Ground) => FO.groundKey g.pred g.args
  ⟨key d.sameDrain, key d.dependency, key d.reverseOrder⟩

def search (t : Theory.Predicate σ) (snap : σ) (domain : List String) (p : FO.Program)
    (x : Int) (q : FO.Body) (ds : List Declaration) (strategy := Strategy.watched) :
    Except String (List FO.Subst) := do
  if ds.isEmpty then return ← Theory.search t snap domain p x q
  let required := ds.flatMap fun d => [d.sameDrain,d.dependency,d.reverseOrder]
  let tmpl ← Theory.template t.name domain p x q required
  let plan := tmpl.resolve (t.test snap)
  let cs := ds.map Declaration.compile
  return plan.candidates.filter fun s => (FO.instantiateQuery q s).any fun gq =>
    !(solve plan.program x gq cs strategy).1.isEmpty

/-- Independent reference: evaluate the whole fixed predicate, ground the program,
and filter exhaustive stable models by the declared order condition. -/
def reference (t : Theory.Predicate σ) (snap : σ) (domain : List String) (p : FO.Program)
    (x : Int) (q : FO.Body) (ds : List Declaration) : Except String (List FO.Subst) := do
  let source ← Theory.materialize t snap domain p
  let gp := FO.ground domain source
  let cs := ds.map Declaration.compile
  return (FO.bindings domain source q).filter fun s => (FO.instantiateQuery q s).any fun gq =>
    (solveAt gp x gq).any fun m => cs.all (·.accepts m)

/-- Replay a substitution against the full eager source interpretation with explicit denials. -/
def Answers (t : Theory.Predicate σ) (snap : σ) (domain : List String) (p : FO.Program)
    (x : Int) (q : FO.Body) (ds : List Declaration) (s : FO.Subst) : Prop :=
  ∃ source, Theory.materialize t snap domain p = .ok source ∧
    s ∈ FO.bindings domain source q ∧ ∃ gq, FO.instantiateQuery q s = some gq ∧
    ∃ m, Admissible (FO.ground domain source) x (ds.map Declaration.compile) m ∧ gq.matches m = true

private theorem reference_models {p x q} {cs : List Constraint} :
    (solveAt p x q).any (fun m => cs.all (·.accepts m)) = true ↔
      ∃ m, Admissible p x cs m ∧ q.matches m = true := by
  simp only [List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨m, hm, valid⟩
    obtain ⟨stable, matchesQ⟩ := solveAt_sound hm
    exact ⟨m, ⟨stable, valid⟩, matchesQ⟩
  · rintro ⟨m, ⟨stable, valid⟩, matchesQ⟩
    obtain ⟨n, hn, same⟩ := solveAt_complete stable matchesQ
    refine ⟨n, hn, ?_⟩
    intro c hc
    have heq : n.contains = m.contains := by
      funext a
      apply Bool.eq_iff_iff.mpr
      simpa only [List.contains_iff_mem] using same a
    simpa only [Constraint.accepts, heq] using valid c hc

theorem reference_iff {t : Theory.Predicate σ} {snap domain p x q ds s xs}
    (h : reference t snap domain p x q ds = .ok xs) :
    s ∈ xs ↔ Answers t snap domain p x q ds s := by
  cases src : Theory.materialize t snap domain p with
  | error e => simp [reference, src, bind, Except.bind] at h
  | ok source =>
    simp [reference, src, bind, Except.bind, pure, Except.pure] at h
    subst xs
    simp only [Answers, src, Except.ok.injEq, exists_eq_left', List.mem_filter]
    cases hi : FO.instantiateQuery q s with
    | none => simp
    | some gq =>
      simp only [Option.any_some, Option.some.injEq, exists_eq_left']
      apply and_congr_right
      intro _
      simpa only [List.all_map] using (reference_models (p := FO.ground domain source) (x := x) (q := gq) (cs := ds.map Declaration.compile))

theorem answers_of_possible {t : Theory.Predicate σ} {snap domain p x q ds s source gq}
    (src : Theory.materialize t snap domain p = .ok source)
    (valid : s ∈ FO.bindings domain source q) (instQ : FO.instantiateQuery q s = some gq)
    (h : Possible (FO.ground domain source ++ (ds.map Declaration.compile).map Constraint.denial) x gq) :
    Answers t snap domain p x q ds s := by
  obtain ⟨m, hm, hq⟩ := h
  exact ⟨source, src, valid, gq, instQ, m, stable_denials_iff.mp hm, hq⟩

end Casp.Order
