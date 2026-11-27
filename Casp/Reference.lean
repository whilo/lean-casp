import Std

namespace Casp

abbrev Atom := String
abbrev Model := List Atom

/-- Bounds on a shared integer parameter. Bounds split the integer line at k. -/
inductive Bound where
  | lt (k : Int)
  | ge (k : Int)
  deriving Repr, DecidableEq

def Bound.test (x : Int) : Bound → Bool
  | .lt k => decide (x < k)
  | .ge k => decide (k ≤ x)

structure Rule where
  head : Option Atom
  pos : List Atom := []
  neg : List Atom := []
  guards : List Bound := []
  deriving Repr

abbrev Program := List Rule

/-- The negative and arithmetic parts select rules in the reduct. -/
def enabled (x : Int) (m : Model) (r : Rule) : Bool :=
  r.guards.all (Bound.test x) && r.neg.all (fun a => !m.contains a)

/-- A model of the reduct obeys every implication, including denials. -/
def Closed (p : Program) (x : Int) (m : Model) (s : Atom → Prop) : Prop :=
  ∀ r ∈ p, enabled x m r = true → (∀ a ∈ r.pos, s a) →
    match r.head with
    | some h => s h
    | none => False

def Stable (p : Program) (x : Int) (m : Model) : Prop :=
  Closed p x m (· ∈ m) ∧ ∀ s, Closed p x m s → ∀ a ∈ m, s a

private def fires (s : Model) (r : Rule) := r.pos.all s.contains

/-- Saturate positive implications. Each ready implication is discharged once. -/
private abbrev Imp := Atom × List Atom
private def ready (known : Model) (i : Imp) := i.2.all known.contains

private def runClosure (pending : List Imp) (known : Model) : Nat → Model
  | 0 => known
  | fuel+1 =>
    match pending.find? (ready known) with
    | none => known
    | some i => runClosure (pending.erase i) (if known.contains i.1 then known else i.1 :: known) fuel

private def implications (rs : Program) : List Imp :=
  rs.filterMap fun r => r.head.map (·, r.pos)

private def derive (rs : Program) :=
  let pending := implications rs
  runClosure pending [] pending.length

private def Respects (rules : List Imp) (s : Atom → Prop) :=
  ∀ i ∈ rules, (∀ a ∈ i.2, s a) → s i.1

private theorem closure_spec (fuel : Nat) (rs : List Imp) (k : Model) (len : rs.length ≤ fuel) :
    let d := runClosure rs k fuel
    k ⊆ d ∧ Respects rs (· ∈ d) ∧
      ∀ s, Respects rs s → (∀ a ∈ k, s a) → ∀ a ∈ d, s a := by
  induction fuel generalizing rs k with
  | zero =>
    have : rs = [] := by simpa using len
    subst rs
    simp [runClosure, Respects]
  | succ n ih =>
    simp only [runClosure]
    split <;> rename_i he
    · refine ⟨fun _ h => h, ?_, fun _ _ hk => hk⟩
      intro i hi hbody
      exact False.elim (List.find?_eq_none.mp he i hi (List.all_eq_true.mpr (by simpa using hbody)))
    · rename_i i
      have hi := List.mem_of_find?_eq_some he
      have hl := List.length_erase_of_mem hi
      let next := if k.contains i.1 then k else i.1 :: k
      have hn (a : Atom) : a ∈ next ↔ a = i.1 ∨ a ∈ k := by
        simp only [next]; split <;> simp_all
      obtain ⟨inc, closed, least⟩ := ih (rs.erase i) next (by omega)
      refine ⟨fun a ha => inc ((hn a).mpr (.inr ha)), ?_, ?_⟩
      · intro j hj hb
        by_cases eq : j = i
        · subst j; exact inc ((hn _).mpr (.inl rfl))
        · exact closed j ((List.mem_erase_of_ne eq).mpr hj) hb
      · intro s hs hk
        apply least s (fun j hj => hs j (List.mem_of_mem_erase hj))
        intro a ha
        rcases (hn a).mp ha with rfl | old
        · exact hs i hi (fun b hb => hk b (by simpa using List.all_eq_true.mp (show i.2.all k.contains = true from List.find?_some (p := ready k) he) b hb))
        · exact hk a old

private theorem mem_imp {rs : Program} {i : Imp} :
    i ∈ implications rs ↔ ∃ r ∈ rs, r.head = some i.1 ∧ r.pos = i.2 := by
  cases i
  simp [implications, Option.map_eq_some_iff, Prod.ext_iff]
  grind

private theorem respects_of_closed {p x m s} (hc : Closed p x m s) :
    Respects (implications (p.filter (enabled x m))) s := by
  intro i hi hb
  obtain ⟨r, hr, hh, hp⟩ := mem_imp.mp hi
  obtain ⟨hr, he⟩ := List.mem_filter.mp hr
  simpa [hh] using hc r hr he (hp ▸ hb)

private theorem derived_in {p x m s} (hc : Closed p x m s) :
    ∀ a ∈ derive (p.filter (enabled x m)), s a :=
  (closure_spec _ _ [] (Nat.le_refl _)).2.2 s (respects_of_closed hc) (by simp)

def check (p : Program) (x : Int) (m : Model) : Bool :=
  let rs := p.filter (enabled x m)
  let d := derive rs
  rs.all (fun r => !fires m r || r.head.any m.contains) && m.all d.contains

theorem check_sound {p x m} (ok : check p x m = true) : Stable p x m := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at ok
  constructor
  · intro r hr he hp
    have h := ok.1 r (List.mem_filter.mpr ⟨hr, he⟩)
    have hf : fires m r = true := List.all_eq_true.mpr (by simpa using hp)
    cases hh : r.head with
    | none => simp [hh, hf] at h
    | some a => simpa [hh, hf] using h
  · intro s hs a ha
    exact derived_in hs a (by simpa using ok.2 a ha)

structure Query where
  pos : List Atom := []
  neg : List Atom := []
  deriving Repr

def Query.matches (q : Query) (m : Model) : Bool :=
  q.pos.all m.contains && q.neg.all (fun a => !m.contains a)

private def subsets : List Atom → List Model
  | [] => [[]]
  | a :: as => let rest := subsets as; rest ++ rest.map (a :: ·)

private def candidates (p : Program) (x : Int) : List Model :=
  (subsets ((p.flatMap Rule.neg).eraseDups)).filterMap fun guess =>
    let rs := p.filter (enabled x guess)
    let m := derive rs
    if (p.flatMap Rule.neg).all (fun a => guess.contains a == m.contains a) then some m else none

/-- Enumerate choices only for atoms occurring under default negation. -/
def solveAt (p : Program) (x : Int) (q : Query) : List Model :=
  (candidates p x).filter fun m => q.matches m && check p x m

/-- Stable models are compared by atom membership, independently of list order. -/
def SameModel (m n : Model) : Prop := ∀ a, a ∈ m ↔ a ∈ n

private theorem contains_eq {m n : Model} {a : Atom} (h : a ∈ m ↔ a ∈ n) :
    m.contains a = n.contains a := Bool.eq_iff_iff.mpr (by simpa using h)

private theorem reduct_eq {p : Program} {m n : Model} (x : Int)
    (h : ∀ a ∈ p.flatMap Rule.neg, m.contains a = n.contains a) :
    p.filter (enabled x m) = p.filter (enabled x n) := by
  apply List.filter_congr
  intro r hr
  unfold enabled
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor <;> intro hb a ha <;> simpa only [h a (List.mem_flatMap.mpr ⟨r, hr, ha⟩)] using hb a ha

private theorem stable_derive {p x m} (hs : Stable p x m) :
    SameModel (derive (p.filter (enabled x m))) m := by
  let rs := p.filter (enabled x m)
  let d := derive rs
  have sub := derived_in hs.1
  have hcl : Closed p x m (· ∈ d) := by
    intro r hr he hb
    cases hh : r.head with
    | some a =>
      apply (closure_spec _ (implications rs) [] (Nat.le_refl _)).2.1 (a, r.pos) _ hb
      exact mem_imp.mpr ⟨r, List.mem_filter.mpr ⟨hr, he⟩, hh, rfl⟩
    | none => simpa [hh] using hs.1 r hr he (fun a ha => sub a (hb a ha))
  exact fun a => ⟨sub a, hs.2 _ hcl a⟩

theorem check_complete {p x m} (hs : Stable p x m) : check p x m = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun a ha => by simpa using (stable_derive hs a).mpr ha⟩
  intro r hr
  obtain ⟨hr, he⟩ := List.mem_filter.mp hr
  by_cases hf : fires m r = true
  · have h := hs.1 r hr he (by simpa using List.all_eq_true.mp hf)
    cases hh : r.head with
    | none => simp [hh] at h
    | some a => simpa [hf, hh] using h
  · simp [hf]

private theorem subset_guess (xs m : Model) :
    xs.filter m.contains ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons a xs ih =>
    by_cases ha : a ∈ m <;> simp [subsets, ha, ih]

theorem solveAt_complete {p x q m} (hs : Stable p x m) (hq : q.matches m = true) :
    ∃ n ∈ solveAt p x q, SameModel n m := by
  let atoms := (p.flatMap Rule.neg).eraseDups
  let g := atoms.filter m.contains
  have hg (a) (ha : a ∈ p.flatMap Rule.neg) : g.contains a = m.contains a := by
    apply contains_eq
    simp [g, atoms, ha]
  let d := derive (p.filter (enabled x m))
  have hd : SameModel d m := stable_derive hs
  have containsD (a) := contains_eq (hd a)
  have filt := reduct_eq x hg
  have verified : check p x d = check p x m := by
    have same := reduct_eq (p := p) (m := d) (n := m) x (fun a _ => containsD a)
    have fireEq (r : Rule) : fires d r = fires m r := List.all_congr rfl containsD
    unfold check
    simp only [same]
    congr 1
    · apply List.all_congr rfl
      intro r
      cases r.head <;> simp [fireEq, hd _]
    · apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      exact ⟨fun h a ha => h a ((hd a).mpr ha), fun h a ha => h a ((hd a).mp ha)⟩
  have queryEq : q.matches d = q.matches m := by
    unfold Query.matches
    congr 1
    · exact List.all_congr rfl containsD
    · exact List.all_congr rfl (fun a => by rw [containsD])
  refine ⟨d, List.mem_filter.mpr ⟨?_, by simp [queryEq, hq, verified, check_complete hs]⟩, hd⟩
  apply List.mem_filterMap.mpr
  refine ⟨g, subset_guess atoms m, ?_⟩
  simp only [filt]
  have agree : (p.flatMap Rule.neg).all (fun a => g.contains a == d.contains a) := by
    apply List.all_eq_true.mpr
    intro a ha
    rw [hg a ha, containsD]
    simp
  simp [d] at agree ⊢
  exact agree

def Possible (p : Program) (x : Int) (q : Query) : Prop :=
  ∃ m, Stable p x m ∧ q.matches m = true

theorem solveAt_sound {p x q m} (h : m ∈ solveAt p x q) :
    Stable p x m ∧ q.matches m = true := by
  have hh := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true] at hh
  obtain ⟨hq, hc⟩ := hh
  exact ⟨check_sound hc, hq⟩

theorem possible_of_result {p x q} (h : (solveAt p x q).isEmpty = false) :
    Possible p x q := by
  cases he : solveAt p x q with
  | nil => simp [he] at h
  | cons m ms => exact ⟨m, solveAt_sound (by simp [he])⟩


/-- Exhaustive search also certifies a negative answer in the finite fragment. -/
theorem possible_iff_result {p x q} : Possible p x q ↔ (solveAt p x q).isEmpty = false := by
  refine ⟨?_, possible_of_result⟩
  rintro ⟨m, hs, hq⟩
  obtain ⟨n, hn, _⟩ := solveAt_complete hs hq
  cases he : solveAt p x q <;> simp_all

structure Region where
  lower : Option Int
  upper : Option Int
  deriving Repr, DecidableEq

/-- Half-open cells [lower,upper). Missing endpoints denote infinity. -/
private def Bound.cut : Bound → Int
  | .lt k | .ge k => k

private def cellsFrom (lower : Option Int) : List Int → List Region
  | [] => [⟨lower, none⟩]
  | k :: ks => ⟨lower, some k⟩ :: cellsFrom (some k) ks

def regions (p : Program) : List Region :=
  cellsFrom none (((p.flatMap Rule.guards).map Bound.cut).eraseDups.mergeSort)

def Region.sample (r : Region) := r.lower.getD ((r.upper.getD 1) - 1)

def Region.Contains (r : Region) (x : Int) : Prop :=
  (∀ l ∈ r.lower, l ≤ x) ∧ (∀ u ∈ r.upper, x < u)

/-- Every value in the cell is on the same side of k as its sample. -/
private def Region.coversCut (r : Region) (k : Int) : Bool :=
  if r.sample < k then r.upper.any (· ≤ k) else r.lower.any (k ≤ ·)

private theorem guard_constant {r : Region} {x : Int} (hx : r.Contains x)
    (g : Bound) (hc : r.coversCut (match g with | .lt k | .ge k => k)) :
    g.test x = g.test r.sample := by
  cases g with
  | lt k | ge k =>
    simp only [Region.coversCut] at hc
    split at hc <;> rename_i h
    · cases hu : r.upper with
      | none => simp [hu] at hc
      | some u =>
        have hxu := hx.2 u (by simp [hu])
        simp [hu] at hc
        simp [Bound.test, show x < k by omega, h] <;> omega
    · cases hl : r.lower with
      | none => simp [hl] at hc
      | some l =>
        have hlx := hx.1 l (by simp [hl])
        simp [hl] at hc
        simp [Bound.test, show ¬ x < k by omega, h] <;> omega

def uniform (p : Program) (r : Region) : Bool :=
  p.all fun rule => rule.guards.all fun | .lt k | .ge k => r.coversCut k

def solve (p : Program) (q : Query) : List (Region × Model) :=
  ((regions p).filter (uniform p)).flatMap fun cell => (solveAt p cell.sample q).map (cell, ·)

theorem Region.stable_iff_sample {p cell x m} (hu : uniform p cell) (hx : cell.Contains x) :
    Stable p x m ↔ Stable p cell.sample m := by
  have same (rule : Rule) (hr : rule ∈ p) : enabled x m rule = enabled cell.sample m rule := by
    have hu := List.all_eq_true.mp hu rule hr
    have hg (g : Bound) (hmem : g ∈ rule.guards) : g.test x = g.test cell.sample := by
      apply guard_constant hx
      cases g <;> exact List.all_eq_true.mp hu _ hmem
    simp only [enabled]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro hh g hmem <;> simpa [hg g hmem] using hh g hmem
  have iffClosed (s : Atom → Prop) : Closed p x m s ↔ Closed p cell.sample m s := by
    constructor <;> intro hcl rule hr hen <;> apply hcl rule hr <;> simpa [same rule hr] using hen
  constructor
  · intro hs
    exact ⟨(iffClosed _).mp hs.1, fun s hc => hs.2 s ((iffClosed s).mpr hc)⟩
  · intro hs
    exact ⟨(iffClosed _).mpr hs.1, fun s hc => hs.2 s ((iffClosed s).mp hc)⟩

theorem solve_sound {p q cell m x} (h : (cell, m) ∈ solve p q)
    (hx : cell.Contains x) : Stable p x m ∧ q.matches m = true := by
  obtain ⟨c, hcell, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨v, hv, he⟩ := List.mem_map.mp hm
  cases he
  obtain ⟨hs, hq⟩ := solveAt_sound hv
  exact ⟨(Region.stable_iff_sample (List.mem_filter.mp hcell).2 hx).mpr hs, hq⟩

private def Separated (c : Region) (k : Int) : Prop :=
  (∃ l ∈ c.lower, k ≤ l) ∨ (∃ u ∈ c.upper, u ≤ k)

private theorem cells_cover (ks : List Int) (sorted : ks.Pairwise (· ≤ ·)) (lo : Option Int)
    (x : Int) (hlo : ∀ l ∈ lo, l ≤ x) (order : ∀ l ∈ lo, ∀ a ∈ ks, l ≤ a) :
    ∃ c ∈ cellsFrom lo ks, c.Contains x ∧
      ∀ k, (∃ l ∈ lo, k ≤ l) ∨ k ∈ ks → Separated c k := by
  induction ks generalizing lo with
  | nil =>
    refine ⟨⟨lo, none⟩, by simp [cellsFrom], ⟨hlo, by simp⟩, ?_⟩
    intro k hk
    simpa [Separated] using hk
  | cons a ks ih =>
    obtain ⟨ahead, tail⟩ := List.pairwise_cons.mp sorted
    by_cases h : x < a
    · refine ⟨⟨lo, some a⟩, by simp [cellsFrom], ⟨hlo, by simpa⟩, ?_⟩
      intro k hk
      rcases hk with old | mem
      · exact .inl old
      · exact .inr ⟨a, rfl, (List.mem_cons.mp mem).elim (fun e => by omega) (ahead k)⟩
    · obtain ⟨c, hc, hx, sep⟩ := ih tail (some a) (by simp; omega) (by simpa using ahead)
      refine ⟨c, List.mem_cons_of_mem _ hc, hx, ?_⟩
      intro k hk
      apply sep
      rcases hk with ⟨l, hl, hkl⟩ | mem
      · exact .inl ⟨a, rfl, by have := order l hl a (by simp); omega⟩
      · rcases List.mem_cons.mp mem with rfl | later
        · exact .inl ⟨_, rfl, by omega⟩
        · exact .inr later

private theorem covers_of_separated {c : Region} {x k : Int}
    (hx : c.Contains x) (hs : Separated c k) : c.coversCut k := by
  obtain ⟨lo, hi⟩ := c
  cases lo <;> cases hi <;>
    simp_all [Region.Contains, Separated, Region.coversCut, Region.sample] <;> grind

theorem solve_complete {p x q m} (hs : Stable p x m) (hq : q.matches m = true) :
    ∃ c n, (c,n) ∈ solve p q ∧ c.Contains x ∧ SameModel n m := by
  let raw := ((p.flatMap Rule.guards).map Bound.cut).eraseDups
  have sorted : raw.mergeSort.Pairwise (· ≤ ·) := by
    simpa using List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
      (by simp; omega) (by simp; omega) raw
  obtain ⟨c, hc, hx, sep⟩ := cells_cover raw.mergeSort sorted none x (by simp) (by simp)
  have hu : uniform p c := by
    apply List.all_eq_true.mpr
    intro r hr
    apply List.all_eq_true.mpr
    intro g hg
    have hmem : g.cut ∈ raw.mergeSort := by
      apply List.mem_mergeSort.mpr
      apply List.mem_eraseDups.mpr
      exact List.mem_map.mpr ⟨g, List.mem_flatMap.mpr ⟨r, hr, hg⟩, rfl⟩
    have h := covers_of_separated hx (sep g.cut (.inr hmem))
    cases g <;> exact h
  obtain ⟨n, hn, eq⟩ := solveAt_complete ((Region.stable_iff_sample hu hx).mp hs) hq
  exact ⟨c, n, List.mem_flatMap.mpr ⟨c, List.mem_filter.mpr ⟨hc, hu⟩,
    List.mem_map.mpr ⟨n, hn, rfl⟩⟩, hx, eq⟩

end Casp
