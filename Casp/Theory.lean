import Casp.FirstOrder

namespace Casp.Theory
open FO

/-- A read-only unary theory predicate. Its interpretation is fixed per snapshot.
The arity-one symbol is reserved in the source passed to this declaration. -/
structure Predicate (σ : Type) where
  name : String
  holds : σ → String → Prop
  decision : ∀ snap a, Decidable (holds snap a)

def Predicate.test (t : Predicate σ) (snap : σ) (a : String) : Bool :=
  @decide (t.holds snap a) (t.decision snap a)

theorem Predicate.test_iff (t : Predicate σ) (snap : σ) (a : String) :
    t.test snap a = true ↔ t.holds snap a := by
  letI := t.decision snap a
  exact decide_eq_true_iff

private def virtualHead (name : String) : FO.Atom := ⟨name, [.var "arg"]⟩

private def keyOf (name a : String) : Casp.Atom :=
  FO.groundKey name [a]

private def valid (name : String) (p : FO.Program) :=
  !p.any fun r => r.head.any fun h => h.pred == name && h.args.length == 1

/-- Independent source semantics: install the whole truth table as ordinary facts. -/
def materialize (t : Predicate σ) (snap : σ) (d : List String) (p : FO.Program) :
    Except String FO.Program := do
  unless valid t.name p do throw s!"interpreted predicate {t.name}/1 also has a rule head"
  let facts := ((activeDomain d p).filter (t.test snap)).map fun a =>
    ({head := some ⟨t.name, [.const a]⟩} : FO.Rule)
  return p ++ facts

/-- An indexed slice contains at most one requested virtual fact per argument.
The keys are shared by positive and default-negated uses. -/
structure Template (symbol : String) where
  plan : FO.Prepared
  requests : List (Casp.Atom × String)
  domain : List String
  inDomain : ∀ r ∈ requests, r.2 ∈ domain

def template (name : String) (d : List String) (p : FO.Program) (x : Int) (q : FO.Body)
    (required : List FO.Ground := []) : Except String (Template name) := do
  unless valid name p do throw s!"interpreted predicate {name}/1 also has a rule head"
  let domain := activeDomain d p
  let (plan, seen) := FO.prepareWithDependencies d (p ++ [{head := some (virtualHead name)}]) x q required true
  if plan.candidates.isEmpty then return ⟨plan, [], domain, by simp⟩
  let available := Std.HashSet.ofList domain
  let requests := seen.toList.filterMap fun g =>
    match g.args with
    | [a] => if g.pred == name && available.contains a then some (keyOf name a, a) else none
    | _ => none
  return ⟨plan, requests, domain, by
    intro r hr
    obtain ⟨g, _, h⟩ := List.mem_filterMap.mp hr
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    simp_all [available]⟩

private def resolveFacts (plan : FO.Prepared) (dropFacts : List String) : FO.Prepared :=
  if dropFacts.isEmpty then plan else
    let dropped := Std.HashSet.ofList dropFacts
    {plan with program := plan.program.filter (fun r => !r.head.any dropped.contains)}

def Template.resolve (t : Template name) (test : String → Bool) : FO.Prepared :=
  resolveFacts t.plan ((t.requests.filter fun (_,a) => !test a).map Prod.fst)

/-- Snapshot-local demand evaluation, once per requested key. -/
def prepare (t : Predicate σ) (snap : σ) (d : List String) (p : FO.Program) (x : Int)
    (q : FO.Body) : Except String (FO.Prepared × Nat) := do
  let tmp ← template t.name d p x q
  return (tmp.resolve (t.test snap), tmp.requests.length)

/-- Eager strategy for the identical search plan. Materialize once per snapshot. -/
def Template.resolveEager (t : Template name) (test : String → Bool) : FO.Prepared :=
  let table := Std.HashSet.ofList (t.domain.filter test)
  t.resolve table.contains

/-- An eager table lookup over all available arguments agrees with demand
evaluation for any instantiated rule slice whose requests are in-domain. -/
theorem eager_eq_demand (t : Template name) (test : String → Bool) :
    t.resolveEager test = t.resolve test := by
  simp only [Template.resolveEager, Template.resolve]
  congr 2
  apply List.filter_congr
  intro r hr
  have h := t.inDomain r hr
  have eq : (Std.HashSet.ofList (t.domain.filter test)).contains r.2 = test r.2 := by
    apply Bool.eq_iff_iff.mpr
    simp [h]
  exact congrArg Bool.not eq

/-- Persistent across queries. Its type ties every entry to the same predicate
and immutable snapshot. Forking the cache is ordinary persistent data sharing. -/
structure Cache (t : Predicate σ) (snap : σ) where
  entries : Std.HashMap String Bool
  correct : ∀ a b, entries[a]? = some b → b = t.test snap a

def Cache.empty (t : Predicate σ) (snap : σ) : Cache t snap :=
  ⟨{}, by simp⟩

private def Cache.insert (c : Cache t snap) (a : String) (b : Bool)
    (h : b = t.test snap a) : Cache t snap :=
  ⟨c.entries.insert a b, by
    intro k v hv
    by_cases eq : a = k
    · subst k
      simpa [h] using (show v = b by simpa using hv.symm)
    · exact c.correct k v (by simpa [Std.HashMap.getElem?_insert, eq] using hv)⟩

private def fill (cache : Cache t snap) : List (Atom × String) → List Atom × Cache t snap × Nat
  | [] => ([],cache,0)
  | (key,a) :: rest => Id.run do
    let (value, next, miss) := match cache.entries[a]? with
      | some b => (b, cache, 0)
      | none =>
        let b := t.test snap a
        (b, cache.insert a b rfl, 1)
    let (disabled, out, count) := fill next rest
    return (if value then disabled else key :: disabled, out, miss + count)

private theorem fill_correct {σ : Type} {t : Predicate σ} {snap : σ} (cache : Cache t snap) (rs : List (Atom × String)) :
    (fill cache rs).1 = (rs.filter (fun (_,a) => !t.test snap a)).map Prod.fst := by
  induction rs generalizing cache with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨key,a⟩ := r
    cases h : cache.entries[a]? with
    | none =>
      simp [fill, h, List.filter_cons, ih]
      cases t.test snap a <;> simp
    | some b =>
      have hb := cache.correct a b h
      simp [fill, h, hb, List.filter_cons, ih]
      cases t.test snap a <;> simp

def Template.resolveCached {σ : Type} {theory : Predicate σ} {snap : σ} (t : Template theory.name) (cache : Cache theory snap) :
    FO.Prepared × Cache theory snap × Nat :=
  let result := fill cache t.requests
  (resolveFacts t.plan result.1, result.2)

theorem cached_eq_demand {σ : Type} {theory : Predicate σ} {snap : σ} (t : Template theory.name) (cache : Cache theory snap) :
    (t.resolveCached cache).1 = t.resolve (theory.test snap) := by
  simp [Template.resolveCached, Template.resolve, fill_correct]

def prepareCached (cache : Cache t snap) (d : List String) (p : FO.Program) (x : Int) (q : FO.Body) :
    Except String (FO.Prepared × Cache t snap × Nat) := do
  let plan ← template t.name d p x q
  return plan.resolveCached cache

def search (t : Predicate σ) (snap : σ) (d : List String) (p : FO.Program) (x : Int)
    (q : FO.Body) : Except String (List Subst) := do
  let (plan, _) ← prepare t snap d p x q
  return plan.candidates.filter plan.accepts

/-- A certificate concerns the independent, full source interpretation. -/
def Answers (t : Predicate σ) (snap : σ) (d : List String) (p : FO.Program) (x : Int)
    (q : FO.Body) (s : Subst) : Prop :=
  ∃ source, materialize t snap d p = .ok source ∧ FO.Answers d source x q s

theorem answers_of_replay {t : Predicate σ} {snap d p x q s m source}
    (src : materialize t snap d p = .ok source) (h : replay d source x q s = some m) :
    Answers t snap d p x q s := ⟨source, src, replay_sound h⟩

end Casp.Theory
