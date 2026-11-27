import Casp.Search
import Std.Data.HashMap

namespace Casp.FO

inductive Term where
  | var (name : String)
  | const (value : String)
  deriving BEq, Repr, Inhabited

structure Atom where
  pred : String
  args : List Term := []
  deriving BEq, Repr, Inhabited

structure Body where
  pos : List Atom := []
  neg : List Atom := []
  deriving BEq, Repr, Inhabited

structure Rule extends Body where
  head : Option Atom := none
  guards : List Bound := []
  deriving Repr, Inhabited

abbrev Program := List Rule
abbrev Subst := List (String × String)

private def terms (as : List Atom) := as.flatMap Atom.args
def vars (as : List Atom) := ((terms as).filterMap fun
  | .var n => some n | _ => none).eraseDups

def Body.vars (q : Body) := FO.vars (q.pos ++ q.neg)
def Rule.atoms (r : Rule) := r.head.toList ++ r.pos ++ r.neg

/-- Variables range over the declared values and all constants appearing in the program. -/
def activeDomain (declared : List String) (p : Program) :=
  (declared ++ ((terms (p.flatMap Rule.atoms)).filterMap fun
    | .const c => some c | _ => none)).eraseDups

private def lookup (s : Subst) (v : String) := s.lookup v

def extend (domain names : List String) (seed : Subst) : List Subst :=
  names.foldl (init := [seed]) fun envs v => envs.flatMap fun env =>
    if (lookup env v).isSome then [env] else domain.map fun c => (v,c) :: env

def bindings (declared : List String) (p : Program) (q : Body) :=
  extend (activeDomain declared p) q.vars []

private def value (s : Subst) : Term → Option String
  | .const c => some c
  | .var v => lookup s v

structure Ground where
  pred : String
  args : List String
  deriving BEq, Hashable, Inhabited

private def inst (a : Atom) (s : Subst) : Option Ground := do
  return ⟨a.pred, ← a.args.mapM (value s)⟩

/-- Self-delimiting fields preserve arity and arbitrary Unicode names. -/
def groundKey (pred : String) (args : List String) : String :=
  String.join ((pred :: args).map fun s => toString s.length ++ ":" ++ s)

private def key (g : Ground) := groundKey g.pred g.args

def instantiateQuery (q : Body) (s : Subst) : Option Casp.Query := do
  let atom := fun a => (inst a s).map key
  return ⟨← q.pos.mapM atom, ← q.neg.mapM atom⟩

def instantiateRule (r : Rule) (s : Subst) : Option Casp.Rule := do
  let q ← instantiateQuery r.toBody s
  let h ← r.head.mapM fun a => (inst a s).map key
  return ⟨h, q.pos, q.neg, r.guards⟩

def ground (declared : List String) (p : Program) : Casp.Program :=
  let domain := activeDomain declared p
  p.flatMap fun r => (extend domain (vars r.atoms) []).filterMap (instantiateRule r)

def Answers (declared : List String) (p : Program) (x : Int) (q : Body) (s : Subst) : Prop :=
  s ∈ bindings declared p q ∧ ∃ gq, instantiateQuery q s = some gq ∧ Possible (ground declared p) x gq

theorem answers_of_possible {d p x q s gq} (valid : s ∈ bindings d p q)
    (instQ : instantiateQuery q s = some gq) (h : Possible (ground d p) x gq) :
    Answers d p x q s := ⟨valid, gq, instQ, h⟩

/-- Exhaustive binding oracle. Compiles the program once, independently of indexed search. -/
def reference (declared : List String) (p : Program) (x : Int) (q : Body) : List Subst :=
  let gp := ground declared p
  (bindings declared p q).filter fun s => (instantiateQuery q s).any fun gq =>
    !(solveAt gp x gq).isEmpty

theorem reference_iff {d p x q s} : s ∈ reference d p x q ↔ Answers d p x q s := by
  simp only [reference, List.mem_filter, Answers]
  cases he : instantiateQuery q s <;> simp [possible_iff_result]

/-- Certified replay returns a witness for the source query under this substitution. -/
def replay (declared : List String) (p : Program) (x : Int) (q : Body) (s : Subst) :
    Option Model := do
  if s ∈ bindings declared p q then
    let gq ← instantiateQuery q s
    firstAt (ground declared p) x gq
  else none

theorem replay_sound {d p x q s m} (h : replay d p x q s = some m) :
    Answers d p x q s := by
  unfold replay at h
  by_cases hb : s ∈ bindings d p q
  · cases he : instantiateQuery q s with
    | none => simp [hb, he] at h
    | some gq =>
      simp [hb, he] at h
      exact ⟨hb, gq, he, m, firstAt_sound h⟩
  · simp [hb] at h

private abbrev Sig := String × Nat
private def Atom.sig (a : Atom) : Sig := (a.pred, a.args.length)
private def Ground.sig (g : Ground) : Sig := (g.pred, g.args.length)

private structure Index where
  domain : List String
  heads : Std.HashMap Sig (List Rule) := {}
  intensional : Std.HashSet Sig := {}
  facts : Std.HashMap Sig (List Ground) := {}
  columns : Std.HashMap (Sig × Nat × String) (List Ground) := {}
  checks : List Rule := []

private def insertFact (idx : Index) (g : Ground) : Index := Id.run do
  let mut columns := idx.columns
  for (c,i) in g.args.zipIdx do
    columns := columns.alter (g.sig,i,c) fun old => some (g :: old.getD [])
  return {idx with columns, facts := idx.facts.alter g.sig fun old => some (g :: old.getD [])}

private def buildIndex (domain : List String) (p : Program) (x : Int) : Index := Id.run do
  let mut idx : Index := { domain }
  for r in p do
    if !r.guards.all (Bound.test x) then continue
    if r.head.isNone || !r.neg.isEmpty then idx := {idx with checks := r :: idx.checks}
    let some h := r.head | continue
    if r.pos.isEmpty && r.neg.isEmpty then
      if let some fact := inst h [] then
        idx := insertFact idx fact
        continue
    idx := {idx with
      intensional := idx.intensional.insert h.sig
      heads := idx.heads.alter h.sig fun old => some (r :: old.getD [])}
  return idx

private def unify (a : Atom) (g : Ground) (s : Subst) : Option Subst := do
  guard (a.sig == g.sig)
  let mut env := s
  for (t,c) in a.args.zip g.args do
    if let some v := value env t then guard (v == c)
    else if let .var n := t then env := (n,c) :: env
  return env

private def matchFacts (idx : Index) (a : Atom) (s : Subst) : List Subst := Id.run do
  for (t,i) in a.args.zipIdx do
    if let some c := value s t then
      return (idx.columns.getD (a.sig,i,c) []).filterMap fun f => unify a f s
  return (idx.facts.getD a.sig []).filterMap fun f => unify a f s

private def rejectKnownNegative (idx : Index) (neg : List Atom) (s : Subst) : Bool :=
  neg.any fun a => !idx.intensional.contains a.sig && !(matchFacts idx a s).isEmpty

private def instances (idx : Index) (r : Rule) (seed : Subst) (filterNeg : Bool) : List Subst :=
  -- Join positive extensional literals before enumerating remaining local variables.
  let edb := r.pos.filter fun a => !idx.intensional.contains a.sig
  let envs := edb.foldl (init := [seed]) fun ss a => ss.flatMap (matchFacts idx a)
  let bound := envs.flatMap (extend idx.domain (vars r.atoms))
  if filterNeg && !r.neg.isEmpty then bound.filter (!rejectKnownNegative idx r.neg ·) else bound

structure Stats where
  visitedAtoms : Nat := 0
  emittedRules : Nat := 0
  deriving Repr

private structure Slice where
  demand : List Ground := []
  seen : Std.HashSet Ground := {}
  rules : Casp.Program := []

private def emit (slice : Slice) (r : Rule) (env : Subst) : Slice := Id.run do
  let some gr := instantiateRule r env | return slice
  let deps := (r.pos ++ r.neg).filterMap fun a => inst a env
  return {slice with rules := gr :: slice.rules, demand := deps ++ slice.demand}

/-- The queue contains only ground atoms from the finite signature and domain.
Every expanded atom is marked before its rules enqueue more demands. -/
private partial def close (idx : Index) (filterNeg : Bool) (s : Slice) : Slice := Id.run do
  let g :: todo := s.demand | return s
  if s.seen.contains g then return close idx filterNeg {s with demand := todo}
  let mut next := {s with demand := todo, seen := s.seen.insert g}
  let pattern : Atom := ⟨g.pred, g.args.map Term.const⟩
  if !(matchFacts idx pattern []).isEmpty then
    next := {next with rules := {head := some (key g)} :: next.rules}
  for r in idx.heads.getD g.sig [] do
    if let some seed := r.head.bind (unify · g []) then
      if seed.all (fun (_, c) => idx.domain.contains c) then
        for env in instances idx r seed filterNeg do next := emit next r env
  return close idx filterNeg next

structure Prepared where
  program : Casp.Program
  query : Body
  candidates : List Subst
  parameter : Int
  stats : Stats

/-- Build a demand slice for all query bindings together. Denials and rules with
negative bodies seed global checks; omitted positive definitions can be extended
by their least closure. The reference and replay paths ground independently. -/
def prepareWithDependencies (declared : List String) (p : Program) (x : Int) (q : Body)
    (required : List Ground) (filterNeg := false) : Prepared × Std.HashSet Ground := Id.run do
  let idx := buildIndex (activeDomain declared p) p x
  let edb := q.pos.filter fun a => !idx.intensional.contains a.sig
  let seeds := edb.foldl (init := [[]]) fun ss a => ss.flatMap (matchFacts idx a)
  -- Canonicalize binding order to match the public source-level representation.
  let vars := q.vars
  let envs := (seeds.flatMap (extend idx.domain vars)).filterMap fun s =>
    vars.reverse.mapM fun v => (lookup s v).map (v, ·)
  let envs := envs.eraseDups
  let envs := if filterNeg && !q.neg.isEmpty then envs.filter (!rejectKnownNegative idx q.neg ·) else envs
  let mut slice : Slice := {demand := required}
  for r in idx.checks do
    for env in instances idx r [] filterNeg do
      if let some g := r.head.bind (inst · env) then
        slice := {slice with demand := g :: slice.demand}
      else slice := emit slice r env
  for env in envs do
    slice := {slice with demand := ((q.pos ++ q.neg).filterMap (inst · env)) ++ slice.demand}
  slice := close idx filterNeg slice
  return (⟨slice.rules, q, envs, x, ⟨slice.seen.size, slice.rules.length⟩⟩, slice.seen)

def prepare (d : List String) (p : Program) (x : Int) (q : Body) : Prepared :=
  (prepareWithDependencies d p x q []).1

def Prepared.accepts (plan : Prepared) (s : Subst) : Bool :=
  (instantiateQuery plan.query s).any fun gq => (firstAt plan.program plan.parameter gq).isSome

def search (d : List String) (p : Program) (x : Int) (q : Body) : List Subst × Stats :=
  let plan := prepare d p x q
  (plan.candidates.filter plan.accepts, plan.stats)

/-- Replay indexed substitutions against the full independent grounding. -/
def certified (d : List String) (p : Program) (x : Int) (q : Body) : List Subst :=
  (search d p x q).1.filter fun s => (replay d p x q s).isSome

theorem certified_sound {d p x q s} (h : s ∈ certified d p x q) : Answers d p x q s := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (List.mem_filter.mp h).2
  exact replay_sound hm

/-- In a witness for not h, every finite instantiation of every rule defining h
has a blocker. The body-local substitution is universally quantified. -/
theorem negative_coverage {d p x q s m} (h : replay d p x q s = some m)
    {gq} (instQ : instantiateQuery q s = some gq) {atom} (neg : atom ∈ gq.neg)
    {r : Rule} (hr : r ∈ p) {env} (he : env ∈ extend (activeDomain d p) (vars r.atoms) [])
    {gr} (instR : instantiateRule r env = some gr) (head : gr.head = some atom) :
    ¬ (enabled x m gr = true ∧ ∀ a ∈ gr.pos, a ∈ m) := by
  unfold replay at h
  split at h
  · simp [instQ] at h
    obtain ⟨stable, satisfied⟩ := firstAt_sound h
    have grounded : gr ∈ ground d p :=
      List.mem_flatMap.mpr ⟨r, hr, List.mem_filterMap.mpr ⟨env, he, instR⟩⟩
    rintro ⟨on, pos⟩
    have member := stable.1 gr grounded on pos
    simp only [head] at member
    simp only [Query.matches, Bool.and_eq_true, List.all_eq_true] at satisfied
    simpa [member] using satisfied.2 atom neg
  · contradiction

/-- A unary residual denotes exactly these permitted domain values for the
existential (brave) query. Different values may be witnessed by different models. -/
structure Residual where
  name : String
  domain : List String
  excluded : List String
  deriving Repr, BEq

def complement (d : List String) (p : Program) (x : Int) (q : Body) : Option Residual := do
  let [v] := q.vars | none
  let domain := activeDomain d p
  let values := (search d p x q).1.filterMap (lookup · v)
  return ⟨v, domain, domain.filter (!values.contains ·)⟩

/-- Exact finite-domain residual; use this path when excluded values need certification too. -/
def exactResidual (d : List String) (p : Program) (x : Int) (q : Body) : Option Residual := do
  let [v] := q.vars | none
  let domain := activeDomain d p
  let answers := reference d p x q
  return ⟨v, domain, domain.filter (fun c => !answers.contains [(v,c)])⟩

theorem exactResidual_iff {d p x q result v c} (one : q.vars = [v])
    (h : exactResidual d p x q = some result) (hc : c ∈ activeDomain d p) :
    c ∉ result.excluded ↔ Answers d p x q [(v,c)] := by
  simp [exactResidual, one] at h
  subst result
  simp [hc, reference_iff]

end Casp.FO
