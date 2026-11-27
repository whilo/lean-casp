import Casp

open Casp.FO

namespace Rollout

-- A deployment depends on its direct and indirect prerequisites.
-- The notation expands to ordinary Lean data. Quoting makes "DB" a constant.
example : ask!{needs(S,"DB"), not blocked(S)} =
    Body.mk [⟨"needs", [.var "S", .const "DB"]⟩] [⟨"blocked", [.var "S"]⟩] := rfl

def topology := fo!{
  service(api); service(worker); service(cache); service(db);
  needs(api,worker); needs(worker,db); needs(api,cache);
  prerequisite(S,D) :- needs(S,D);
  prerequisite(S,D) :- needs(S,M), prerequisite(M,D)
}

-- An incident can block a service directly or through any prerequisite.
def health := fo!{
  blocked(S) :- incident(S);
  blocked(S) :- prerequisite(S,D), incident(D);
  ready(S) :- service(S), not blocked(S)
}

-- Choose one rollout mode for the API when it is ready.
def modes := fo!{
  canary :- ready(api), not immediate;
  immediate :- ready(api), not canary
}

def normal := topology ++ health ++ modes
def outage := normal ++ fo!{incident(db)}
def maintenance := normal ++ fo!{changeFreeze; :- changeFreeze, immediate}

-- Sort for display; query answers have no prescribed enumeration order here.
def names (p : Program) (q : Body) :=
  ((search [] p 0 q).1.filterMap (·.lookup "S")).mergeSort

#eval names normal ask!{prerequisite(api,S)}
#eval names normal ask!{ready(S)}
#eval names outage ask!{ready(S)}

#guard names normal ask!{prerequisite(api,S)} == ["cache","db","worker"]
#guard names normal ask!{ready(S)} == ["api","cache","db","worker"]
#guard names outage ask!{ready(S)} == ["cache"]

def possible (p : Program) (q : Body) := !(search [] p 0 q).1.isEmpty

#eval [possible normal ask!{canary}, possible normal ask!{immediate},
       possible normal ask!{canary, immediate}]
#eval [possible maintenance ask!{canary}, possible maintenance ask!{immediate}]
#guard possible normal ask!{canary} && possible normal ask!{immediate}
#guard !possible normal ask!{canary, immediate}
#guard possible maintenance ask!{canary} && !possible maintenance ask!{immediate}
#guard !possible outage ask!{canary} && !possible outage ask!{immediate}

def readiness := ask!{ready(S)}
#eval ((prepare [] outage 0 readiness).stats.emittedRules, (ground [] outage).length)

-- Replay the surviving substitution against the full source semantics.
example : Answers [] outage 0 readiness [("S","cache")] := by casp

end Rollout
