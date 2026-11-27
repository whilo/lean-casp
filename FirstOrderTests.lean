import Casp

open Casp.FO
namespace FirstOrderTests

def agrees (d : List String) (p : Program) (q : Body) (x := (0 : Int)) : Bool :=
  let ref := reference d p x q
  let ans := (search d p x q).1
  ref.length == ans.length && ref.all ans.contains && ans.all fun s => (replay d p x q s).isSome

private def xy := ["a","b"]
private def projection (p : Program) (q : Body) :=
  ((search xy p 0 q).1.filterMap (·.lookup "X")).mergeSort

private def filtered := fo!{ q(a); q(b); r(b); p(X) :- q(X), not r(X) }
#guard projection filtered ask!{p(X)} == ["a"]
#guard agrees xy filtered ask!{p(X)}
#guard agrees xy filtered ask!{not p(X)}
example : Answers ["a","b"] filtered 0 ask!{p(X)} [("X","a")] := by
  apply reference_iff.mp
  decide +kernel

private def choice := fo!{ dom(a); dom(b); p(X) :- dom(X), not q(X); q(X) :- dom(X), not p(X) }
#guard projection choice ask!{p(X)} == xy
#guard projection choice ask!{p(X), q(X)} == []
#guard (search xy choice 0 ask!{p(a), q(b)}).1 == [[]]
private def denied := choice ++ fo!{ :- p(a) }
#guard projection denied ask!{p(X)} == ["b"]
#guard agrees xy denied ask!{not q(X), p(X)}

-- forall_over_facts in test_forall.pl; finite people projection excludes ann.
private def likes := fo!{food(cake); food(rice); eats(ann,cake); likes(X) :- food(F), eats(X,F)}
#guard agrees ["ann","bob"] likes ask!{not likes(X)}
#guard (complement ["ann","bob"] likes 0 ask!{not likes(X)}).map (·.excluded) == some ["ann"]

-- One working definition defeats negation even if all the other bodies fail.
private def blocked := fo!{ edge(a,b); edge(a,c); edge(b,b); faulty(c);
  link(c,b); stopped(b); blocked(X) :- edge(X,Y), faulty(Y);
  blocked(X) :- link(X,Z), stopped(Z) }
#guard (complement ["a","b","c","d"] blocked 0 ask!{not blocked(X)}).map (·.excluded) ==
  some ["a","c"]
#guard agrees ["d"] blocked ask!{not blocked(X)}
#guard (complement xy blocked 0 ask!{not blocked(X), not blocked(Y)}).isNone

-- Every local witness must fail in the SAME model.
private def competing := fo!{ node(a); node(b); hit(a) :- not hit(b);
  hit(b) :- not hit(a); blocked :- node(Y), hit(Y) }
#guard (search xy competing 0 ask!{not blocked}).1.isEmpty
#guard agrees xy competing ask!{not blocked}

private def path := fo!{ edge(a,b); edge(b,c); edge(c,b);
  reach(X,Y) :- edge(X,Y);
  reach(X,Y) :- edge(X,Z), reach(Z,Y) }
#guard (search [] path 0 ask!{reach(a,Y)}).1.length == 2
#guard agrees [] path ask!{reach(a,Y)}
#guard agrees [] path ask!{not reach(X,X)}
#guard agrees [] path ask!{reach(X,Y), not reach(Y,X)}

-- Facts and rules for the same predicate, overloaded arity, repeated variables,
-- explicit uppercase constants, empty domains, and disconnected global checks.
private def mixed := fo!{ rel(a,b); rel(X,X); rel; nt(X) :- rel(X,X), not bad(X); bad(b) }
#guard agrees xy mixed ask!{rel(X,Y), nt(X)}
#guard (search [] fo!{p("A"); p("a:b"); p("雪"); p(""); p(a,b)} 0 ask!{p(X)}).1.length == 4
#guard agrees [] fo!{p("a:b"); p(a,b); p("雪")} ask!{p(X)}
#guard (search [] fo!{p(X)} 0 ask!{p(X)}).1.isEmpty
#guard (search [] fo!{} 0 ask!{}).1 == [[]]
#guard (search ["a"] fo!{} 0 ask!{not absent(X)}).1 == [[("X","a")]]
#guard (search xy (filtered ++ fo!{odd(X) :- q(X), not odd(X)}) 0 ask!{p(a)}).1.isEmpty
#guard (search xy (filtered ++ fo!{:- r(b)}) 0 ask!{p(a)}).1.isEmpty
#guard (search [] fo!{p(X); :- p(X)} 0 ask!{}).1 == [[]]
#guard (search xy fo!{p(X); :- p(X)} 0 ask!{}).1.isEmpty

-- Cross each of these rule forms with every other form, including recursion
-- through defaults, an existential local, unbound heads, and denials.
private def rules := fo!{p(X) :- q(X); p(X) :- not q(X); q(X) :- not p(X);
  q(X) :- q(X); p(X) :- q(Y); :- p(X), q(X); p(a); q(b); p(X)}
private def queries := [ask!{}, ask!{p(X)}, ask!{not p(X)}, ask!{p(X), q(X)},
  ask!{p(a), q(b)}, ask!{not p(a), not q(b)}]
#guard rules.all fun a => rules.all fun b => queries.all (agrees xy [a,b] ·)

-- Inactive guards must also disappear from global consistency checks.
private def guarded := filtered ++ [(fo!{:- q(a)}).head! |> fun r => {r with guards := [.ge 4]}]
#guard agrees xy guarded ask!{p(X)} 3 && agrees xy guarded ask!{p(X)} 4
#guard projection guarded ask!{p(X)} == ["a"]

#guard agrees ["a"] fo!{p(X)} ask!{p(b)}
#guard (search ["a"] fo!{p(X)} 0 ask!{p(b)}).1.isEmpty
#guard (search ["a"] fo!{p(X)} 0 ask!{not p(b)}).1 == [[]]
#guard exactResidual ["d"] blocked 0 ask!{not blocked(X)} ==
  complement ["d"] blocked 0 ask!{not blocked(X)}
example : Answers xy filtered 0 ask!{not p(X)} [("X","b")] := by casp

private def twoLocals := fo!{edge(a,b); edge(b,c); bad(c);
  blocked(X) :- edge(X,Y), edge(Y,Z), bad(Z)}
#guard projection twoLocals ask!{blocked(X)} == ["a"]
#guard agrees xy twoLocals ask!{not blocked(X)}
#guard certified xy twoLocals 0 ask!{not blocked(X)} ==
  (search xy twoLocals 0 ask!{not blocked(X)}).1

-- Indexed queries restrict instantiations before the ground engine runs.
private def sliceExample := path ++ fo!{noise(i);noise(j);noise(k)}
#guard (prepare [] sliceExample 0 ask!{reach(a,Y)}).stats.emittedRules <
  (ground [] sliceExample).length
#guard agrees [] sliceExample ask!{reach(a,Y)}

-- Empty forall ranges, independent local scopes, missing facts, and free variables
-- visible only under default negation all exercise different binding modes.
#guard agrees [] fo!{p :- q(Y)} ask!{not p}
#guard agrees xy fo!{p(X) :- r(X,Y); p(X) :- s(Y,X); s(b,a)} ask!{not p(X)}
#guard agrees xy fo!{p(X) :- not q(Y); q(a)} ask!{not p(X)}
#guard agrees xy fo!{choice(a) :- not choice(b); choice(b) :- not choice(a)} ask!{not choice(X), not choice(Y)}
#guard (replay xy filtered 0 ask!{p(X)} [("X","nonmember")]).isNone

end FirstOrderTests
