import Casp

open Casp.FO

namespace BlockedDemo

def policy := fo!{
  person(ann); person(bob); blocked(ann);
  allowed(X) :- person(X), not blocked(X)
}

#eval (search [] policy 0 ask!{allowed(X)}).1
#eval (search [] policy 0 ask!{not blocked(X)}).1
#eval (search ["cy"] policy 0 ask!{not blocked(X)}).1

#guard (search [] policy 0 ask!{allowed(X)}).1 == [[("X","bob")]]
#guard (search [] policy 0 ask!{not blocked(X)}).1 == [[("X","bob")]]

example : Answers [] policy 0 ask!{allowed(X)} [("X","bob")] := by casp

end BlockedDemo
