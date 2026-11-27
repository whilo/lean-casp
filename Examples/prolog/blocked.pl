person(ann).
person(bob).
blocked(ann).
allowed(X) :- person(X), not blocked(X).
