# The embedded rule and query language

After `import Casp`, a `fo!{…}` term has Lean type `Casp.FO.Program` (a list of rules), and an `ask!{…}` term has type `Casp.FO.Body`. Lean parses the clauses when it elaborates the file. Evaluation begins when you hand those values to a solver. This lets you build a library of reusable policies using ordinary Lean definitions. [Parser and macro definitions](../Casp/Syntax.lean)

| Inside the embedding | Meaning |
| --- | --- |
| `fo!{online; node(api); node("DB")}` | Three facts. A bare predicate is nullary. Quoted arguments are literal strings, including uppercase names. |
| `fo!{same(X) :- edge(X,X)}` | Both occurrences refer to the same rule-local variable. The next rule may reuse its name independently. |
| `fo!{blocked(S) :- needs(S,D), incident(D)}` | A witness for the body-local variable `D` suffices to derive the head. |
| `fo!{ready(S) :- service(S), not blocked(S)}` | Default negation. To support readiness, the chosen model must exclude `blocked(S)`. |
| `fo!{:- frozen, immediate}` | A denial. Its head is absent, and its body must never jointly hold in an accepted model. |
| `ask!{ready(S), not blocked(S)}` | Return substitutions for which both requirements hold in a single stable model. |
| `ask!{}` | Ask for existence of a stable model subject to the program's global checks. |

Use commas within bodies and argument lists and semicolons between clauses. Uppercase initial letters introduce named variables. Arguments can also be lowercase names or strings. The grammar represents predicates with different arities, including zero, and function-free terms. For the equivalent of an anonymous local, give it a fresh uppercase name for each independent occurrence. Arithmetic guards are available through the rule data type. [Integer guard example](../Examples/Windows.lean)

## Inspect or transform a query

This equality is proved by reflexivity. Lean's macro expansion alone turns the left side into the right side.

```lean
open Casp.FO

example : ask!{needs(S,"DB"), not blocked(S)} =
    Body.mk [⟨"needs", [.var "S", .const "DB"]⟩] [⟨"blocked", [.var "S"]⟩] := rfl
```

The body stores separate lists of positive and default-negated atoms. Their position on the page does not prescribe a Prolog call sequence. For example the planner can use an indexed fact to bind a variable before enumerating it. The kernel checks this equality in the [rollout example](../Examples/Rollout.lean).

## Distinguish three actions in a Lean file

* `def q := ask!{ready(S)}` constructs reusable query data.
* `#eval (search [] outage 0 q).1` executes the indexed evaluator and prints the list of substitutions. Here `[]` supplies no extra domain names and `0` supplies the integer guard parameter.
* `example : Answers [] outage 0 q [("S","cache")] := by casp` asks Lean to verify one substitution against the full source semantics. The existence of this witness allows other substitutions and other stable models.

The names inside the braces denote logic variables, constants and predicates. To parameterize a program by a Lean value, combine previously constructed rule lists, build data using the constructors, or register a fixed interpreted predicate for an immutable snapshot. The dispatch example demonstrates that third option. [Predicate example](../Examples/Dispatch.lean)
