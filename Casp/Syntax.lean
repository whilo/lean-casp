import Casp.FirstOrder
import Lean

namespace Casp.FO
open Lean

declare_syntax_cat foArg
syntax ident : foArg
syntax str : foArg
declare_syntax_cat foAtom
syntax ident : foAtom
syntax ident "(" foArg,+ ")" : foAtom
declare_syntax_cat foLit
syntax foAtom : foLit
syntax "not " foAtom : foLit
declare_syntax_cat foRule
syntax foAtom : foRule
syntax foAtom " :- " foLit,+ : foRule
syntax ":- " foLit,+ : foRule
syntax "fo!{" sepBy(foRule, ";") "}" : term
syntax "ask!{" foLit,* "}" : term

private def argTerm (stx : TSyntax `foArg) : MacroM Lean.Term := do
  match stx with
  | `(foArg| $v:ident) =>
    let name := v.getId.toString
    if name == "_" then Macro.throwErrorAt v "use a named variable"
    let n := quote name
    if name.toList.head!.isUpper then `(Casp.FO.Term.var $n) else `(Casp.FO.Term.const $n)
  | `(foArg| $v:str) => `(Casp.FO.Term.const $v)
  | _ => Macro.throwUnsupported

private def atomTerm (stx : TSyntax `foAtom) : MacroM Lean.Term := do
  match stx with
  | `(foAtom| $p:ident) => `(Casp.FO.Atom.mk $(quote p.getId.toString) [])
  | `(foAtom| $p:ident($args,*)) =>
    let ts ← args.getElems.mapM argTerm
    `(Casp.FO.Atom.mk $(quote p.getId.toString) [$ts,*])
  | _ => Macro.throwUnsupported

private def bodyTerm (ls : Array (TSyntax `foLit)) : MacroM Lean.Term := do
  let mut pos := #[]
  let mut neg := #[]
  for l in ls do
    match l with
    | `(foLit| not $a:foAtom) => neg := neg.push (← atomTerm a)
    | `(foLit| $a:foAtom) => pos := pos.push (← atomTerm a)
    | _ => Macro.throwUnsupported
  `(Casp.FO.Body.mk [$pos,*] [$neg,*])

private def ruleTerm (stx : TSyntax `foRule) : MacroM Lean.Term := do
  match stx with
  | `(foRule| $a:foAtom) => `(Casp.FO.Rule.mk {} (some $(← atomTerm a)) [])
  | `(foRule| $a:foAtom :- $ls,*) =>
    `(Casp.FO.Rule.mk $(← bodyTerm ls.getElems) (some $(← atomTerm a)) [])
  | `(foRule| :- $ls,*) => `(Casp.FO.Rule.mk $(← bodyTerm ls.getElems) none [])
  | _ => Macro.throwUnsupported

macro_rules
  | `(fo!{ $rs;* }) => do
    let rules ← rs.getElems.mapM ruleTerm
    `(([$rules,*] : Casp.FO.Program))
  | `(ask!{ $ls,* }) => bodyTerm ls.getElems

end Casp.FO
