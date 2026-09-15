/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public meta import Lean.Elab.Term
public meta import Lean.Meta.Sym.SymM

/-!
# Rebuilding componentwise categorical constructions

`obj% t` elaborates `t` at default transparency and rebuilds its structures against the expected
type. Component data must match at implicit transparency;
compatibility proofs retain the expected types and are checked at default transparency.
-/

public meta section

open Lean Meta Elab Term

namespace Mathlib.Tactic.CategoryTheory.Obj

/-- Expose component data while retaining categorical identity and composition notation. -/
private def exposeData (value : Expr) : MetaM Expr := withDefault do
  Sym.foldProjs (← whnfHeadPred value fun e =>
    pure (!e.isAppOf ``CategoryTheory.CategoryStruct.id &&
      !e.isAppOf ``CategoryTheory.CategoryStruct.comp))

/-- Rebuild structures and functions against the expected indices.
Proofs keep the expected type; data must match at implicit transparency. -/
partial def rebuild (value expected : Expr) (depth : Nat := 0) : MetaM Expr := do
  if depth > 64 then
    throwError "obj%: structure nesting exceeds 64 levels"
  let expected ← instantiateMVars expected
  if ← isProp expected then
    unless ← withDefault <| isDefEq (← inferType value) expected do
      throwError "obj%: incompatible proof types"
    return ← mkExpectedTypeHint value expected
  let exposed ← exposeData value
  if exposed.isAppOf ``CategoryTheory.CategoryStruct.id then
    if ← withImplicit <| isDefEq (← inferType exposed) expected then
      return exposed
  let target ← withImplicit <| whnf expected
  if target.isForall then
    forallTelescope target fun xs body => do
      let value ← rebuild (mkAppN value xs) body (depth + 1)
      mkLambdaFVars xs value
  else if target.getAppFn.isConst && isStructure (← getEnv) target.getAppFn.constName! then
    let name := target.getAppFn.constName!
    let info ← getConstInfoInduct name
    let ctorName := info.ctors.head!
    let ctorInfo ← getConstInfoCtor ctorName
    let ctor := mkAppN (mkConst ctorName target.getAppFn.constLevels!) target.getAppArgs
    let (args, _, result) ← forallMetaTelescope (← inferType ctor)
    unless ← withImplicit <| isDefEq result expected do
      throwError "obj%: cannot determine constructor parameters"
    for i in [:ctorInfo.numFields] do
      let arg := args[i]!
      let field ← rebuild (.proj name i value) (← inferType arg) (depth + 1)
      arg.mvarId!.assign field
    return ← instantiateMVars (mkAppN ctor args)
  else
    let value := exposed
    unless ← withImplicit <| isDefEq (← inferType value) expected do
      throwError "obj%: component data still has incompatible types\n\
        {← inferType value}\n{expected}"
    return value

syntax (name := objPercent) "obj% " term:arg : term

@[term_elab objPercent] def elabObjPercent : TermElab := fun stx expected? => do
  let some expected := expected? | throwError "obj% requires an expected type"
  let term : Term := ⟨stx[1]⟩
  let term ← if term.raw.isIdent && term.raw.getId == `Iso.refl then `($term _) else pure term
  let value ← withDefault <| elabTermEnsuringType term (some expected)
  synthesizeSyntheticMVarsNoPostponing
  rebuild (← instantiateMVars value) expected

end Mathlib.Tactic.CategoryTheory.Obj
