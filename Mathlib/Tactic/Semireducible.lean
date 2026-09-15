/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.Init
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.Term
public meta import Lean.Meta.Closure
public meta import Lean.Meta.Tactic.Simp.SimpTheorems

/-!
# Semireducible terms

`semireducible% t` puts `t` in an auxiliary semireducible definition, capturing its local
variables. The result unfolds at default transparency, but remains hidden at instance and
implicit transparency. For example, an instance-reducible functor can expose its objects
while keeping `map := semireducible% fun f ↦ ...` hidden.

An unfolding theorem is registered with `simp`, but is not a `dsimp` theorem.
-/

public meta section

open Lean Meta Elab Term

namespace Mathlib.Tactic

/-- Register an unfolding theorem without marking it as reflexive for `dsimp`. -/
private def addSemireducibleSimpLemma (name : Name) : MetaM Unit := do
  let info ← getConstInfoDefn name
  let (type, value) ← forallTelescope info.type fun xs _ => do
    let lhs := mkAppN (mkConst name (info.levelParams.map mkLevelParam)) xs
    let rhs := (mkAppN info.value xs).headBeta
    let type ← mkEq lhs rhs
    -- The type hint also prevents the legacy theorem-body check from recognizing `rfl`.
    let value ← mkExpectedTypeHint (← mkEqRefl lhs) type
    return (← mkForallFVars xs type, ← mkLambdaFVars xs value)
  let lemmaName := name ++ `eq
  addDecl <| .thmDecl { name := lemmaName, levelParams := info.levelParams, type, value }
  addSimpTheorem simpExtension lemmaName true false .global 1000

/-- Put a term in an auxiliary semireducible definition. -/
syntax (name := semireduciblePercent) "semireducible% " term : term

@[term_elab semireduciblePercent] def elabSemireduciblePercent : TermElab := fun stx expected? => do
  let value ← elabTermAndSynthesize stx[1] expected?
  let name ← mkAuxDeclName `_semireducible
  let value ← mkAuxDefinitionFor name value (compile := false)
  addSemireducibleSimpLemma name
  setInlineAttribute name
  if (← read).declName?.any (isMarkedMeta (← getEnv)) then
    modifyEnv (markMeta · name)
  let logErrors := !(← read).isNoncomputableSection &&
    !(← read).declName?.any (Lean.isNoncomputable (← getEnv))
  compileDecls (logErrors := logErrors) #[name]
  return value

end Mathlib.Tactic
