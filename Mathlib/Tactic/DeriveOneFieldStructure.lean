/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util
public import Mathlib.Logic.Equiv.Defs

/-!
# Deriving handlers for one-field structures

A *one-field structure* is a structure with a single field, such as
```lean
structure Wrapper (α : Type*) where
  inner : α
```
It is the structural counterpart of a type synonym `def Wrapper (α : Type*) := α`: the two types
are in canonical bijection, but a one-field structure is not definitionally equal to the type of
its field, so type class inference cannot leak instances from one to the other.

Lean derives instances for a type synonym by *delta deriving*: it unfolds the definition and
reuses the instance found for the unfolded type. That strategy is unavailable for a one-field
structure, so every class needs a deriving handler that *transfers* the instance along the
canonical equivalence.

This file provides the infrastructure shared by all such handlers. A handler is written as

```lean
initialize
  registerDerivingHandler ``C <| mkOneFieldStructureHandler ``C fun info => do
    return (← `(C $info.typeStx), ← `(transferC $info.equivStx))
```

where `transferC` is the transfer construction for `C`. See
`Mathlib/Topology/Algebra/Module/DeriveOneFieldStructure.lean` for the handlers used by
`TangentSpace`.

## Class arguments

A deriving handler only receives the *name* of the class, never the arguments written in the
`deriving` clause: `deriving Module R` and `deriving Module` invoke the same handler with the same
information, and the former is in fact rejected by `Lean.Elab.DerivingClassView.getClassName`.
Handlers for classes with extra arguments (a scalar ring, say) should therefore quantify over
those arguments themselves, producing an instance such as
`∀ {R} [Semiring R] [Module R α], Module R (Wrapper α)`, and the `deriving` clause should mention
the class without arguments.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term Meta Command

/-- The data of a one-field structure `S`, made available to a deriving handler while the
parameters of `S` are in scope as free variables.

The `Stx` fields are syntax stand-ins for the corresponding expressions; they are only valid
inside the `TermElabM` computation that produced them. -/
structure Info where
  /-- The name of the structure. -/
  declName : Name
  /-- The parameters of the structure, as free variables. -/
  params : Array Expr
  /-- The structure applied to `params`. -/
  type : Expr
  /-- The type of the unique field. -/
  fieldType : Expr
  /-- Syntax for `type`. -/
  typeStx : Term
  /-- Syntax for `fieldType`. -/
  fieldTypeStx : Term
  /-- Syntax for the projection `type → fieldType`. -/
  projStx : Term
  /-- Syntax for the constructor `fieldType → type`. -/
  mkStx : Term
  /-- Syntax for the canonical equivalence `type ≃ fieldType`. -/
  equivStx : Term

/-- Run `k` on the data of the one-field structure `declName`, with the parameters of `declName`
in scope. Returns `none` if `declName` is not a structure with exactly one field. -/
def withOneFieldStructure {α : Type} (declName : Name) (k : Info → TermElabM α) :
    TermElabM (Option α) := do
  let env ← getEnv
  unless isStructure env declName do return none
  let indVal ← getConstInfoInduct declName
  let [ctorName] := indVal.ctors | return none
  let fields := getStructureFields env declName
  unless fields.size == 1 do return none
  -- `getStructureFields` flattens parent structures; make sure there is a genuine single field.
  unless (getStructureParentInfo env declName).isEmpty do return none
  let lvls := indVal.levelParams.map mkLevelParam
  -- Universe names introduced by a handler (through `Type _`, say) must not clash with the
  -- universe parameters of the structure itself.
  withLevelNames indVal.levelParams do
  forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    let ctorInfo ← getConstInfoCtor ctorName
    let .forallE _ fieldType _ _ ← whnf (← instantiateForall ctorInfo.type params) | return none
    let type := mkAppN (mkConst declName lvls) params
    let proj := mkAppN (mkConst (declName ++ fields[0]!) lvls) params
    let mk := mkAppN (mkConst ctorName lvls) params
    let typeStx ← exprToSyntax type
    let fieldTypeStx ← exprToSyntax fieldType
    let projStx ← exprToSyntax proj
    let mkStx ← exprToSyntax mk
    -- Both round trips hold by `rfl` thanks to definitional eta for structures.
    let equivStx ← `(Equiv.mk $projStx $mkStx (fun _ => rfl) (fun _ => rfl))
    some <$> k
      { declName, params, type, fieldType, typeStx, fieldTypeStx, projStx, mkStx, equivStx }

/-- Turn the first `n` binders of `e` into implicit ones, leaving instance binders alone.
The parameters of a structure are explicit more often than not, but the instance derived for it
must determine them by unification. -/
private partial def implicitizeBinders (n : Nat) (e : Expr) : Expr :=
  match n, e with
  | 0, e => e
  | n + 1, .forallE nm t b bi =>
    .forallE nm t (implicitizeBinders n b) (if bi.isInstImplicit then bi else .implicit)
  | n + 1, .lam nm t b bi =>
    .lam nm t (implicitizeBinders n b) (if bi.isInstImplicit then bi else .implicit)
  | _, e => e

/-- Build a deriving handler for `className` out of `mkInst`, which is given the data of a
one-field structure and returns the type and the value of the instance to declare.

The resulting instance is generalized over the parameters of the structure; `mkInst` may
quantify over further variables by writing binders into the type and value it returns. -/
def mkOneFieldStructureHandler (className : Name) (mkInst : Info → TermElabM (Term × Term)) :
    DerivingHandler := fun declNames => do
  let #[declName] := declNames | return false
  let some (instName, type, value, levelParams, isProp) ← liftTermElabM <|
      withOneFieldStructure declName fun info => do
    let (typeStx, valStx) ← mkInst info
    let type ← elabType typeStx
    let value ← elabTermEnsuringType valStx type
    synthesizeSyntheticMVarsNoPostponing
    let n := info.params.size
    let type := implicitizeBinders n (← mkForallFVars info.params (← instantiateMVars type))
    let value := implicitizeBinders n (← mkLambdaFVars info.params (← instantiateMVars value))
    let type ← levelMVarToParam type
    let value ← levelMVarToParam value
    let levelParams := (collectLevelParams (collectLevelParams {} type) value).params
    let instName ← NameGen.mkBaseNameWithSuffix "inst" type
    let instName ← liftMacroM <| mkUnusedBaseName ((← getCurrNamespace) ++ instName)
    return (instName, type, value, levelParams.toList, ← isProp type)
    | return false
  liftTermElabM do
    if isProp then
      addDecl <| .thmDecl { name := instName, levelParams, type, value }
      addInstance instName .global (eval_prio default)
    else
      let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
      addAndCompile <| .defnDecl
        { name := instName, levelParams, type, value, hints, safety := .safe }
      registerInstance instName .global (eval_prio default)
    addDeclarationRangesFromSyntax instName (← getRef)
    trace[Elab.Deriving.oneFieldStructure] "derived {className} instance {instName} : {type}"
  return true

initialize registerTraceClass `Elab.Deriving.oneFieldStructure

end Mathlib.Deriving.OneFieldStructure
