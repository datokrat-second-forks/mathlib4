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

This file provides the infrastructure shared by all such handlers. A handler is registered as

```lean
initialize
  registerOneFieldStructureHandler ``C fun info args => do
    return (← `(C $(info.typeStx)), ← `(transferC $(info.equivStx)))
```

where `transferC` is the transfer construction for `C`, and is invoked by writing `deriving C` on
the structure. All side conditions of the returned instance (the instance on the field type in the
first place, say) are synthesized from the structure's parameters at deriving time; deriving fails
if they are not available there. In particular the derived instance receives no hypotheses beyond
the structure's own parameters, mirroring the behaviour of delta deriving for type synonyms. See
`Mathlib/Topology/Algebra/Module/DeriveOneFieldStructure.lean` for the handlers used by
`TangentSpace`.

## Class arguments

Lean's built-in deriving mechanism for structures only passes the *name* of the class to a
deriving handler: `deriving Module 𝕜` is rejected before any handler runs (delta deriving for
type synonyms, by contrast, elaborates the deriving clause as a term, which is how
`deriving instance Module 𝕜 for MySynonym` has always worked for definitions).

To let one-field structures keep that spelling, this file intercepts the `deriving instance`
command by a macro whenever one of its classes carries arguments and reroutes it through the
`derive_one_field_instance` command below. The class arguments are elaborated *inside the
parameter telescope of the structure*, so they may refer to the structure's parameters by name:

```lean
structure TangentSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] ... where
  inner : E

deriving instance Module 𝕜 for TangentSpace
```

Definitions appearing as targets of such a rerouted command are still delta-derived as before.
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

/-- A builder for a one-field structure instance of some class. It is given the data of the
structure and the arguments written after the class in the deriving clause (`𝕜` in
`deriving instance Module 𝕜 for TangentSpace`; empty for a plain `deriving C`), and returns the
type and the value of the instance to declare. Both are elaborated inside the parameter telescope
of the structure, so argument syntax may refer to the structure's parameters by name. -/
@[expose] def OneFieldBuilder := Info → (args : Array Term) → TermElabM (Term × Term)

initialize oneFieldBuildersRef : IO.Ref (NameMap OneFieldBuilder) ← IO.mkRef {}

/-- Throw an error if a deriving clause passed arguments to a class whose one-field structure
handler does not accept any. -/
def ensureNoArgs (className : Name) (args : Array Term) : TermElabM Unit := do
  if h : 0 < args.size then
    throwErrorAt args[0] "`{.ofConstName className}` takes no arguments when derived for a \
      one-field structure"

/-- Derive an instance of `className` (applied to `args`) for the one-field structure `declName`,
using the registered builder. Returns `false` if `declName` is not a one-field structure or no
builder is registered for `className`. -/
def deriveOneFieldInstance (declName className : Name) (args : Array Term := #[]) :
    CommandElabM Bool := do
  let some builder := (← oneFieldBuildersRef.get).find? className | return false
  let some (instName, type, value, levelParams, isProp) ← liftTermElabM <|
      withOneFieldStructure declName fun info => do
    let (typeStx, valStx) ← builder info args
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
  -- Match the exposure of the structure itself (its projection, really): the derived instance
  -- must be unfoldable wherever the projection is, and no further. Without this, an instance
  -- derived by the standalone command (rather than an inline `deriving` clause, which runs
  -- inside the structure's own elaboration) would get a private body even in an
  -- `@[expose] public section`.
  let env ← getEnv
  let exposed := (getStructureFields env declName).any fun f =>
    env.hasExposedBody (declName ++ f)
  liftTermElabM <| withExporting (isExporting := exposed) do
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

/-- The deriving handler dispatching to `deriveOneFieldInstance` with no class arguments, for
plain `deriving C` clauses. -/
def mkDerivingHandler (className : Name) : DerivingHandler := fun declNames => do
  let #[declName] := declNames | return false
  deriveOneFieldInstance declName className

/-- Register `builder` as the one-field structure deriving handler for `className`, both for
plain `deriving C` clauses (via the built-in deriving mechanism) and for argument-carrying
`deriving instance C args for S` commands. Must be called in an `initialize` block. -/
def registerOneFieldStructureHandler (className : Name) (builder : OneFieldBuilder) : IO Unit := do
  oneFieldBuildersRef.modify (·.insert className builder)
  registerDerivingHandler className (mkDerivingHandler className)

/-- Derive instances of possibly argument-carrying classes for one-field structures, e.g.
`derive_one_field_instance Module 𝕜 for TangentSpace`. Class arguments are elaborated inside the
parameter telescope of the structure and may refer to its parameters by name.

This command is an implementation detail: `deriving instance Module 𝕜 for TangentSpace` expands
to it whenever a class carries arguments. Targets that are definitions (and classes that are not
constant applications) fall back to Lean's delta deriving, as they would in core. -/
syntax (name := deriveOneFieldInstanceCmd)
  "derive_one_field_instance " term,+ " for " term,+ : command

elab_rules : command
  | `(derive_one_field_instance $classes,* for $decls,*) => do
    for decl in decls.getElems do
      for cls in classes.getElems do
        withRef cls do
          -- Decompose the class into a head identifier and plain positional arguments.
          let (clsId?, args) :=
            if cls.raw.isIdent then
              (some cls.raw, #[])
            else if cls.raw.isOfKind ``Lean.Parser.Term.app
                && cls.raw[0].isIdent
                && cls.raw[1].getArgs.all fun a =>
                    !a.isOfKind ``Lean.Parser.Term.namedArgument
                    && !a.isOfKind ``Lean.Parser.Term.ellipsis then
              (some cls.raw[0], cls.raw[1].getArgs.map fun a => (⟨a⟩ : Term))
            else
              (none, #[])
          -- Delta deriving, exactly as core's `deriving instance` does for definitions.
          let deltaFallback : CommandElabM Unit := runTermElabM fun _ => withRef decl do
            let declExpr ← if decl.raw.isIdent then do
                let declName ← realizeGlobalConstNoOverload decl
                let info ← getConstInfo declName
                unless info.isDefinition do
                  throwError "cannot derive `{cls}` for `{.ofConstName declName}`: it is not a \
                    definition, and no one-field structure deriving handler is registered for \
                    this class"
                mkConstWithLevelParams declName
              else
                Term.elabTermAndSynthesize decl none
            Term.processDefDeriving ⟨cls, false, cls⟩ declExpr
          match clsId? with
          | none => deltaFallback
          | some clsId =>
            let className ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo clsId
            if decl.raw.isIdent then
              let declName ← liftCoreM <| realizeGlobalConstNoOverload decl
              match (← getEnv).find? declName with
              | some (.inductInfo _) =>
                if args.isEmpty then
                  applyDerivingHandlers className #[declName]
                else if (← oneFieldBuildersRef.get).contains className then
                  unless ← deriveOneFieldInstance declName className args do
                    throwError "failed to derive `{cls}` for `{.ofConstName declName}`: it is \
                      not a structure with exactly one field"
                else
                  throwError "class `{.ofConstName className}` has no one-field structure \
                    deriving handler, so it cannot be derived with arguments for an inductive type"
              | some (.defnInfo _) => deltaFallback
              | _ => throwError "cannot derive instances for `{.ofConstName declName}`"
            else
              deltaFallback

/-- Reroute `deriving instance ... for ...` through `derive_one_field_instance` whenever one of
the classes carries arguments; such commands are rejected by the built-in elaborator unless every
target is a definition. Everything else falls through to the built-in elaborator unchanged. -/
macro_rules
  | `(deriving $[noncomputable%$ncTk?]? instance $[$classes],* for $[$decls],*) => do
    if ncTk?.isSome then Macro.throwUnsupported
    -- `@[expose]` deriving classes keep the built-in behaviour.
    if classes.any fun c => c.raw[0].getNumArgs != 0 then Macro.throwUnsupported
    -- Defer to the built-in elaborator when every class is a plain identifier.
    if classes.all fun c => c.raw[1].isIdent then Macro.throwUnsupported
    let terms : Array Term := classes.map fun c => ⟨c.raw[1]⟩
    `(derive_one_field_instance $[$terms],* for $[$decls],*)

initialize registerTraceClass `Elab.Deriving.oneFieldStructure

end Mathlib.Deriving.OneFieldStructure
