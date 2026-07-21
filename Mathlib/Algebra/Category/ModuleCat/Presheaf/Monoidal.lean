/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
-- imported only for the `InstanceTypesDemos` section at the end of this file
meta import Lean.PostprocessTraces

/-!
# The monoidal category structure on presheaves of modules

Given a presheaf of commutative rings `R : Cᵒᵖ ⥤ CommRingCat`, we construct
the monoidal category structure on the category of presheaves of modules
`PresheafOfModules (R ⋙ forget₂ _ _)`. The tensor product `M₁ ⊗ M₂` is defined
as the presheaf of modules which sends `X : Cᵒᵖ` to `M₁.obj X ⊗ M₂.obj X`.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

open CategoryTheory MonoidalCategory BraidedCategory Category Limits
open Lean.PostprocessTraces

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ _ RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

namespace Monoidal

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

/-
tl;dr:
It helps to mark `ModuleCat.RestrictScalars.obj'` and `ModuleCat.restrictScalars`
implicit-reducible. These ensure that the synthesis fallback's instances are defeq to the unified
instances at implicit transparency.

---
AI-produced investigation:

`tensorObjMap` (here) and `tensorObj_map_tmul` (below) both need
`backward.isDefEq.instanceTypes "none"` under the project default `"markOrSynth"` (set in
`lakefile.lean`; a bare `lake env lean` uses the toolchain register default `"mark"`, but both
modes reject these sites identically — the demos below pin `"markOrSynth"`).

Root cause — one ring, two spellings. For `M : PresheafOfModules (R ⋙ forget₂ _ _)`, the
carrier `M.obj X` is a `ModuleCat ↑((R ⋙ forget₂ CommRingCat RingCat).obj X)`: its base ring
is `R.obj X : CommRingCat` pushed through the composite forgetful functor into `RingCat`.
Every definition and statement in this file instead spells that ring directly as `↑(R.obj X)`
(the `CommRingCat` carrier). The two carriers `↑(R.obj X)` and
`↑((R ⋙ forget₂ CommRingCat RingCat).obj X)` are definitionally equal only by unfolding
`Functor.comp`, `HasForget₂.forget₂` and the `RingCat`/`CommRingCat` bundling — all
semireducible, so they agree at `.default` but not at `.instances`/reducible (Demo 1). Hence
the `Ring`, `Module` and `DistribMulAction` instances built on the two spellings agree only at
`.default` as well.

Site `tensorObj_map_tmul` (data-valued rejection, cleanest). Checking that lemma's `rfl`
forces synthesis of `Module ↑(R.obj Y) ↑((restrictScalars (R.map f).hom).obj (M₁.obj Y))`.
The candidate `@ModuleCat.isModule` must fill an instance-typed metavariable
`?m : Ring ↑(R.obj Y)` with the value the goal already carries,
`RingCat.instRingObjForgetRingHomCarrier : Ring ↑((R ⋙ forget₂ CommRingCat RingCat).obj Y)`.
Under `markOrSynth`, `checkTypesAndAssign` runs three checks:
  (a) the direct type check at `.instances` — `Ring ↑(R.obj Y) =?= Ring ↑((R ⋙ …).obj Y)` —
      fails, the carriers differ there (Demo 2 shows this ❌ with both types);
  (b) the fallback `synthPending` — succeeds, synthesizing the `CommRingCat`-native
      `CommRingCat.instCommRingObjForgetRingHomCarrier.toRing`;
  (c) the requirement that the goal's candidate be defeq to that synthesized instance — fails,
      because `RingCat.instRingObjForgetRingHomCarrier` and
      `CommRingCat.instCommRingObjForgetRingHomCarrier.toRing` are defeq only at `.default`,
      not at the `.instances` transparency instance search runs at (Demo 1).
So it is leg (c) that ultimately fails; with `set_option diagnostics true` the toolchain
reports it verbatim:
    failure when assigning instance metavariable with type
      Ring ↑(R.obj Y)
    the rejected candidate value
      RingCat.instRingObjForgetRingHomCarrier
    is not definitionally equal to the synthesized instance
      CommRingCat.instCommRingObjForgetRingHomCarrier.toRing
`ModuleCat.isModule` therefore cannot apply, no other candidate matches, the `Module` goal is
unsynthesizable, the coercion in the statement is ill-typed, and `rfl` fails.

Site `tensorObjMap` (this def). Same synonym, one instance layer up. The
`rw [TensorProduct.tmul_add]` in the third `tensorLift` argument forces synthesis of
`CompatibleSMul ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y) ↑(M₂.obj Y)`. Its only instance
`CompatibleSMul.isScalarTower` must fill `?m : DistribMulAction ↑(R.obj Y) ↑(M₂.obj Y)` with
the smul the goal carries on the `restrictScalars` object,
`ModuleCat.instModuleCarrierObjRestrictScalars.toDistribMulAction`, whose type is
`DistribMulAction ↑((R ⋙ …).obj Y) ↑((restrictScalars …).obj (M₂.obj Y))`. Legs (a)–(c) play
out exactly as above: (a) fails on the ring and module carriers at `.instances`, (b)
synthesizes the `ModuleCat`-native `(M₂.obj Y).isModule.toDistribMulAction`, (c) rejects
because the `restrictScalars`-packed instance is not defeq to it at `.instances` (Demo 3).
`CompatibleSMul` is then unsynthesizable and is left as an unsolved instance goal
("failed to synthesize … CompatibleSMul …"), which aborts the `rw`.

Consequences without the option: `tensorObjMap` cannot be elaborated, `tensorObj_map_tmul`
fails its `rfl`, and everything downstream (`tensorObj`, `tensorHom`, and the
monoidal/symmetric-category instances) collapses.

Shared cause: yes — both sites are the same `R.obj X` (`CommRingCat`) vs
`(R ⋙ forget₂ CommRingCat RingCat).obj X` (`RingCat`) carrier synonym; site
`tensorObj_map_tmul` hits it on a `Ring` metavariable, site `tensorObjMap` on a
`DistribMulAction` metavariable one `restrictScalars`/`CompatibleSMul` layer higher. This is
the reference analysis for the sibling cluster (`Presheaf/Sheafify.lean`,
`Differentials/Presheaf.lean`, `Monoidal/Closed.lean`, `Presheaf/Pushforward.lean`), which
share the `PresheafOfModules`/`ModuleCat.restrictScalars` carrier machinery.

Prop-exemption: not applicable. The rejected metavariables are `Ring` (site
`tensorObj_map_tmul`) and `DistribMulAction` (site `tensorObjMap`), both data-valued — even
though `tensorObjMap`'s outer class `CompatibleSMul` is a `Prop`, the parked exemption keys on
the rejected metavariable itself, not on the enclosing class.

Possible fixes (proof-local preferred): (i) spell the definitions and statements over the
`RingCat` carrier `↑((R ⋙ forget₂ CommRingCat RingCat).obj X)` that `M.obj X` actually uses,
removing the synonym crossing (at the cost of the `CommRing`/`R.obj X` readability the file was
written for); (ii) pass the offending `Ring`/`Module`/`DistribMulAction` instances explicitly
at the call sites so synthesis need not re-derive them; (iii) make the object action of
`forget₂ CommRingCat RingCat` reduce at `.instances` so the two carriers agree there — an
infrastructure definition change, out of scope here. Keeping `"none"` locally is the current
choice.
-/
set_option backward.isDefEq.instanceTypes "none" in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `tensorObj`. -/
noncomputable def tensorObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      rw [map_add, TensorProduct.tmul_add])
    (by intro a m₁ m₂; dsimp; erw [M₂.map_smul, TensorProduct.tmul_smul (r := R.map f a)]; rfl)

-- set_option linter.tacticChec/skInstances true

-- set_option allowUnsafeReducibility true
-- attribute [implicit_reducible]
--   -- Quiver.Hom
--   ModuleCat.restrictScalars
--   -- AddCon.Quotient
--   ModuleCat.RestrictScalars.obj'
--   -- tensorObj
--   -- Quotient
--   -- TensorProduct

-- #print ModuleCat.instModuleCarrierObjRestrictScalars

-- section

-- attribute [-instance] ModuleCat.instModuleCarrierObjRestrictScalars in
-- instance {R : Type u₁} {S : Type _} [Ring R] [Ring S] {f : R →+* S}
--     {M : ModuleCat.{v} S} : Module S <| (ModuleCat.restrictScalars f).obj M :=
--   inferInstanceAs <| Module S M
-- end

-- #print PresheafOfModules.Monoidal.instModuleCarrierObjModuleCatRestrictScalars
-- #print instModuleCarrierObjModuleCatRestrictScalars._aux_1

-- works if `ModuleCat.RestrictScalars.obj'` and `ModuleCat.restrictScalars` are implicit-reducible
-- so that synthesized instances and unified instances match.
-- However, that causes massive slowdowns!
postprocess_traces
  exposeSubtrees (fun x => (ofClass `Meta.isDefEq.assign.checkTypes x) <&&> failed x)
in
set_option backward.isDefEq.instanceTypes "none" in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `tensorObj`. -/
noncomputable example {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      rw [map_add, TensorProduct.tmul_add])
    (by
      intro a m₁ m₂
      dsimp
      erw [M₂.map_smul]
      (set_option trace.Meta.synthInstance true in
      set_option trace.Meta.isDefEq true in
      set_option trace.Meta.isDefEq.printTransparency true in
      set_option trace.Meta.isDefEq.assign.checkTypes true in
      erw [TensorProduct.tmul_smul (r := R.map f a)])
      rfl)


private meta partial def elideBelow (p : TracePattern) : TracePostprocessor :=
  fun trees => trees.mapM go
where
  go (t : TraceTree) : Lean.CoreM TraceTree := do
    match t with
    | .leaf msg => return .leaf msg
    | .node data msg children wrap =>
      if ← p t then
        return .node data m!"{msg} (truncated)" #[] wrap
      else
        return .node data msg (← children.mapM go) wrap

/--
error: failed to synthesize instance of type class
  TensorProduct.CompatibleSMul ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y) ↑(M₂.obj Y)
---
error: unsolved goals
C : Type u_1
inst✝ : Category.{v_1, u_1} C
R : Cᵒᵖ ⥤ CommRingCat
M₁ M₂ M₃ M₄ : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)
X Y : Cᵒᵖ
f : X ⟶ Y
a : ↑((R ⋙ forget₂ CommRingCat RingCat).obj X)
m₁ : ↑(M₁.obj X)
m₂ : ↑(M₂.obj X)
⊢ TensorProduct.CompatibleSMul ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y) ↑(M₂.obj Y)
---
trace: [Meta.synthInstance] ❌️ TensorProduct.CompatibleSMul ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y) ↑(M₂.obj Y)
  [Meta.synthInstance.apply] ❌️ apply @TensorProduct.CompatibleSMul.isScalarTower to TensorProduct.CompatibleSMul
        ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y) ↑(M₂.obj Y)
    [Meta.synthInstance.tryResolve] ❌️ TensorProduct.CompatibleSMul ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y)
          ↑(M₂.obj Y) ≟ TensorProduct.CompatibleSMul ?m.272 ?m.273 ?m.276 ?m.277
      [Meta.isDefEq] ❌️ [instances] TensorProduct.CompatibleSMul ↑(R.obj Y) ↑(R.obj Y) ↑(M₁.obj Y)
            ↑(M₂.obj Y) =?= TensorProduct.CompatibleSMul ?m.272 ?m.273 ?m.276 ?m.277
        [Meta.isDefEq] ❌️ [instances] ModuleCat.instModuleCarrierObjRestrictScalars.toDistribMulAction =?= ?m.285
          [Meta.isDefEq.assign.checkTypes] ❌️ (?m.285 : DistribMulAction ↑(R.obj Y)
                ↑(M₂.obj
                    Y)) := (ModuleCat.instModuleCarrierObjRestrictScalars.toDistribMulAction : DistribMulAction
                ↑((R ⋙ forget₂ CommRingCat RingCat).obj Y)
                ↑((ModuleCat.restrictScalars (RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map f))).obj
                    (M₂.obj Y))) (truncated)
          [Meta.isDefEq.assign.checkTypes] ❌️ (?m.285 : DistribMulAction ↑(R.obj Y)
                ↑(M₂.obj
                    Y)) := ({ toSMul := ModuleCat.instModuleCarrierObjRestrictScalars._aux_1, mul_smul := ⋯,
                one_smul := ⋯, smul_zero := ⋯,
                smul_add :=
                  ⋯ } : DistribMulAction ↑((R ⋙ forget₂ CommRingCat RingCat).obj Y)
                ↑((ModuleCat.restrictScalars (RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map f))).obj
                    (M₂.obj Y))) (truncated)
-/
#guard_msgs in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.isDefEq.assign.checkTypes x) <&&> failed x)
  >=> elideBelow (fun x => (ofClass `Meta.isDefEq.assign.checkTypes x) <&&> failed x)
in
set_option backward.isDefEq.instanceTypes "markOrSynth" in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `tensorObj`. -/
noncomputable example {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      rw [map_add, TensorProduct.tmul_add])
    (by
      intro a m₁ m₂
      dsimp
      erw [M₂.map_smul]
      (set_option trace.Meta.synthInstance true in
      set_option trace.Meta.isDefEq true in
      set_option trace.Meta.isDefEq.printTransparency true in
      set_option trace.Meta.isDefEq.assign.checkTypes true in
      erw [TensorProduct.tmul_smul (r := R.map f a)])
      rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two presheaves of modules. -/
@[simps obj]
noncomputable def tensorObj : PresheafOfModules (R ⋙ forget₂ _ _) where
  obj X := M₁.obj X ⊗ M₂.obj X
  map f := tensorObjMap M₁ M₂ f
  map_id X := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp
    rfl) -- `ModuleCat.restrictScalarsId'App_inv_apply` doesn't get picked up due to type mismatch
  map_comp f g := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp +instances)

variable {M₁ M₂ M₃ M₄}

-- Needs `instanceTypes "none"` for the same `R.obj Y` (`CommRingCat`) vs
-- `(R ⋙ forget₂ CommRingCat RingCat).obj Y` (`RingCat`) ring-carrier synonym as `tensorObjMap`
-- above: here the `Module ↑(R.obj Y) ↑((restrictScalars …).obj (M₁.obj Y))` needed to type the
-- coercion is unsynthesizable because its `Ring ↑(R.obj Y)` slot rejects (leg (c)) the
-- `RingCat`-bundled instance the goal carries. See the analysis before `tensorObjMap`.
set_option backward.isDefEq.instanceTypes "none" in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X :))
      (β := fun _ ↦ (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((tensorObj M₁ M₂).map f)) (m₁ ⊗ₜ[R.obj X] m₂) =
    M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two morphisms of presheaves of modules. -/
@[simps]
noncomputable def tensorHom (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) : tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ where
  app X := f.app X ⊗ₘ g.app X
  naturality {X Y} φ := ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ ↦ by
    dsimp
    rw [tensorObj_map_tmul]
    -- Need `erw` because of the type mismatch in `map` and the tensor product.
    erw [ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul]
    rw [naturality_apply, naturality_apply]
    simp)

end Monoidal

open Monoidal

open ModuleCat.MonoidalCategory in
noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorObj := tensorObj
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom := tensorHom
  tensorUnit := unit _
  associator M₁ M₂ M₃ := isoMk (fun _ ↦ α_ _ _ _)
    (fun _ _ _ ↦ ModuleCat.MonoidalCategory.tensor_ext₃' (by intros; rfl))
  leftUnitor M := Iso.symm (isoMk (fun _ ↦ (λ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [leftUnitor_inv_apply, leftUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))
  rightUnitor M := Iso.symm (isoMk (fun _ ↦ (ρ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [rightUnitor_inv_apply, rightUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))

noncomputable instance monoidalCategory :
    MonoidalCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorHom_def _ _ := by ext1; apply tensorHom_def
  id_tensorHom_id _ _ := by ext1; apply id_tensorHom_id
  tensorHom_comp_tensorHom _ _ _ _ := by ext1; apply tensorHom_comp_tensorHom
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by
    ext1 X
    apply MonoidalCategory.id_whiskerRight (C := ModuleCat (R.obj X))
  associator_naturality _ _ _ := by ext1; apply associator_naturality
  leftUnitor_naturality _ := by ext1; apply leftUnitor_naturality
  rightUnitor_naturality _ := by ext1; apply rightUnitor_naturality
  pentagon _ _ _ _ := by ext1; apply pentagon
  triangle _ _ := by ext1; apply triangle

open BraidedCategory

noncomputable instance symmetricCategory :
    SymmetricCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  braiding M₁ M₂ :=
    isoMk (fun X ↦ braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X))
      (fun _ _ f ↦ ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl))
  braiding_naturality_right _ _ _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  braiding_naturality_left _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  hexagon_forward _ _ _ := by
    ext : 1
    apply hexagon_forward (C := ModuleCat (R.obj _))
  hexagon_reverse _ _ _ := by
    ext : 1
    apply hexagon_reverse (C := ModuleCat (R.obj _))
  symmetry _ _ := by
    ext : 1
    apply SymmetricCategory.symmetry (C := ModuleCat (R.obj _))

section

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

lemma tensorObj_obj (X : Cᵒᵖ) :
    (M₁ ⊗ M₂).obj X =
      MonoidalCategory.tensorObj (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

variable {M₂ M₃} in
@[simp]
lemma whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    dsimp% (M₁ ◁ f).app X = whiskerLeft (C := ModuleCat (R.obj X)) (M₁.obj X) (f.app X) :=
  rfl

variable {M₁ M₂} in
@[simp]
lemma whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    dsimp% (f ▷ M₃).app X = whiskerRight (C := ModuleCat (R.obj X)) (f.app X) (M₃.obj X) := rfl

variable {M₁ M₂ M₃ M₄} in
@[simp]
lemma tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    dsimp% (f ⊗ₘ g).app X =
      MonoidalCategory.tensorHom (C := ModuleCat (R.obj X)) (f.app X) (g.app X) := rfl

@[simp]
lemma leftUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).hom.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma leftUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).inv.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv := by
  rfl

@[simp]
lemma rightUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).hom.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma rightUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).inv.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv :=
  rfl

@[simp]
lemma associator_hom_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).hom.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).hom :=
  rfl

@[simp]
lemma associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

@[simp]
lemma braiding_hom_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).hom.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).hom := by
  rfl

@[simp]
lemma braiding_inv_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).inv.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).inv := rfl

end

instance (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PreservesColimitsOfSize.{u, u} (tensorLeft F) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _ _
      (fun X ↦ isColimitOfPreserves (tensorLeft (show ModuleCat (R.obj X) from F.obj X))
        (isColimitOfPreserves (evaluation _ X) hc))⟩⟩⟩

instance (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PreservesColimitsOfSize.{u, u} (tensorRight F) :=
  preservesColimits_of_natIso (tensorLeftIsoTensorRight F)

section InstanceTypesDemos
/-!
Guarded demonstrations for the two `backward.isDefEq.instanceTypes "none"` sites above.
The trace demo pins `"markOrSynth"` (the `lakefile.lean` project default; a bare
`lake env lean` would otherwise fall back to the toolchain register default `"mark"`).
`with_reducible rfl` is used as a proxy for the `.instances` transparency the instance-type
check runs at: it accepts nothing below `.default`, which is exactly where the two ring
spellings and the instances built on them diverge. Delete this whole section once the
`R.obj`/`forget₂` carrier synonym is resolved upstream.
-/
open Lean.PostprocessTraces

namespace PresheafOfModules.Monoidal

/-- Keeps the `checkTypes` rejection head lines (both types) but drops their verbose
fallback-synthesis subtrees, so the trace demo stays small. -/
private meta partial def dropCheckTypesChildren (t : TraceTree) : TraceTree :=
  if t.cls? == some `Meta.isDefEq.assign.checkTypes then t.withChildren #[]
  else t.withChildren (t.children.map dropCheckTypesChildren)

-- Demo 1 (shared root cause). The ring carriers, and the `Ring` instances built on them (site
-- `tensorObj_map_tmul`'s leg (c) pair), agree at `.default` …
example (X : Cᵒᵖ) : (↑(R.obj X) : Type u) = ↑((R ⋙ forget₂ CommRingCat RingCat).obj X) := rfl
example (X : Cᵒᵖ) :
    (RingCat.instRingObjForgetRingHomCarrier (R := (R ⋙ forget₂ CommRingCat RingCat).obj X)) =
      (CommRingCat.instCommRingObjForgetRingHomCarrier (R := R.obj X)).toRing := rfl
-- … but not at `.instances`/reducible, which is why leg (c) rejects the goal's candidate:
/--
error: Tactic `rfl` failed: The left-hand side
  RingCat.instRingObjForgetRingHomCarrier
is not definitionally equal to the right-hand side
  CommRingCat.instCommRingObjForgetRingHomCarrier.toRing

C : Type u_1
inst✝ : Category.{v_1, u_1} C
R : Cᵒᵖ ⥤ CommRingCat
X : Cᵒᵖ
⊢ RingCat.instRingObjForgetRingHomCarrier = CommRingCat.instCommRingObjForgetRingHomCarrier.toRing
-/
#guard_msgs in
example (X : Cᵒᵖ) :
    (RingCat.instRingObjForgetRingHomCarrier (R := (R ⋙ forget₂ CommRingCat RingCat).obj X)) =
      (CommRingCat.instCommRingObjForgetRingHomCarrier (R := R.obj X)).toRing := by
  with_reducible_and_instances rfl

-- Demo 2 (site `tensorObj_map_tmul`, live). Under `markOrSynth` the `Module` needed to type the
-- statement is unsynthesizable: `ModuleCat.isModule`'s `Ring ↑(R.obj Y)` slot rejects, at
-- `.instances`, the `RingCat`-bundled `Ring` the goal carries (the ❌ `checkTypes` line shows
-- both types; the fallback subtree that would rediscover the `CommRingCat`-native instance —
-- leg (c) — is pruned away for brevity).
set_option backward.isDefEq.instanceTypes "markOrSynth" in
set_option backward.isDefEq.respectTransparency false in
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq.assign.checkTypes true in
set_option linter.style.longLine false in
/--
error: failed to synthesize instance of type class
  Module ↑(R.obj Y)
    ↑((ModuleCat.restrictScalars (RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map f))).obj (M₁.obj Y))
---
trace: [Meta.synthInstance] ❌️ Module ↑(R.obj Y)
      ↑((ModuleCat.restrictScalars (RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map f))).obj (M₁.obj Y))
  [Meta.synthInstance.apply] ❌️ apply @ModuleCat.isModule to Module ↑(R.obj Y)
        ↑((ModuleCat.restrictScalars (RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map f))).obj (M₁.obj Y))
    [Meta.synthInstance.tryResolve] ❌️ Module ↑(R.obj Y)
          ↑((ModuleCat.restrictScalars (RingCat.Hom.hom ((R ⋙ forget₂ CommRingCat RingCat).map f))).obj
              (M₁.obj Y)) ≟ Module ?m.142 ↑?m.144
      [Meta.isDefEq.assign.checkTypes] ❌️ (?m.143 : Ring
            ↑(R.obj
                Y)) := (RingCat.instRingObjForgetRingHomCarrier : Ring
            ((forget RingCat).obj ((R ⋙ forget₂ CommRingCat RingCat).obj X)))
-/
#guard_msgs in
postprocess_traces
  (filterSubtrees (fun x => (ofClass `Meta.synthInstance.apply x)
      <&&> (containsString "ModuleCat.isModule" x) <&&> (containsString "M₁.obj Y" x)))
  >=> (fun roots => return roots.map dropCheckTypesChildren)
  >=> (filterSubtrees (fun x => (failed x) <&&> (containsString "instRingObjForget" x)))
in
example {M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X :))
      (β := fun _ ↦ (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X))
        ((_root_.PresheafOfModules.Monoidal.tensorObj M₁ M₂).map f)) (m₁ ⊗ₜ[R.obj X] m₂) =
    M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

-- Demo 3 (site `tensorObjMap`, leg (c) value pair). The smul the goal carries on the
-- `restrictScalars` object and the `ModuleCat`-native smul instance synthesis produces agree at
-- `.default` …
example {M₂ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.instModuleCarrierObjRestrictScalars
        (f := (R.map f).hom) (M := M₂.obj Y)).toDistribMulAction =
      (M₂.obj Y).isModule.toDistribMulAction := rfl
-- … but not at `.instances`/reducible, so `CompatibleSMul.isScalarTower`'s `DistribMulAction`
-- slot rejects it:
set_option linter.style.longLine false in
/--
error: Tactic `rfl` failed: The left-hand side
  @Module.toDistribMulAction (↑(R.obj Y))
    (↑((ModuleCat.restrictScalars (CommRingCat.Hom.hom (R.map f))).obj (M₂.obj Y)))
    CommRingCat.instCommRingObjForgetRingHomCarrier.toSemiring
    ((ModuleCat.restrictScalars (CommRingCat.Hom.hom (R.map f))).obj (M₂.obj Y)).isAddCommGroup.toAddCommMonoid
    ModuleCat.instModuleCarrierObjRestrictScalars
is not definitionally equal to the right-hand side
  @Module.toDistribMulAction (↑((R ⋙ forget₂ CommRingCat RingCat).obj Y)) (↑(M₂.obj Y))
    RingCat.instRingObjForgetRingHomCarrier.toSemiring (M₂.obj Y).isAddCommGroup.toAddCommMonoid (M₂.obj Y).isModule

C : Type u_1
inst✝ : Category.{v_1, u_1} C
R : Cᵒᵖ ⥤ CommRingCat
M₂ : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)
X Y : Cᵒᵖ
f : X ⟶ Y
⊢ ModuleCat.instModuleCarrierObjRestrictScalars.toDistribMulAction = (M₂.obj Y).isModule.toDistribMulAction
-/
#guard_msgs in
example {M₂ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.instModuleCarrierObjRestrictScalars
        (f := (R.map f).hom) (M := M₂.obj Y)).toDistribMulAction =
      (M₂.obj Y).isModule.toDistribMulAction := by
  with_reducible rfl

end PresheafOfModules.Monoidal
end InstanceTypesDemos

end PresheafOfModules
