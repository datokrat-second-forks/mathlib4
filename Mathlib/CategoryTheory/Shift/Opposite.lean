/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The (naive) shift on the opposite category

If `C` is a category equipped with a shift by a monoid `A`, the opposite category
can be equipped with a shift such that the shift functor by `n` is `(shiftFunctor C n).op`.
This is the "naive" opposite shift, which we shall set on a category `OppositeShift C A`,
which is a type synonym for `Cᵒᵖ`.

However, for the application to (pre)triangulated categories, we would like to
define the shift on `Cᵒᵖ` so that `shiftFunctor Cᵒᵖ n` for `n : ℤ` identifies to
`(shiftFunctor C (-n)).op` rather than `(shiftFunctor C n).op`. Then, the construction
of the shift on `Cᵒᵖ` shall combine the shift on `OppositeShift C A` and another
construction of the "pullback" of a shift by a monoid morphism like `n ↦ -n`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `A`, we define
a type synonym `OppositeShift.functor A F` for `F.op`. When `F` has a `CommShift` structure
by `A`, we define a `CommShift` structure by `A` on `OppositeShift.functor A F`. In this
way, we can make this an instance and reserve `F.op` for the `CommShift` instance by
the modified shift in the case of (pre)triangulated categories.

Similarly, if `τ` is a natural transformation between functors `F,G : C ⥤ D`, we define
a type synonym for `τ.op` called
`OppositeShift.natTrans A τ : OppositeShift.functor A F ⟶ OppositeShift.functor A G`.
When `τ` has a `CommShift` structure by `A` (i.e. is compatible with `CommShift` structures
on `F` and `G`), we define a `CommShift` structure by `A` on `OppositeShift.natTrans A τ`.

Finally, if we have an adjunction `F ⊣ G` (with `G : D ⥤ C`), we define a type synonym
`OppositeShift.adjunction A adj : OppositeShift.functor A G ⊣ OppositeShift.functor A F`
for `adj.op`, and we show that, if `adj` compatible with `CommShift` structures
on `F` and `G`, then `OppositeShift.adjunction A adj` is also compatible with the pulled back
`CommShift` structures.

Given a `CommShift` structure on a functor `F`, we define a `CommShift` structure on `F.op`
(and vice versa).
We also prove that, if an adjunction `F ⊣ G` is compatible with `CommShift` structures on
`F` and `G`, then the opposite adjunction `G.op ⊣ F.op` is compatible with the opposite
`CommShift` structures.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

section

variable (C : Type*) [Category* C] (A : Type*) [AddMonoid A] [HasShift C A]

namespace HasShift

set_option backward.defeqAttrib.useBackward true in
/-- Construction of the naive shift on the opposite category of a category `C`:
the shiftfunctor by `n` is `(shiftFunctor C n).op`. -/
def mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where
  F n := (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_zero_add_inv_app n X.unop).trans (by simp))
  add_zero_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_add_zero_inv_app n X.unop).trans (by simp))

end HasShift

/-- The category `OppositeShift C A` is the opposite category `Cᵒᵖ` equipped
with the naive shift: `shiftFunctor (OppositeShift C A) n` is `(shiftFunctor C n).op`. -/
@[nolint unusedArguments]
def OppositeShift (A : Type*) [AddMonoid A] [HasShift C A] := Cᵒᵖ

instance : Category (OppositeShift C A) := inferInstanceAs (Category Cᵒᵖ)

instance : HasShift (OppositeShift C A) A :=
  hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)

set_option backward.isDefEq.respectTransparency false in
instance [HasZeroObject C] : HasZeroObject (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance

instance [Preadditive C] : Preadditive (OppositeShift C A) :=
  inferInstanceAs (Preadditive Cᵒᵖ)

instance [Preadditive C] (n : A) [(shiftFunctor C n).Additive] :
    (shiftFunctor (OppositeShift C A) n).Additive := by
  change (shiftFunctor C n).op.Additive
  infer_instance

lemma oppositeShiftFunctorZero_inv_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).inv.app X =
      ((shiftFunctorZero C A).hom.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
lemma oppositeShiftFunctorZero_hom_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).hom.app X =
      ((shiftFunctorZero C A).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorZero (OppositeShift C A) A).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorZero_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

variable {C A}
variable (X : OppositeShift C A) (a b c : A) (h : a + b = c)

lemma oppositeShiftFunctorAdd_inv_app :
    (shiftFunctorAdd (OppositeShift C A) a b).inv.app X =
      ((shiftFunctorAdd C a b).hom.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
lemma oppositeShiftFunctorAdd_hom_app :
    (shiftFunctorAdd (OppositeShift C A) a b).hom.app X =
      ((shiftFunctorAdd C a b).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorAdd (OppositeShift C A) a b).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorAdd_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma oppositeShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).inv.app X =
      ((shiftFunctorAdd' C a b c h).hom.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app]

set_option backward.isDefEq.respectTransparency.types false in
lemma oppositeShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).hom.app X =
      ((shiftFunctorAdd' C a b c h).inv.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app]

end

variable {C D : Type*} [Category* C] [Category* D] (A : Type*) [AddMonoid A]
  [HasShift C A] [HasShift D A] (F : C ⥤ D)

/--
The functor `F.op`, seen as a functor from `OppositeShift C A` to `OppositeShift D A`.
(We will use this to carry a `CommShift` instance for the naive shifts on the opposite category.
Then, in the pretriangulated case, we will be able to put a `CommShift` instance on `F.op`
for the modified shifts and not deal with instance clashes.)
-/
def OppositeShift.functor : OppositeShift C A ⥤ OppositeShift D A := F.op

variable {F} in
/--
The natural transformation `τ`, seen as a natural transformation from `OppositeShift.functor F A`
to `OppositeShift.functor G A`..
-/
def OppositeShift.natTrans {G : C ⥤ D} (τ : F ⟶ G) :
    OppositeShift.functor A G ⟶ OppositeShift.functor A F :=
  NatTrans.op τ

namespace Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Given a `CommShift` structure on `F`, this is the corresponding `CommShift` structure on
`OppositeShift.functor F` (for the naive shifts on the opposite categories).
-/
instance commShiftOp [CommShift F A] :
    CommShift (OppositeShift.functor A F) A where
  commShiftIso a := (NatIso.op (F.commShiftIso a)).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoZero_inv_app, op_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorZero_hom_app]
    rfl
  commShiftIso_add a b := by
    rw [commShiftIso_add]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoAdd_inv_app, op_comp, Category.assoc, CommShift.isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_inv_app, oppositeShiftFunctorAdd_hom_app]
    rfl

lemma commShiftOp_iso_eq [CommShift F A] (a : A) :
    (OppositeShift.functor A F).commShiftIso a = (NatIso.op (F.commShiftIso a)).symm := rfl

-- Both options are still needed, and neither one alone is enough. Measured, per configuration:
--   * parent option only: exactly three `simp only` arguments go unused, `unop_comp` twice and
--     `Category.assoc` once, and the final `rfl` of `commShiftIso_add` then fails.
--     `with_unfolding_all rfl` does not rescue it.
--   * `instances false` only: eleven arguments go unused, and both `erw` steps fail
--     (`oppositeShiftFunctorZero_hom_app` and `oppositeShiftFunctorAdd_hom_app`).
--   * neither option: as the previous case.
-- The rest of this note describes the **parent-option-only** configuration.
--
-- ❌ mvar-type check at [instances] — the `[HasShift ?C A]` argument, after the `ᵒᵖ`-stated
--    `NatIso.removeOp_hom` / `NatTrans.removeOp_app` have already pinned `?C := Cᵒᵖ`:
--      HasShift Cᵒᵖ A  =?=  HasShift (OppositeShift C A) A
--        blocked by `Cᵒᵖ =?= OppositeShift C A`, and inside it by `Opposite =?= OppositeShift`
--      assigned: instHasShiftOppositeShift C A
--      synth ❌ — `HasShift Cᵒᵖ A` deliberately does not exist, and both candidates
--        `#[inst✝², inst✝¹]` fail → no unify
-- `OppositeShift C A` is a type synonym for `Cᵒᵖ` whose whole point is to carry a *different*
-- `HasShift`, so it must stay opaque to instance search: `instance_reducible` is out, and
-- `implicit_reducible` does not reach a check pinned to `.instances`.
-- With every option removed the shape differs: the rejected metavariable is the `Iso` being
-- rewritten rather than a `HasShift` instance, the check runs at [implicit], and there is no
-- synthesis step. The blocking pair is the same `Opposite =?= OppositeShift`.
--
-- The rejection does not make `isoZero_inv_app` fail. Its LHS and the goal subterm are both headed
-- by `NatTrans.app`, and the goal subterm is *mixed*: the outer `NatTrans.app` is `ᵒᵖ`-spelled
-- (left that way by the `removeOp` lemmas above) while the `CommShift.isoZero` inside it is
-- `OppositeShift`-spelled. One `isDefEq` then tries two things:
--   1. same head, unify the arguments pairwise. `?A` and the `AddMonoid A` slot pass, then the
--      `[HasShift ?C A]` slot can only take `instHasShiftOppositeShift`, which is the rejection
--      above. Rolled back.
--   2. both sides are unfolded to the projection form `(CommShift.isoZero … ).inv.1 X`, and the
--      *projected structures* are compared first. Now `?C := OppositeShift C A` and
--      `?inst := instCategoryOppositeShift C A`, everything is consistent and passes.
-- So the rewrite succeeds either way — in a *different spelling*. Nothing is reordered: the two
-- rewrite sequences are identical lemma for lemma, only `unop_comp` (and the `Category.assoc` steps
-- it enables) drop out of the one without `instances false`.
-- That is what reaches `unop_comp` below, which involves no `HasShift` at all: it is not a failed
-- rewrite but a *discrimination-tree miss*. With `instances false` the rejected assignment goes
-- through, so `CommShift.isoZero_inv_app` / `isoAdd_inv_app` rewrite into the `Cᵒᵖ` /
-- `Category.opposite` spelling, and `unop_comp` — indexed under `Opposite` — matches and fires.
-- Without it those lemmas instantiate honestly at `OppositeShift C A` and
-- `instCategoryOppositeShift`,
-- the resulting `CategoryStruct.comp` is indexed under `OppositeShift`, and simp never retrieves
-- `unop_comp` at all: with every `Meta.Tactic.simp` trace class enabled it appears only in the echo
-- of the argument list and in the unused-argument warning, never in a rewrite attempt.
set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.isDefEq.respectTransparency false in
/--
Given a `CommShift` structure on `OppositeShift.functor F` (for the naive shifts on the opposite
categories), this is the corresponding `CommShift` structure on `F`.
-/
@[simps -isSimp, instance_reducible]
def commShiftUnop
    [CommShift (OppositeShift.functor A F) A] : CommShift F A where
  commShiftIso a := NatIso.removeOp ((OppositeShift.functor A F).commShiftIso a).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoZero_inv_app, unop_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_hom_app, oppositeShiftFunctorZero_inv_app]
    rfl
  commShiftIso_add a b := by
    rw [commShiftIso_add]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoAdd_inv_app, unop_comp, Category.assoc,
      CommShift.isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_hom_app, oppositeShiftFunctorAdd_inv_app]
    rfl

end Functor

namespace NatTrans

variable {F} {G : C ⥤ D} [F.CommShift A] [G.CommShift A]

open Opposite in
instance commShift_op (τ : F ⟶ G) [NatTrans.CommShift τ A] :
    NatTrans.CommShift (OppositeShift.natTrans A τ) A where
  shift_comm _ := by
    ext
    rw [← cancel_mono (((OppositeShift.functor A F).commShiftIso _).inv.app _),
      ← cancel_epi (((OppositeShift.functor A G).commShiftIso _).inv.app _)]
    simp only [Functor.comp_obj, comp_app, Functor.whiskerRight_app, assoc,
      Iso.inv_hom_id_app_assoc, Functor.whiskerLeft_app, Iso.hom_inv_id_app, comp_id]
    exact (op_inj_iff _ _).mpr (NatTrans.shift_app_comm τ _ (unop _))

end NatTrans

namespace NatTrans

variable (C) in
/-- The obvious isomorphism between the identity of `OppositeShift C A` and
`OppositeShift.functor (𝟙 C)`.
-/
def OppositeShift.natIsoId : 𝟭 (OppositeShift C A) ≅ OppositeShift.functor A (𝟭 C) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The natural isomorphism `NatTrans.OppositeShift.natIsoId C A` commutes with shifts.
-/
instance : NatTrans.CommShift (OppositeShift.natIsoId C A).hom A where
  shift_comm _ := by
    ext
    dsimp [OppositeShift.natIsoId, Functor.commShiftOp_iso_eq]
    simp only [Functor.commShiftIso_id_hom_app, Functor.map_id,
      comp_id, Functor.commShiftIso_id_inv_app, CategoryTheory.op_id, id_comp]
    rfl

variable {E : Type*} [Category* E] [HasShift E A] (G : D ⥤ E)

/-- The obvious isomorphism between `OppositeShift.functor (F ⋙ G)` and the
composition of `OppositeShift.functor F` and `OppositeShift.functor G`.
-/
def OppositeShift.natIsoComp : OppositeShift.functor A (F ⋙ G) ≅
    OppositeShift.functor A F ⋙ OppositeShift.functor A G := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [F.CommShift A] [G.CommShift A] :
    NatTrans.CommShift (OppositeShift.natIsoComp A F G).hom A where
  shift_comm _ := by
    ext
    dsimp [OppositeShift.natIsoComp, Functor.commShiftOp_iso_eq]
    simp only [Functor.map_id, comp_id, id_comp]
    rfl

end NatTrans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The adjunction `adj`, seen as an adjunction between `OppositeShift.functor G`
and `OppositeShift.functor F`.
-/
@[simps -isSimp]
def OppositeShift.adjunction {F} {G : D ⥤ C} (adj : F ⊣ G) :
    OppositeShift.functor A G ⊣ OppositeShift.functor A F where
  unit := (NatTrans.OppositeShift.natIsoId D A).hom ≫
    OppositeShift.natTrans A adj.counit ≫ (NatTrans.OppositeShift.natIsoComp A G F).hom
  counit := (NatTrans.OppositeShift.natIsoComp A F G).inv ≫
    OppositeShift.natTrans A adj.unit ≫ (NatTrans.OppositeShift.natIsoId C A).inv
  left_triangle_components _ := by
    dsimp [OppositeShift.natTrans, NatTrans.OppositeShift.natIsoComp,
      NatTrans.OppositeShift.natIsoId, OppositeShift.functor]
    simp only [comp_id, id_comp, Quiver.Hom.unop_op]
    rw [← op_comp, adj.right_triangle_components]
    rfl
  right_triangle_components _ := by
    dsimp [OppositeShift.natTrans, NatTrans.OppositeShift.natIsoComp,
      NatTrans.OppositeShift.natIsoId, OppositeShift.functor]
    simp only [comp_id, id_comp, Quiver.Hom.unop_op]
    rw [← op_comp, adj.left_triangle_components]
    rfl

namespace Adjunction

variable {F} {G : D ⥤ C} (adj : F ⊣ G)

/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F` and `G`, then
the opposite adjunction `OppositeShift.adjunction adj` is compatible with the opposite
`CommShift` structures.
-/
instance commShift_op [F.CommShift A] [G.CommShift A] [adj.CommShift A] :
    Adjunction.CommShift (OppositeShift.adjunction A adj) A where
  commShift_unit := by dsimp [OppositeShift.adjunction]; infer_instance
  commShift_counit := by dsimp [OppositeShift.adjunction]; infer_instance

end Adjunction

end CategoryTheory
