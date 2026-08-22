/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Commutative group objects in additive categories.

We construct an inverse of the forgetful functor `CommGrp C ⥤ C` if `C` is an additive category.

This looks slightly strange because the additive structure of `C` maps to the multiplicative
structure of the commutative group objects.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Preadditive

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [CartesianMonoidalCategory C]

@[simps]
instance (X : C) : GrpObj X where
  one := 0
  mul := fst _ _ + snd _ _
  inv := -𝟙 X
  one_mul := by simp [← leftUnitor_hom]
  mul_one := by simp [← rightUnitor_hom]
  mul_assoc := by simp [add_assoc]

variable [BraidedCategory C]

instance (X : C) : IsCommMonObj X where
  mul_comm := by simp [add_comm]

variable (C) in
/-- The canonical functor from an additive category into its commutative group objects. This is
always an equivalence, see `commGrpEquivalence`. -/
@[simps]
def toCommGrp : C ⥤ CommGrp C where
  obj X := ⟨X⟩
  map {X Y} f := InducedCategory.homMk (Grp.homMk'' f)

-- PROJECT: develop `ChosenFiniteCoproducts`, and construct `ChosenFiniteCoproducts` from
-- `CartesianMonoidalCategory` in preadditive categories, to give this lemma a proper home.
set_option backward.privateInPublic true in
omit [BraidedCategory C] in
private theorem monoidal_hom_ext {X Y Z : C} {f g : X ⊗ Y ⟶ Z}
    (h₁ : lift (𝟙 X) 0 ≫ f = lift (𝟙 X) 0 ≫ g) (h₂ : lift 0 (𝟙 Y) ≫ f = lift 0 (𝟙 Y) ≫ g) :
    f = g :=
  BinaryCofan.IsColimit.hom_ext
    (binaryBiconeIsBilimitOfLimitConeOfIsLimit (tensorProductIsBinaryProduct X Y)).isColimit h₁ h₂

-- This declaration needed `backward.isDefEq.respectTransparency.instances false` and the parent
-- `backward.isDefEq.respectTransparency false`. The parent is gone. The marks below replace it.
-- `lax_instance_defeq MonObj` has to stay. The analysis below is for that state, with the parent
-- removed and the marks in place.
--
-- The `simp only` further down rewrites `(𝟭 (CommGrp C)).obj x✝` to `x✝` in the carrier of
-- `MonObj.mul`. It leaves the `MonObj` instance beside it alone. `convert!` then offers the old
-- instance for the new type. Two metavariables, one per `convert!`, 6 rejections in total:
--
--   ❌ type check, pinned at [instances]
--        MonObj ((CommGrp.forget C ⋙ toCommGrp C).obj x✝).X
--          =?= MonObj ((𝟭 (CommGrp C)).obj x✝).X
--   ✅ synthesis
--        goal    MonObj ((CommGrp.forget C ⋙ toCommGrp C).obj x✝).X
--        result  ((CommGrp.forget C ⋙ toCommGrp C).obj x✝).grp.toMonObj
--   ❌ unify, at the ambient [implicit]
--        ((𝟭 (CommGrp C)).obj x✝).grp.toMonObj
--          =?= ((CommGrp.forget C ⋙ toCommGrp C).obj x✝).grp.toMonObj
--      ↳ ❌ [implicit] MonObj.one =?= 0
--
-- That unify does not succeed at `all` transparency either. Checked with `with_unfolding_all rfl`
-- on `x.grp.toMonObj = ((toCommGrp C).obj x.X).grp.toMonObj`, and on the `one` and `mul` fields
-- separately. All three fail. So this is a real gap and not a transparency setting. No mark can
-- close it, at any level.
--
-- The reason is that `toCommGrp` does not give the instance back. `CommGrp C` carries `grp` as an
-- instance field, and `toCommGrp C` has `obj X := ⟨X⟩`. That discards `x.grp` and lets synthesis
-- refill the field from the global `GrpObj` instance at the top of this file, with `one := 0` and
-- `mul := fst _ _ + snd _ _`. So the unify asks whether an arbitrary group object structure on
-- `x.X` equals the canonical one built from the additive structure. That is exactly what this
-- declaration proves propositionally. `Subsingleton.elim` handles `one` and `monoidal_hom_ext`
-- handles `mul`.
--
-- The marks do bite, and they are needed. They take the whole forgetful tower down to
-- `((𝟭 (CommGrp C)).obj x✝).1 =?= x✝.1` at [implicit], so both carriers agree. Only the instance
-- fields differ.
--
-- That is also what `lax_instance_defeq MonObj` buys. The metavariable needs some `MonObj` on that
-- carrier to be type-correct, and the carriers are equal. Route 1 asks for more, that the offered
-- instance equal the synthesized one. The attribute drops that extra demand and keeps the type
-- check.
--
-- The trace also has 4 rejections on `OfNat (?m ⟶ 𝟙_ ?m) 0`, from the literal `0` in
-- `MonObj.lift_comp_one_right _ 0`. Synthesis ends in 💥 on a stuck hom type, so there is no term
-- to unify. Those are inert. The attribute cannot touch an `OfNat` metavariable, and the file
-- compiles.
attribute [local lax_instance_defeq] MonObj in
attribute [local implicit_reducible]
  toCommGrp CommGrp.forget CommGrp.forget₂Grp Grp.forget
  Grp.forget₂Mon Mon.forget
in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Auxiliary definition for `commGrpEquivalence`. -/
@[simps!]
def commGrpEquivalenceAux : CommGrp.forget C ⋙ toCommGrp C ≅
      𝟭 (CommGrp C) := by
  refine NatIso.ofComponents (fun _ => CommGrp.mkIso (Iso.refl _) ?_ ?_) ?_
  · exact ((IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)).eq_of_src _ _
  · simp only [Functor.id_obj,
      mul_def, Iso.refl_hom, Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    apply monoidal_hom_ext
    · simp only [comp_add, lift_fst, lift_snd, add_zero]
      convert! (MonObj.lift_comp_one_right _ 0).symm
      · simp
      · infer_instance
    · simp only [comp_add, lift_fst, lift_snd, zero_add]
      convert! (MonObj.lift_comp_one_left 0 _).symm
      · simp
      · infer_instance
  · cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An additive category is equivalent to its category of commutative group objects. -/
@[simps!]
def commGrpEquivalence : C ≌ CommGrp C where
  functor := toCommGrp C
  inverse := CommGrp.forget C
  unitIso := Iso.refl _
  counitIso := commGrpEquivalenceAux

end CategoryTheory.Preadditive
