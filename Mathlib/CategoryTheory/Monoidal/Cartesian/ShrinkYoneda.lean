/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.MonCat.Shrink
public import Mathlib.Algebra.Category.Grp.Shrink
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The Yoneda embedding for monoid objects for locally small categories

Let `C` be a locally `w`-small category. We define the Yoneda
embedding `shrinkYonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} w` and its `Grp` analogue.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [CartesianMonoidalCategory C]

set_option backward.defeqAttrib.useBackward true in
instance (M : Mon C) (X : Cᵒᵖ) : Small.{w} ((yonedaMon.obj M).obj X) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (M : Grp C) (X : Cᵒᵖ) : Small.{w} ((yonedaGrp.obj M).obj X) := by
  dsimp
  infer_instance

-- `backward.isDefEq.respectTransparency.instances false` stays on six declarations below. Two
-- more sites were stale and are removed. All six declarations also carry
-- `backward.isDefEq.respectTransparency false`, but that option alone is not sufficient.
--
-- Trace on `shrinkYonedaMon` with `.instances false` removed and the other options kept:
--   ❌ mvar type check:
--     ❌ Small.{w, v} ↑((yonedaMonObj X.X).obj Y) =?= Small.{w, v} ↑((yonedaMon.obj X).obj Y)
--     assigned: the `Small` instance declared above, which is stated at `(yonedaMon.obj M).obj X`
--     ❌ synth ("the instance could not be synthesized directly")
--     unification would not succeed at [implicit]. It needs [default].
--
-- The comparison goes down to `(yonedaMonObj X.X).1 =?= (yonedaMon.obj X).1`. `yonedaMon` is a
-- plain `def` whose value is a structure literal with `obj M := yonedaMonObj M.X`. To close the
-- gap you must unfold `yonedaMon` and then reduce the projection. `yonedaMon` is semireducible,
-- so [instances] cannot do this.
--
-- The `Small` instance above is stated for the functor value `(yonedaMon.obj M).obj X`. The goals
-- that come out of `shrinkYonedaMon` are stated for the object presheaf `(yonedaMonObj M).obj X`.
-- The declaration itself makes both spellings appear, because it reads
-- `MonCat.shrinkFunctor (yonedaMon.obj X)` while `yonedaMon.map` produces terms typed at
-- `yonedaMonObj`.
--
-- fix: none found.
--   - `attribute [implicit_reducible] yonedaMon yonedaGrp` does not help. The check runs at
--     exactly [instances], so no mark at [implicit] can reach it.
--   - Restating both `Small` instances at `(yonedaMonObj M).obj X` leaves 10 errors, because
--     `MonCat.shrinkFunctor (yonedaMon.obj X)` then finds no instance at all.
--   - Declaring both spellings leaves 17 errors. Instance search picks one spelling per goal, so
--     the mismatch only moves.
--   - Defining `shrinkYonedaMon` from `yonedaMonObj X.X` instead of `yonedaMon.obj X`, with the
--     `Small` instances restated to match, leaves 18 errors. Most of them are new, of the form
--     `stuck at solving universe constraint`, because `yonedaMonObj` lands in `MonCat.{v}` while
--     `shrinkYonedaMon` must land in `MonCat.{w}`. So this is not the repair either.
--
-- Unlike `Mathlib/CategoryTheory/Bicategory/Yoneda.lean`, this file is not just a missing bump.
-- Removing the parent option and comparing errors with and without `instances false` looks like
-- it says otherwise, because both give 34. That test is void here: `parent ON, instances OFF`
-- also gives the same 34 errors with the same messages. All three broken configurations agree,
-- so the test says only that both options are needed together.
-- A `defeqAt` probe on `(yonedaMonObj M.X).obj Y =?= (yonedaMon.obj M).obj Y` gives
-- reducible false, instances false, implicit false, default true. The same holds for the two
-- sides wrapped in `Small.{w}`. So the comparison needs [default], and no bump to [implicit]
-- would help.
--
-- `Small` is a propositional class, so the rejection might be a bit harsh.
set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYonedaMon :
    Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} where
  obj X := MonCat.shrinkFunctor (yonedaMon.obj X)
  map f := MonCat.shrinkFunctorMap (yonedaMon.map f)

open MonObj

/-- The type `(shrinkYonedaMon.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`. -/
noncomputable def shrinkYonedaMonObjObjEquiv {M : Mon C} {Y : Cᵒᵖ} :
    (shrinkYonedaMon.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
    {M : Mon C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaMon.{w}.obj _).map g (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

lemma shrinkYonedaMonObjObjEquiv_symm_comp {M : Mon C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaMonObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaMon.obj _).map g.op (shrinkYonedaMonObjObjEquiv.symm f) :=
  (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm g.op f).symm

set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Mon C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaMon.map g).app _ (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (f ≫ g.hom) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYonedaGrp :
    Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w} where
  obj X := GrpCat.shrinkFunctor (yonedaGrp.obj X)
  map f := GrpCat.shrinkFunctorMap (yonedaGrp.map f)

/-- The type `(shrinkYonedaGrp.obj M).obj Y` is equivalent to `Y.unop ⟶ M.X`. -/
noncomputable def shrinkYonedaGrpObjObjEquiv {M : Grp C} {Y : Cᵒᵖ} :
    (shrinkYonedaGrp.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm
    {M : Grp C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaGrp.{w}.obj _).map g (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

lemma shrinkYonedaGrpObjObjEquiv_symm_comp {M : Grp C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaGrpObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaGrp.obj _).map g.op (shrinkYonedaGrpObjObjEquiv.symm f) :=
  (shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm g.op f).symm

set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Grp C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaGrp.map g).app _ (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (f ≫ g.hom.hom) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

end CategoryTheory
