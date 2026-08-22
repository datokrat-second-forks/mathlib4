/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# The category of small categories has all small limits.

An object in the limit consists of a family of objects,
which are carried to one another by the functors in the diagram.
A morphism between two such objects is a family of morphisms between the corresponding objects,
which are carried to one another by the action on morphisms of the functors in the diagram.

## Future work
Can the indexing category live in a lower universe?
-/

@[expose] public section


noncomputable section

universe v u

open CategoryTheory Limits ConcreteCategory

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

namespace Cat

namespace HasLimits

instance categoryObjects {F : J ⥤ Cat.{u, u}} {j} :
    SmallCategory ((F ⋙ Cat.objects.{u, u}).obj j) :=
  (F.obj j).str

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition:
the diagram whose limit gives the morphism space between two objects of the limit category. -/
@[simps]
def homDiagram {F : J ⥤ Cat.{v, v}} (X Y : limit (F ⋙ Cat.objects.{v, v})) :
    J ⥤ Type v where
  obj j := limit.π (F ⋙ Cat.objects) j X ⟶ limit.π (F ⋙ Cat.objects) j Y
  map f := ↾fun g ↦ by
    refine eqToHom ?_ ≫ (F.map f).toFunctor.map g ≫ eqToHom ?_
    · exact (congr_hom (limit.w (F ⋙ Cat.objects) f) X).symm
    · exact congr_hom (limit.w (F ⋙ Cat.objects) f) Y
  map_id X := by
    ext f
    let : Category (objects.obj (F.obj X)) := (inferInstance : Category (F.obj X))
    simp [Functor.congr_hom congr($(F.map_id X).toFunctor) f]
  map_comp {_ _ Z} f g := by
    ext h
    let : Category (objects.obj (F.obj Z)) := (inferInstance : Category (F.obj Z))
    simp [Functor.congr_hom congr($(F.map_comp f g).toFunctor) h, eqToHom_map]

set_option backward.isDefEq.respectTransparency false in
@[simps]
instance (F : J ⥤ Cat.{v, v}) : Category (limit (F ⋙ Cat.objects) :) where
  Hom X Y := limit (homDiagram X Y)
  id X := Types.Limit.mk.{v, v} (homDiagram X X) (fun _ => 𝟙 _) fun j j' f => by simp
  comp {X Y Z} f g := Types.Limit.mk.{v, v} (homDiagram X Z)
    (fun j => limit.π (homDiagram X Y) j f ≫ limit.π (homDiagram Y Z) j g) fun j j' h => by
    simp [-homDiagram_obj, ← limit.w_apply (homDiagram X Y) h f,
      ← limit.w_apply (homDiagram Y Z) h g]
  id_comp _ := by
    apply Types.limit_ext.{v, v}
    simp [-homDiagram_obj]
  comp_id _ := by
    apply Types.limit_ext.{v, v}
    simp [-homDiagram_obj]
  assoc _ _ _ := by
    apply Types.limit_ext.{v, v}
    simp [-homDiagram_obj]

/-- Auxiliary definition: the limit category. -/
@[simps]
def limitConeX (F : J ⥤ Cat.{v, v}) : Cat.{v, v} where α := limit (F ⋙ Cat.objects)

set_option backward.isDefEq.respectTransparency.types false in
attribute [-simp] homDiagram_obj in
/-- Auxiliary definition: the cone over the limit category. -/
@[simps]
def limitCone (F : J ⥤ Cat.{v, v}) : Cone F where
  pt := limitConeX F
  π :=
    { app := fun j => Functor.toCatHom
        { obj := limit.π (F ⋙ Cat.objects) j
          map := fun f => limit.π (homDiagram _ _) j f }
      naturality := fun _ _ f => Cat.Hom.ext <|
        CategoryTheory.Functor.ext (fun X => (congr_hom (limit.w (F ⋙ Cat.objects) f) X).symm)
          fun X Y h => (congr_hom (limit.w (homDiagram X Y) f) h).symm }

set_option backward.defeqAttrib.useBackward true in
attribute [-simp] homDiagram_obj Functor.comp_obj in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition: the universal morphism to the proposed limit cone. -/
@[simps! toFunctor]
def limitConeLift (F : J ⥤ Cat.{v, v}) (s : Cone F) : s.pt ⟶ limitConeX F :=
  Functor.toCatHom <| {
    obj :=
      limit.lift (F ⋙ Cat.objects)
        { pt := s.pt
          π :=
            { app := fun j => ↾(s.π.app j).toFunctor.obj
              naturality := fun _ _ f => objects.congr_map (s.π.naturality f) } }
    map f := by
      fapply Types.Limit.mk.{v, v}
      · intro j
        refine eqToHom ?_ ≫ (s.π.app j).toFunctor.map f ≫ eqToHom ?_ <;> simp
      · intro j j' h
        dsimp [Functor.comp_obj, homDiagram_obj]
        simp only [Functor.map_comp, eqToHom_map, ← Functor.comp_map, Category.assoc, eqToHom_trans,
          eqToHom_trans_assoc]
        have := congr($((s.π.naturality h).symm).toFunctor)
        dsimp at this
        rw [Functor.id_comp] at this
        rw [Functor.congr_hom this f]
        simp }

set_option backward.isDefEq.respectTransparency.types false in
theorem limit_π_homDiagram_eqToHom {F : J ⥤ Cat.{v, v}} (X Y : limit (F ⋙ Cat.objects.{v, v}))
    (j : J) (h : X = Y) :
    limit.π (homDiagram X Y) j (eqToHom h) =
      eqToHom (ConcreteCategory.congr_arg (limit.π (F ⋙ Cat.objects.{v, v}) j) h) := by
  subst h
  simp [-homDiagram_obj]

-- tl;dr: this site is a real `[instances]` casualty, not collateral of the parent option. Both
-- options stay. The site is not repaired, but marks get most of the way.
--
-- Diagnosis. Traced with the child option removed and the parent kept, every other option at its
-- default value, plus `trace.Meta.isDefEq`, `trace.Meta.isDefEq.printTransparency`,
-- `trace.Meta.isDefEq.assign`, `trace.Meta.isDefEq.assign.checkTypes` and
-- `trace.Meta.synthInstance`. 150 assignments are rejected. 38 of them are instance
-- metavariables, in two groups.
--
-- Group 1. `Cat.of` bundles the category structure, and the bundled copy is offered where the
-- plain instance is wanted:
--
--   ❌ type check, pinned at [instances]
--        Category.{?u, v} (limit (F ⋙ objects))  =?=  Category.{v, v} ↑(limitConeX F)
--   ✅ synthesis
--        goal    Category.{v, v} (limit (F ⋙ objects))
--        result  instCategoryLimitCompObjects F
--   ❌ unify, at the ambient [reducible]
--        (limitConeX F).str  =?=  instCategoryLimitCompObjects F
--
-- Group 2. The constant cone functor is not unfolded on the offered side:
--
--   ❌ type check, pinned at [instances]
--        Category.{?u, v} ↑s.pt  =?=  Category.{v, v} ↑(((Functor.const J).obj s.pt).obj j)
--   ✅ synthesis
--        goal    Category.{v, v} ↑s.pt
--        result  s.pt.str
--   ❌ unify, at the ambient [reducible]
--        (((Functor.const J).obj s.pt).obj j).str  =?=  s.pt.str
--
-- At [reducible] no mark can help, because `implicit_reducible` does not unfold there. The parent
-- option puts the ambient there. It suppresses the [implicit] bump that `isDefEqApp` gives to
-- instance arguments. So remove the parent first, then judge the marks.
--
-- With the parent removed the same rejections are still there, 20 of them, but now at [implicit].
-- Group 1 keeps its type check and its synthesis, and only the unify moves:
--
--   ❌ unify, at the ambient [implicit]
--        (limitConeX F).str  =?=  instCategoryLimitCompObjects F
--        (limitConeX F).2    =?=  instCategoryLimitCompObjects F
--
-- A third metavariable also appears, on `CategoryStruct` rather than `Category`:
--
--   ❌ type check, pinned at [instances]
--        CategoryStruct.{?u, v} (objects.obj (F.obj j))
--          =?= CategoryStruct.{v, v} ((F ⋙ objects).obj j)
--   ✅ synthesis
--        goal    CategoryStruct.{v, v} (objects.obj (F.obj j))
--        result  (F.obj j).instCategoryObjObjects.toCategoryStruct
--   ❌ unify, at the ambient [implicit]
--        categoryObjects.1  =?=  (F.obj j).instCategoryObjObjects.toCategoryStruct
--
-- That is why this site is not collateral. The check has real work to do with the parent gone.
-- Comparing compiler output alone does not show this. With the parent removed, the output with
-- `instances false` and without it is byte-identical, because the declaration already fails for
-- its own reason and elaboration never reaches the difference. Only the trace separates them.
--
-- Marks measured, with the parent removed. This would work, but we can't make `Quiver.Hom`
-- implicit-reducible:
--
-- attribute [local implicit_reducible]
--   CategoryTheory.Cat.HasLimits.limitConeX
--   CategoryTheory.Cat.objects
--   CategoryTheory.Cat.HasLimits.homDiagram
--   CategoryTheory.Cat.HasLimits.limitCone
--   CategoryTheory.Cat.HasLimits.limitConeLift
--   Quiver.Hom
--    -- unnecessary if Cat.objects was implicit-reducible from at its definition already
--   instCategoryObjObjects._aux_5 -- This is an example of tacticCheckInstances not helping.
-- in
--
-- The problematic error solved by these marks is the `refine_2` branch of `uniq`. There `simp`
-- reports `limit_π_homDiagram_eqToHom` as an unused argument, so that lemma never fires, but the
-- origin of the issue is further above.
--
-- The marks are not applied below. With the parent in place they are inert, because the unify runs
-- at [reducible]. They are recorded here for the next person who tries the parent-first recipe.
--
-- The parent `backward.isDefEq.respectTransparency false` is the reason here as well. It holds the
-- fallback unify at [reducible], where no mark reaches it. If the parent could be removed, the
-- `.instances` opt-out would go with it. The parent has not been removed here.
--
-- The opt-out below is `attribute [local lax_instance_defeq] Category CategoryStruct`, which turns
-- the `.instances` check off for those two classes in place of the whole
-- `backward.isDefEq.respectTransparency.instances false` option. The rejected assignments name
-- both classes, so both are listed. Errors and warnings are the same either way. This is a
-- narrower opt-out, not a repair.
set_option linter.tacticCheckInstances true
attribute [local lax_instance_defeq] CategoryTheory.Category CategoryTheory.CategoryStruct in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition: the proposed cone is a limit cone. -/
def limitConeIsLimit (F : J ⥤ Cat.{v, v}) : IsLimit (limitCone F) where
  lift := limitConeLift F
  fac s j := Cat.Hom.ext <| CategoryTheory.Functor.ext (by intro; simp [← comp_apply])
    fun X Y f => by
      dsimp [limitConeLift]
      exact Types.Limit.π_mk.{v, v} _ _ _ _
  uniq s m w := by
    symm
    ext1
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      apply Types.limit_ext.{v, v}
      intro j
      simp [← comp_apply, ← w j]
    · intro X Y f
      have (j : _) := Functor.congr_hom congr($((w j).symm).toFunctor) f
      simp [this, -homDiagram_obj, limit_π_homDiagram_eqToHom]

end HasLimits

/-- The category of small categories has all small limits. -/
instance : HasLimits Cat.{v, v} where
  has_limits_of_shape _ :=
    { has_limit := fun F => ⟨⟨⟨HasLimits.limitCone F, HasLimits.limitConeIsLimit F⟩⟩⟩ }

instance : PreservesLimits Cat.objects.{v, v} where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (HasLimits.limitConeIsLimit F)
          (Limits.IsLimit.ofIsoLimit (limit.isLimit (F ⋙ Cat.objects))
            (Cone.ext (by rfl) (by cat_disch))) }

end Cat

end CategoryTheory
