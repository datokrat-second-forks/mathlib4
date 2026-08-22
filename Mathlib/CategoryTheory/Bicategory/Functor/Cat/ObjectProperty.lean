/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Properties of objects in target categories of a pseudofunctor to `Cat`

Given `F : Pseudofunctor B Cat`, we introduce a type `F.ObjectProperty`
which consists of properties `P` of objects for all categories `F.obj X` for `X : B`.
The typeclass `P.IsClosedUnderMapObj` expresses that this property
is preserved by the application of the functors `F.map`: this allows
to define a sub-pseudofunctor `P.fullsubcategory : Pseudofunctor B Cat`.

## TODO (@joelriou)
* Given a Grothendieck topology `J` on a category `C`, define
  a type class `Pseudofunctor.ObjectProperty.IsLocal P J` extending
  `IsClosedUnderMapObj` saying that if an object locally satisfies
  the property, then it satisfies the property. Assuming this, show that
  `P.fullsubcategory` is a stack if the original pseudofunctor was.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : Pseudofunctor B Cat.{v', u'})

/-- If `F : Pseudofunctor B Cat`, this is the data of a property of
objects in all categories `F.obj X` for `X : B`. -/
protected structure ObjectProperty where
  /-- A property of objects in the category `F.obj X` for all `X : B`. -/
  prop (X : B) : CategoryTheory.ObjectProperty (F.obj X)

namespace ObjectProperty

variable {F} (P : F.ObjectProperty)

/-- Given `F : Pseudofunctor B Cat`, `P : F.ObjectProperty` and `X : B`, this is
the full subcategory of `F.obj X` consisting of the objects satisfying the
property `P`. -/
abbrev Obj (X : B) := (P.prop X).FullSubcategory

/-- If `P` is a property of objects for a pseudofunctor `F` to `Cat`,
this is the condition that `P` is preserved by the application of the functors `F.map`. -/
class IsClosedUnderMapObj (P : F.ObjectProperty) : Prop where
  map_obj (P) {X Y : B} {M : F.obj X} (hM : P.prop X M) (f : X ⟶ Y) :
    P.prop Y ((F.map f).toFunctor.obj M)

export IsClosedUnderMapObj (map_obj)

/-- If `P` is a property of objects for a pseudofunctor `F` to `Cat`, this is the
condition that all `P.prop : ObjectProperty (F.obj X)` for `X : B` are closed
under isomorphisms. -/
class IsClosedUnderIsomorphisms : Prop where
  isClosedUnderIsomorphisms (X : B) : (P.prop X).IsClosedUnderIsomorphisms

attribute [instance] IsClosedUnderIsomorphisms.isClosedUnderIsomorphisms

section

variable [P.IsClosedUnderMapObj]

/-- Given a property `P` of objects for `F : Pseudofunctor B Cat` and a morphism `f : X ⟶ Y`
in `B`, this is the functor `P.Obj X ⥤ P.Obj Y` that is induced by `F.map f`. -/
@[simps!]
def map {X Y : B} (f : X ⟶ Y) :
    P.Obj X ⥤ P.Obj Y :=
  (P.prop Y).lift (ObjectProperty.ι _ ⋙ (F.map f).toFunctor)
    (fun M ↦ P.map_obj M.2 f)

/-- Given a property `P` of objects for `F : Pseudofunctor B Cat` and
a `2`-morphism in `B`, this is the induced natural transformation between
the induced functors on the fullsubcategories of objects satisfying `P`. -/
@[simps!]
def map₂ {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    P.map f ⟶ P.map g :=
  ((P.prop Y).fullyFaithfulι.whiskeringRight _).preimage
    (Functor.whiskerLeft (P.prop X).ι (F.map₂ α).toNatTrans)

/-- Auxiliary definition for `fullsubcategory`. -/
def mapId (X : B) :
    P.map (𝟙 X) ≅ 𝟭 _ :=
  ((P.prop X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapId X)))

@[simp]
lemma mapId_hom_app {X : B} (M : P.Obj X) :
  (P.mapId X).hom.app M = ObjectProperty.homMk
    ((F.mapId X).hom.toNatTrans.app M.obj) := rfl

@[simp]
lemma mapId_inv_app {X : B} (M : P.Obj X) :
  (P.mapId X).inv.app M = ObjectProperty.homMk
    ((F.mapId X).inv.toNatTrans.app M.obj) := rfl

/-- Auxiliary definition for `fullsubcategory`. -/
def mapComp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.map (f ≫ g) ≅ P.map f ⋙ P.map g :=
  ((P.prop Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapComp f g)))

@[simp]
lemma mapComp_hom_app {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X) :
    (P.mapComp f g).hom.app M = ObjectProperty.homMk
      ((F.mapComp f g).hom.toNatTrans.app M.obj) := rfl

@[simp]
lemma mapComp_inv_app {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X) :
    (P.mapComp f g).inv.app M = ObjectProperty.homMk
      ((F.mapComp f g).inv.toNatTrans.app M.obj) := rfl

/-- Given a property of objects `P` for a pseudofunctor from `B` to `Cat`, this is
the induced pseudofunctor which sends `X : B` to the full subcategory of `F.obj X`
consisting of objects satisfying `P`. -/
@[simps]
def fullsubcategory : Pseudofunctor B Cat where
  obj X := Cat.of (P.Obj X)
  map f := Cat.Hom.ofFunctor (P.map f)
  map₂ α := Cat.Hom₂.ofNatTrans (P.map₂ α)
  mapId X := Cat.Hom.isoMk (P.mapId X)
  mapComp f g := Cat.Hom.isoMk (P.mapComp f g)

-- tl;dr: both options are needed together, and a mark does not replace either. Removing every
-- instance-metavariable rejection is not enough to repair this site.
--
-- Without the options `aesop` cannot fill the default fields `naturality_naturality`,
-- `naturality_id` and `naturality_comp` of `Pseudofunctor.StrongTrans`.
--
-- The desync, traced with both options removed. 24 rejections, all the same:
--
--   ❌ type check, pinned at [instances]
--        Category.{?u, max u' v'} (Cat.of (P.Obj a) ⟶ F.obj b)
--          =?= Category.{max u' v', max u' v'} (P.fullsubcategory.obj a ⟶ F.obj b)
--   ✅ synthesis
--        goal    Category.{max u' v', max u' v'} (Cat.of (P.Obj a) ⟶ F.obj b)
--        result  Cat.Hom.instCategory
--   ❌ unify, at the ambient [implicit]
--        { toQuiver := Cat.Hom.instQuiver, id := …, comp := …, … }  =?=  Cat.Hom.instCategory
--
-- `P.fullsubcategory.obj a` is `Cat.of (P.Obj a)`, but the composite spelling does not reduce.
--
-- A mark closes that gap completely and still does not repair the declaration. With
--     attribute [local implicit_reducible] ObjectProperty.fullsubcategory
-- and both options removed, the trace holds **zero** instance-metavariable rejections, and the
-- same 10 errors remain. `aesop` still cannot close the naturality goals.
--
-- Measured, every combination:
--
--   mark   `instances false`   parent   result
--   off    off                 off      10 errors, 24 rejections
--   on     off                 off      10 errors,  0 rejections
--   on     off                 on       10 errors
--   off    on                  off      10 errors
--   on     on                  off      10 errors
--   off    on                  on       compiles
--   on     on                  on       compiles
--
-- So the child option is needed given the parent, the parent is needed given the child, and the
-- mark is neither necessary nor sufficient. What the parent supplies here is not the instance
-- desync. It is the old behavior of `isDefEqArgs`, which compares instance arguments under
-- `withInferTypeConfig`, that is at `.default` (`Lean/Meta/ExprDefEq.lean:480-488`). `aesop` needs
-- that to close the goals, and no reducibility attribute reproduces a blanket `.default`.
--
-- The mark is not applied below. It is recorded because it isolates the instance desync cleanly,
-- which is useful when judging whether the `[instances]` check is what breaks this site. It is
-- not.
--
-- The parent `backward.isDefEq.respectTransparency false` is the reason here as well. The matrix
-- above shows it: with the parent gone the mark clears every instance rejection, and the same 10
-- errors stay, so the check is not what breaks this site. If the parent could be removed, the
-- `.instances` opt-out would go with it. The parent has not been removed here.
--
-- The opt-out below is `attribute [local lax_instance_defeq] Category`, which turns the
-- `.instances` check off for one class in place of the whole
-- `backward.isDefEq.respectTransparency.instances false` option. It gives the same result. This is
-- a narrower opt-out, not a repair.
attribute [local lax_instance_defeq] CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of `P.fullsubcategory` in `F`. -/
@[simps]
def ι : StrongTrans P.fullsubcategory F where
  app X := Cat.Hom.ofFunctor (P.prop (X := X)).ι
  naturality f := Iso.refl _

end

end ObjectProperty

end Pseudofunctor

end CategoryTheory
