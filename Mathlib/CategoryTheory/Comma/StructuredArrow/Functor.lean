/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Grothendieck

/-!
# Structured Arrow Categories as strict functor to Cat

Forming a structured arrow category `StructuredArrow d T` with `d : D` and `T : C ⥤ D` is strictly
functorial in `S`, inducing a functor `Dᵒᵖ ⥤ Cat`. This file constructs said functor and proves
that, in the dual case, we can precompose it with another functor `L : E ⥤ D` to obtain a category
equivalent to `Comma L T`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

/-- The structured arrow category `StructuredArrow d T` depends on the chosen domain `d : D` in a
functorial way, inducing a functor `Dᵒᵖ ⥤ Cat`. -/
@[simps]
def functor (T : C ⥤ D) : Dᵒᵖ ⥤ Cat where
  obj d := .of <| StructuredArrow d.unop T
  map f := (map f.unop).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp)
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp)

end StructuredArrow

namespace CostructuredArrow

/-- The costructured arrow category `CostructuredArrow T d` depends on the chosen codomain `d : D`
in a functorial way, inducing a functor `D ⥤ Cat`. -/
@[simps]
def functor (T : C ⥤ D) : D ⥤ Cat where
  obj d := .of <| CostructuredArrow T d
  map f := (CostructuredArrow.map f).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

variable {E : Type u₃} [Category.{v₃} E]
variable (L : C ⥤ D) (R : E ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor used to establish the equivalence `grothendieckPrecompFunctorEquivalence` between
the Grothendieck construction on `CostructuredArrow.functor` and the comma category. -/
@[simps]
def grothendieckPrecompFunctorToComma : Grothendieck (R ⋙ functor L) ⥤ Comma L R where
  obj P := ⟨P.fiber.left, P.base, P.fiber.hom⟩
  map f := ⟨f.fiber.left, f.base, by simp⟩

-- tl;dr: the fiber of `R ⋙ functor L` carries its own bundled category structure, and the goal
-- also names that category as `CostructuredArrow L (R.obj X)`. The two do not meet at
-- [instances].
--
-- This declaration carried `backward.isDefEq.respectTransparency.instances false` and the parent
-- `backward.isDefEq.respectTransparency false`. Both are removed. The four marks below replace
-- them.
--
-- Diagnosis. Traced with both options removed and no mark, all other options at their default
-- value, plus `trace.Meta.isDefEq.assign.checkTypes` and `trace.Meta.synthInstance`.
--
-- ❌ mvar type check, pinned at [instances]:
--      Category.{?u, max u₁ v₂} (CostructuredArrow L (R.obj X))
--        =?= Category.{v₁, max v₂ u₁} ↑((R ⋙ functor L).obj X)
--    assigned: `((R ⋙ functor L).obj X).str`, the bundled structure of the `Cat`-valued fiber.
--    To see the two carriers as one type you must unfold `functor` and `Functor.comp`. Neither
--    unfolds at [instances].
--
-- ✅ synthesis. It succeeds, but with a different value,
--    `instCategoryCostructuredArrow_1 L (R.obj X)`.
--
-- ❌ unify. The rejected value and the synthesized one are compared at the ambient transparency.
--    All 42 rejected blocks are this one metavariable.
--
-- The marks work only after the parent option is gone. The parent suppresses the [implicit] bump
-- that `isDefEqApp` gives to instance arguments, so the unify runs below the level the marks need.
-- This was measured on three other sites, `Monoidal/Closed/FunctorCategory/Basic.lean`,
-- `Sites/Plus.lean` and `Algebra/Category/Grp/Colimits.lean`. It was not re-measured here.
--
-- The four constants below are the ones `linter.tacticCheckInstances` named. Remove the parent
-- option first, then run the linter, then mark what it names.
set_option backward.defeqAttrib.useBackward true in
attribute [local implicit_reducible]
  Quiver.Hom
  Grothendieck.ι
  functor
  grothendieckPrecompFunctorToComma
in
/-- Fibers of `grothendieckPrecompFunctorToComma L R`, composed with `Comma.fst L R`, are isomorphic
to the projection `proj L (R.obj X)`. -/
@[simps!]
def ιCompGrothendieckPrecompFunctorToCommaCompFst (X : E) :
    Grothendieck.ι (R ⋙ functor L) X ⋙ grothendieckPrecompFunctorToComma L R ⋙ Comma.fst _ _ ≅
    proj L (R.obj X) :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun _ => by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor used to establish the equivalence `grothendieckPrecompFunctorEquivalence`
between the Grothendieck construction on `CostructuredArrow.functor` and the comma category. -/
@[simps]
def commaToGrothendieckPrecompFunctor : Comma L R ⥤ Grothendieck (R ⋙ functor L) where
  obj X := ⟨X.right, mk X.hom⟩
  map f := ⟨f.right, homMk f.left⟩
  map_id X := Grothendieck.ext _ _ rfl (by simp)
  map_comp f g := Grothendieck.ext _ _ rfl (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- For `L : C ⥤ D`, taking the Grothendieck construction of `CostructuredArrow.functor L`
precomposed with another functor `R : E ⥤ D` results in a category which is equivalent to
the comma category `Comma L R`. -/
@[simps]
def grothendieckPrecompFunctorEquivalence : Grothendieck (R ⋙ functor L) ≌ Comma L R where
  functor := grothendieckPrecompFunctorToComma _ _
  inverse := commaToGrothendieckPrecompFunctor _ _
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/-- The functor projecting out the domain of arrows from the Grothendieck construction on
costructured arrows. -/
@[simps!]
def grothendieckProj : Grothendieck (functor L) ⥤ C :=
  grothendieckPrecompFunctorToComma L (𝟭 _) ⋙ Comma.fst _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Fibers of `grothendieckProj L` are isomorphic to the projection `proj L X`. -/
@[simps!]
def ιCompGrothendieckProj (X : D) :
    Grothendieck.ι (functor L) X ⋙ grothendieckProj L ≅ proj L X :=
  ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) X

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Functors between costructured arrow categories induced by morphisms in the base category
composed with fibers of `grothendieckProj L` are isomorphic to the projection `proj L X`. -/
@[simps!]
def mapCompιCompGrothendieckProj {X Y : D} (f : X ⟶ Y) :
    CostructuredArrow.map f ⋙ Grothendieck.ι (functor L) Y ⋙ grothendieckProj L ≅ proj L X :=
  Functor.isoWhiskerLeft (CostructuredArrow.map f)
    (ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) Y)

/-- The functor `CostructuredArrow.pre` induces a natural transformation
`CostructuredArrow.functor (S ⋙ T) ⟶ CostructuredArrow.functor T` for `S : C ⥤ D` and
`T : D ⥤ E`. -/
@[simps]
def preFunctor {D : Type u₁} [Category.{v₁} D] (S : C ⥤ D) (T : D ⥤ E) :
    functor (S ⋙ T) ⟶ functor T where
  app e := (pre S T e).toCatHom

end CostructuredArrow

end CategoryTheory
