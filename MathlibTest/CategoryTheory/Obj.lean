import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Tactic.CategoryTheory.Obj

namespace ObjPercentTest

open CategoryTheory CategoryTheory.Functor MonoidalCategory
open CategoryTheory.Localization

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

section
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (F : C ⥤ D) (G : D ⥤ E)

def identityExample : F ⋙ 𝟭 D ≅ F := by
  with_reducible_and_instances exact obj% Iso.refl

example (X : C) : (identityExample F).hom.app X = 𝟙 (F.obj X) := by
  simp [identityExample]

example (X : C) : (obj% (Iso.refl _) : 𝟭 C ⋙ F ≅ F).inv.app X = 𝟙 (F.obj X) := by
  dsimp

example : F ⋙ 𝟭 D ≅ F := obj% (Iso.refl F)

def transformationExample : 𝟭 C ⋙ F ⟶ F := by
  with_reducible_and_instances exact obj% (𝟙 F)

example (X : C) : (transformationExample F).app X = 𝟙 (F.obj X) := by
  simp [transformationExample]

example (H : D ⥤ E) : (𝟭 C ⋙ F) ⋙ H ≅ F ⋙ H := by
  with_reducible_and_instances exact obj% Iso.refl

-- Keep categorical identities intact when the component morphisms are structures.
def doubleOppositeExample : 𝟭 (Cᵒᵖᵒᵖ) ≅ unopUnop C ⋙ opOp C := obj% Iso.refl

example (X : Cᵒᵖᵒᵖ) : (doubleOppositeExample (C := C)).hom.app X = 𝟙 X := by
  simp [doubleOppositeExample]

-- The wrapper does not invent a map equality for arbitrary functors.
example (_F' : C ⥤ D) : True := by
  fail_if_success have : F ≅ _F' := obj% (Iso.refl F)
  trivial
end

section
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Monoidal]
  (F : D ⥤ E) (G : C ⥤ E) [G.Monoidal] [W.ContainsIdentities] [Lifting L W G F]

def localizationExample :
    (((whiskeringLeft₂ E).obj L).obj L).obj (curriedTensorPost F) ≅ curriedTensorPost G :=
  obj% ((postcompose₂.obj F).mapIso (Functor.curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F))

example (X Y : C) :
    ((localizationExample L W F G).hom.app X).app Y =
      F.map (Functor.LaxMonoidal.μ L X Y) ≫ (Lifting.iso L W G F).hom.app (X ⊗ Y) := by
  simp [localizationExample]

example : localizationExample L W F G =
    ((postcompose₂.obj F).mapIso (Functor.curriedTensorPreIsoPost L) ≪≫
      curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)) := by
  rfl

-- The original expression can also be provided through a named definition.
def namedSource :
    (((whiskeringLeft₂ E).obj L).obj L).obj (curriedTensorPost F) ≅ curriedTensorPost G :=
  (postcompose₂.obj F).mapIso (Functor.curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

def wrappedSource :
    (((whiskeringLeft₂ E).obj L).obj L).obj (curriedTensorPost F) ≅ curriedTensorPost G :=
  obj% (namedSource L W F G)

example (X Y : C) :
    ((wrappedSource L W F G).hom.app X).app Y =
      F.map (Functor.LaxMonoidal.μ L X Y) ≫ (Lifting.iso L W G F).hom.app (X ⊗ Y) := by
  simp [wrappedSource]
end

end ObjPercentTest
