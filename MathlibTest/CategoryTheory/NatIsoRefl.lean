import Mathlib.CategoryTheory.NatIso

open CategoryTheory

set_option backward.isDefEq.respectTransparency true

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {K : Type u₄} [Category.{v₄} K]
  (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)

-- Infer both maps and all four law proofs from the expected endpoints.
example : F ≅ F := by
  with_reducible_and_instances exact NatIso.refl

example : F ⋙ 𝟭 D ≅ F := by
  fail_if_success with_reducible_and_instances exact Iso.refl F
  with_reducible_and_instances exact NatIso.refl

example : 𝟭 C ⋙ F ≅ F := by
  with_reducible_and_instances exact NatIso.refl

example : (F ⋙ G) ⋙ H ≅ F ⋙ (G ⋙ H) := by
  with_reducible_and_instances exact NatIso.refl

-- The automatic equality proof must retain its requested type for simp and dsimp.
example (X : C) : (NatIso.refl : F ⋙ 𝟭 D ≅ F).hom.app X = 𝟙 (F.obj X) := by
  simp

example (X : C) : (NatIso.refl : 𝟭 C ⋙ F ≅ F).inv.app X = 𝟙 (F.obj X) := by
  dsimp

example (X : C) :
    (NatIso.refl : (F ⋙ G) ⋙ H ≅ F ⋙ (G ⋙ H)).hom.app X = 𝟙 (H.obj (G.obj (F.obj X))) := by
  simp

-- Reduce components before simp changes the identity map arguments.
example (X : C) :
    (NatIso.refl : 𝟭 C ≅ 𝟭 C ⋙ 𝟭 C).hom.app X ≫
      (NatIso.refl : 𝟭 C ⋙ 𝟭 C ≅ 𝟭 C).hom.app X = 𝟙 X := by
  simp

-- A supplied map equality need not hold definitionally.
section

variable {obj : C → D}
  {map₁ map₂ : ∀ {X Y : C}, (X ⟶ Y) → (obj X ⟶ obj Y)}
  (map_id₁ : ∀ X, map₁ (𝟙 X) = 𝟙 (obj X))
  (map_comp₁ : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    map₁ (f ≫ g) = map₁ f ≫ map₁ g)
  (map_id₂ : ∀ X, map₂ (𝟙 X) = 𝟙 (obj X))
  (map_comp₂ : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    map₂ (f ≫ g) = map₂ f ≫ map₂ g)
  (h : @map₁ = @map₂)

example :
    CategoryTheory.Functor.mk obj map₁ map_id₁ (@map_comp₁) ≅
      CategoryTheory.Functor.mk obj map₂ map_id₂ (@map_comp₂) := by
  fail_if_success exact NatIso.refl
  with_reducible_and_instances exact NatIso.refl h

example (X : C) :
    (NatIso.refl h : CategoryTheory.Functor.mk obj map₁ map_id₁ (@map_comp₁) ≅
      CategoryTheory.Functor.mk obj map₂ map_id₂ (@map_comp₂)).hom.app X = 𝟙 (obj X) := by
  dsimp

end
