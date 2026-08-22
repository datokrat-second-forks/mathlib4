/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj b`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).toFunctor.obj f ⟶ f'`

`Grothendieck.functor` makes the Grothendieck construction into a functor from the functor category
`C ⥤ Cat` to the over category `Over C` in the category of categories.

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consist again of `β : b ⟶ b'` and `φ : f ⟶ (G.map (op β)).obj f'`.

## Notable constructions

- `Grothendieck F` is the Grothendieck construction.
- Elements of `Grothendieck F` whose base is `c : C` can be transported along `f : c ⟶ d` using
  `transport`.
- A natural transformation `α : F ⟶ G` induces `map α : Grothendieck F ⥤ Grothendieck G`.
- The Grothendieck construction and `map` together form a functor (`functor`) from the functor
  category `E ⥤ Cat` to the over category `Over E`.
- A functor `G : D ⥤ C` induces `pre F G : Grothendieck (G ⋙ F) ⥤ Grothendieck F`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of a functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/

@[expose] public section


universe w u v u₁ v₁ u₂ v₂

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]
variable (F : C ⥤ Cat.{v₂, u₂})

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

namespace Grothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (Functor.ofCatHom (F.map base)).obj X.fiber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).toFunctor.obj X.fiber ⟶ Y.fiber

@[ext (iff := false)]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

/-- The identity morphism in the Grothendieck category.
-/
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by simp)

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp f g := Grothendieck.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 ((Cat.Hom.toNatIso <| eqToIso (F.map_id Y.base)) ≪≫
        (eqToIso Cat.Hom.id_toFunctor)) f.fiber]
      simp
  id_comp f := by ext <;> simp [comp, id]
  assoc f g h := by
    ext
    · simp [comp]
    · simp [comp, ← NatIso.naturality_2 (Cat.Hom.toNatIso (eqToIso (F.map_comp g.base h.base)) ≪≫
        (eqToIso (Cat.Hom.comp_toFunctor _ _))) f.fiber]

@[simp]
theorem id_base (X : Grothendieck F) :
    Hom.base (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
theorem id_fiber (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by simp) :=
  rfl

@[simp]
theorem comp_base {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_fiber {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) =
      eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber :=
  rfl

theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  simp

@[simp]
theorem base_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Grothendieck.base h) := by subst h; rfl

@[simp]
theorem fiber_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; simp) := by subst h; rfl

lemma eqToHom_eq {X Y : Grothendieck F} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) } := by
  subst hF
  rfl

section Transport

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element of `Grothendieck F` to a `d`-based element.
-/
@[simps]
def transport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : Grothendieck F :=
  ⟨c, (F.map t).toFunctor.obj x.fiber⟩

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element `x` of `Grothendieck F` to a `d`-based element `x.transport t`.

`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identity on fibers.
-/
@[simps]
def toTransport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : x ⟶ x.transport t :=
  ⟨t, 𝟙 _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Construct an isomorphism in a Grothendieck construction from isomorphisms in its base and fiber.
-/
@[simps]
def isoMk {X Y : Grothendieck F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).toFunctor.obj X.fiber ≅ Y.fiber) :
    X ≅ Y where
  hom := ⟨e₁.hom, e₂.hom⟩
  inv := ⟨e₁.inv, (F.map e₁.inv).toFunctor.map e₂.inv ≫ eqToHom (by
    rw [← Cat.Hom.comp_obj, ← F.map_comp,e₁.hom_inv_id,F.map_id,Cat.Hom.id_obj])⟩
  hom_inv_id := Grothendieck.ext _ _ (by simp) (by simp)
  inv_hom_id := Grothendieck.ext _ _ (by simp) (by
    have := Functor.congr_hom congr($((F.mapIso e₁).inv_hom_id).toFunctor) e₂.inv
    simp_all)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
If `F : C ⥤ Cat` and `x : Grothendieck F`, then every `C`-isomorphism `α : x.base ≅ c` induces
an isomorphism between `x` and its transport along `α`
-/
@[simps!]
def transportIso (x : Grothendieck F) {c : C} (α : x.base ≅ c) :
    x.transport α.hom ≅ x := (isoMk α (Iso.refl _)).symm

end Transport
section

variable (F)

/-- The forgetful functor from `Grothendieck F` to the source category. -/
@[simps!]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map f := f.1

end

section

variable {G : C ⥤ Cat}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The Grothendieck construction is functorial: a natural transformation `α : F ⟶ G` induces
a functor `Grothendieck.map : Grothendieck F ⥤ Grothendieck G`.
-/
@[simps!]
def map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where
  obj X :=
  { base := X.base
    fiber := (α.app X.base).toFunctor.obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber }
  -- map_id X := by simp only [id_base, id_fiber, eqToHom_map, eqToHom_trans]; rfl
  map_comp {X Y Z} f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_fiber, map_comp, ← Cat.Hom.comp_map,
      Functor.congr_hom congr($(α.naturality g.base).toFunctor) f.fiber]
    simp


theorem map_obj {α : F ⟶ G} (X : Grothendieck F) :
    (Grothendieck.map α).obj X = ⟨X.base, (α.app X.base).toFunctor.obj X.fiber⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem map_map {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y} :
    (Grothendieck.map α).map f =
    ⟨f.base, (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber⟩ := by
    apply Grothendieck.ext _ _ (by simp) (by simp)

/-- The functor `Grothendieck.map α : Grothendieck F ⥤ Grothendieck G` lies over `C`. -/
theorem functor_comp_forget {α : F ⟶ G} :
    Grothendieck.map α ⋙ Grothendieck.forget G = Grothendieck.forget F := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem map_id_eq : map (𝟙 F) = Functor.id (Grothendieck <| F) := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `mapIdIso` to `map_id_eq` whenever we can. -/
def mapIdIso : (map (𝟙 F)).toCatHom ≅ 𝟙 (Cat.of <| Grothendieck <| F) :=
  eqToIso congr(($map_id_eq).toCatHom)

variable {H : C ⥤ Cat}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem map_comp_eq (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, map_obj_fiber, NatTrans.comp_app, Cat.Hom.comp_toFunctor,
      comp_obj, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Functor.comp_map, eqToHom_refl, map_comp,
      eqToHom_map, eqToHom_trans_assoc, Category.comp_id, Category.id_comp]

/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `map_comp_iso` to `map_comp_eq` whenever we can. -/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
def compAsSmallFunctorEquivalenceInverse :
    Grothendieck F ⥤ Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) where
  obj X := ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
def compAsSmallFunctorEquivalenceFunctor :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ⥤ Grothendieck F where
  obj X := ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id _ := by apply Grothendieck.ext <;> simp
  map_comp _ _ := by apply Grothendieck.ext <;> simp [down_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Taking the Grothendieck construction on `F ⋙ asSmallFunctor`, where
`asSmallFunctor : Cat ⥤ Cat` is the functor which turns each category into a small category of a
(potentially) larger universe, is equivalent to the Grothendieck construction on `F` itself. -/
@[simps]
def compAsSmallFunctorEquivalence :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ≌ Grothendieck F where
  functor := compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := Iso.refl _
  unitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F} in
/-- Mapping a Grothendieck construction along the whiskering of any natural transformation
`α : F ⟶ G` with the functor `asSmallFunctor : Cat ⥤ Cat` is naturally isomorphic to conjugating
`map α` with the equivalence between `Grothendieck (F ⋙ asSmallFunctor)` and `Grothendieck F`. -/
def mapWhiskerRightAsSmallFunctor (α : F ⟶ G) :
    map (whiskerRight α Cat.asSmallFunctor.{w}) ≅
    (compAsSmallFunctorEquivalence F).functor ⋙ map α ⋙
      (compAsSmallFunctorEquivalence G).inverse :=
  NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun f => by
      fapply Grothendieck.ext
      · simp [compAsSmallFunctorEquivalenceInverse]
      · simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse,
        comp_obj, compAsSmallFunctorEquivalenceInverse_obj_base, map_obj_base,
        compAsSmallFunctorEquivalenceFunctor_obj_base, Cat.asSmallFunctor_obj, Cat.of_α,
        Iso.refl_hom, Functor.comp_map, comp_base, id_base,
        compAsSmallFunctorEquivalenceInverse_map_base, map_map_base,
        compAsSmallFunctorEquivalenceFunctor_map_base, Cat.asSmallFunctor_map, toCatHom_toFunctor,
        map_obj_fiber, whiskerRight_app, AsSmall.down_obj, AsSmall.up_obj_down,
        compAsSmallFunctorEquivalenceInverse_obj_fiber,
        compAsSmallFunctorEquivalenceFunctor_obj_fiber, comp_fiber, map_map_fiber, AsSmall.down_map,
        down_comp, eqToHom_down, AsSmall.up_map_down, map_comp, eqToHom_map, id_fiber,
        Category.assoc, eqToHom_trans_assoc, compAsSmallFunctorEquivalenceInverse_map_fiber,
        compAsSmallFunctorEquivalenceFunctor_map_fiber, eqToHom_comp_iff, comp_eqToHom_iff]
        simp only [conj_eqToHom_iff_heq']
        rw [G.map_id]
        simp)

end

/-- The Grothendieck construction as a functor from the functor category `E ⥤ Cat` to the
over category `Over E`. -/
def functor {E : Cat.{v, u}} : (E ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E where
  obj F := Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F).toCatHom
  map {_ _} α := Over.homMk (X := E) (Grothendieck.map α).toCatHom
    congr($(Grothendieck.functor_comp_forget).toCatHom)
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp [Grothendieck.map_comp_eq α β]
    rfl

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1⟩

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨f.2⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps!]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨f⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    simp
    rfl

section Pre

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction induces a functor
`Grothendieck (G ⋙ F) ⥤ Grothendieck F`. -/
@[simps, implicit_reducible]
def pre (G : D ⥤ C) : Grothendieck (G ⋙ F) ⥤ Grothendieck F where
  obj X := ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

@[simp]
theorem pre_id : pre F (𝟭 C) = 𝟭 _ := rfl

-- tl;dr: the parent `backward.isDefEq.respectTransparency false` is the reason. The opt-out from
-- the `.instances` check is collateral of it, not a casualty of the check. Remove the parent and
-- the check has nothing real left to reject, so the `.instances` opt-out goes too. The parent has
-- not been removed here. See the last paragraph.
--
-- This declaration opts out of the `.instances` check. The opt-out is now
-- `attribute [local lax_instance_defeq] Category`, which turns the check off for one class in
-- place of the whole `backward.isDefEq.respectTransparency.instances false` option. Every rejected
-- assignment here has a `Category` metavariable, so the narrow form covers the site. It stays,
-- with its parent. The site is not repaired. Do not count it as an independent `[instances]`
-- failure.
--
-- The parent came first. Upstream `preNatIso` carried no options at all. The parent
-- `backward.isDefEq.respectTransparency false` was added by an earlier adaptation. The child
-- `instances false` was added on top of it, in `ea8987667f`.
--
-- Diagnosis. Traced with the child option removed and the parent kept, every other option at its
-- default value, plus `trace.Meta.isDefEq.assign`, `trace.Meta.isDefEq.assign.checkTypes`,
-- `trace.Meta.synthInstance` and `trace.Meta.isDefEq.printTransparency`. 69 assignments are
-- rejected. Six of them are instance metavariables.
--
-- All six are the same metavariable, `Category.{v₂, u₂} ↑(F.obj (H.obj Y.base))`. The value
-- offered for it is always a `Cat`-bundled `.str` that names the same object of `C` by a longer
-- route. Route 1 of `checkTypesAndAssign` runs three steps on each one:
--
--   ❌ type check, pinned at [instances]
--        Category.{?u, u₂} ↑(F.obj (H.obj Y.base))
--          =?= Category.{v₂, u₂} ↑((H ⋙ F).obj Y.base)
--   ✅ synthesis
--        goal    Category.{v₂, u₂} ↑(F.obj (H.obj Y.base))
--        result  (F.obj (H.obj Y.base)).str
--   ❌ unify, at the ambient [reducible]
--        ((H ⋙ F).obj Y.base).str  =?=  (F.obj (H.obj Y.base)).str
--
-- The other five rejections differ only in the spelling of the offered value. Each one unifies
-- against the same synthesized `(F.obj (H.obj Y.base)).str`, at [reducible]:
--
--   ❌ (F.obj ((pre F H).obj ((map (whiskerRight α.hom F)).obj Y)).base).str
--   ❌ (F.obj ({ base := G.obj Y.base, fiber := Y.fiber }.transport (α.app Y.base).hom).base).str
--
-- No mark can help at [reducible]. `implicit_reducible` does not unfold there. The parent option
-- is the cause. It suppresses the [implicit] bump that `isDefEqApp` gives to instance arguments,
-- so the ambient stays at the caller's level.
--
-- Removing the parent option clears all six, with the marks and without them. Measured on
-- `trace.Meta.isDefEq.assign` nodes, with both options removed, one class-typed rejection is left:
--
--   ❌ type check, pinned at [instances]
--        Category.{?u, u} C  =?=  Category.{v₁, u₁} D
--   ✅ synthesis
--        goal    Category.{v, u} C
--        result  inst✝¹
--   ❌ unify, at the ambient [default]
--        inst✝  =?=  inst✝¹
--
-- That one is ordinary instance search trying the wrong ambient instance. Search then succeeds.
-- It is not evidence about the `[instances]` check. `C` and `D` are different variables, so the
-- type check fails at every transparency. With `instances false` the check runs at `.implicit`
-- instead and rejects the same assignment. Only the fallback disappears.
--
-- So with the parent removed, `instances false` changes nothing here. That is the verdict for this
-- site. The child option is doing no work of its own. It exists only because the parent lowers the
-- ambient to [reducible], where the six real rejections cannot be repaired.
--
-- `Grothendieck.pre`, `Functor.comp` and `whiskerRight` need no mark. They already carry the
-- attribute.
--
-- The proof still fails. The remaining failure is a different mechanism. Two goals stay open, and
-- both print with identical sides:
--
--   ⊢ eqToHom ⋯ ≫ eqToHom ⋯ ≫ (F.map (α.hom.app Y.base)).toFunctor.map f.fiber =
--       eqToHom ⋯ ≫ eqToHom ⋯ ≫ (F.map (α.hom.app Y.base)).toFunctor.map f.fiber
--
-- `pp.explicit true` shows why. The goal states its own hom-type at one spelling and carries the
-- `Category` instance at the other:
--
--   carrier   @Bundled.α Category.{v₂, u₂} (F.obj (H.obj Y.base))
--   instance  @Bundled.α Category.{v₂, u₂}
--               (F.obj ((map (whiskerRight α.hom F) ⋙ pre F H).obj Y).base)
--
-- That is the same spelling pair as the six rejections above. Here it is built into the goal
-- instead of rejected during assignment. `rfl` at [default] does not close it, and neither does
-- `simp`. This desync is what the parent option is holding up. It is not caused by the
-- `[instances]` check.
--
-- Neither option can be dropped, with or without the marks. Measured, all four combinations:
--
--   `instances false`   parent   marks    result
--   on                  on       on       compiles
--   off                 on       on       2 unsolved goals
--   on                  off      on       2 unsolved goals
--   on                  off      off      2 unsolved goals
--   off                 off      on       2 unsolved goals
--
-- Every failing combination leaves the same goal. The parent option is load-bearing in its own
-- right, for the desync shown above. The child option is load-bearing only while the parent is
-- present. The marks replace neither.
--
-- The three marks below change nothing that was measured. They are kept because they are harmless
-- and they make the site easy to experiment on.
--
-- Order of removal, measured. With the parent kept, dropping the `.instances` opt-out gives 2
-- errors, so the opt-out cannot go on its own. The parent must go first. Attempts to remove the
-- parent with marks have not succeeded. With both options gone and the three marks kept, 2 errors
-- remain, and `linter.tacticCheckInstances true` reports a `simp` desync on
-- `(F.obj ((map (whiskerRight α.hom F) ⋙ pre F H).obj Y✝).base).str` against
-- `(F.obj (H.obj Y✝.base)).str`. Adding a fourth mark on `Grothendieck.pre` makes it worse, at 4
-- errors. So the site stays open, and the open question is the parent option, not the check.
attribute [local lax_instance_defeq] CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local implicit_reducible]
  Grothendieck.transport
  Grothendieck.transportIso
  Grothendieck.map
in
/--
A natural isomorphism between functors `G ≅ H` induces a natural isomorphism between the canonical
morphism `pre F G` and `pre F H`, up to composition with
`Grothendieck (G ⋙ F) ⥤ Grothendieck (H ⋙ F)`.
-/
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F G ≅ map (whiskerRight α.hom F) ⋙ (pre F H) :=
  NatIso.ofComponents
    (fun X => (transportIso ⟨G.obj X.base, X.fiber⟩ (α.app X.base)).symm)
    (fun f => by
      fapply Grothendieck.ext <;> simp)

/--
Given an equivalence of categories `G`, `preInv _ G` is the (weak) inverse of the `pre _ G.functor`.
-/
def preInv (G : D ≌ C) : Grothendieck F ⥤ Grothendieck (G.functor ⋙ F) :=
  map (whiskerRight G.counitInv F) ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse

variable {F} in
lemma pre_comp_map (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) :
    pre F G ⋙ map α = map (whiskerLeft G α) ⋙ pre H G := rfl

variable {F} in
lemma pre_comp_map_assoc (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : Type*} [Category* E]
    (K : Grothendieck H ⥤ E) : pre F G ⋙ map α ⋙ K = map (whiskerLeft G α) ⋙ pre H G ⋙ K := rfl

variable {E : Type*} [Category* E] in
@[simp]
lemma pre_comp (G : D ⥤ C) (H : E ⥤ D) : pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G := rfl

/--
Let `G` be an equivalence of categories. The functor induced via `pre` by `G.functor ⋙ G.inverse`
is naturally isomorphic to the functor induced via `map` by a whiskered version of `G`'s inverse
unit.
-/
protected def preUnitIso (G : D ≌ C) :
    map (whiskerRight G.unitInv _) ≅ pre (G.functor ⋙ F) (G.functor ⋙ G.inverse) :=
  preNatIso _ G.unitIso.symm |>.symm

-- Same issue as `preNatIso` above. See the note there.
attribute [local lax_instance_defeq] CategoryTheory.Category in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local implicit_reducible]
  Grothendieck.transport
  Grothendieck.transportIso
  Grothendieck.map
in
/--
Given a functor `F : C ⥤ Cat` and an equivalence of categories `G : D ≌ C`, the functor
`pre F G.functor` is an equivalence between `Grothendieck (G.functor ⋙ F)` and `Grothendieck F`.
-/
def preEquivalence (G : D ≌ C) : Grothendieck (G.functor ⋙ F) ≌ Grothendieck F where
  functor := pre F G.functor
  inverse := preInv F G
  unitIso := by
    refine (eqToIso ?_)
      ≪≫ (Grothendieck.preUnitIso F G |> isoWhiskerLeft (map _))
      ≪≫ (pre_comp_map_assoc G.functor _ _ |> Eq.symm |> eqToIso)
    calc
      _ = map (𝟙 _) := map_id_eq.symm
      _ = map _ := ?_
      _ = map _ ⋙ map _ := map_comp_eq _ _
    congr; ext X
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, Functor.id_obj,
      Functor.map_id, NatTrans.comp_app, NatTrans.id_app, whiskerLeft_app, whiskerRight_app,
      Equivalence.counitInv_functor_comp]
  counitIso := preNatIso F G.counitIso.symm |>.symm
  functor_unitIso_comp := by
    intro X
    simp only [preInv, Grothendieck.preUnitIso, pre_id,
      Iso.trans_hom, eqToIso.hom, eqToHom_app, eqToHom_refl, isoWhiskerLeft_hom, NatTrans.comp_app]
    fapply Grothendieck.ext <;> simp [preNatIso, transportIso]

variable {F} in
/--
Let `F, F' : C ⥤ Cat` be functor, `G : D ≌ C` an equivalence and `α : F ⟶ F'` a natural
transformation.

Left-whiskering `α` by `G` and then taking the Grothendieck construction is, up to isomorphism,
the same as taking the Grothendieck construction of `α` and using the equivalences `pre F G`
and `pre F' G` to match the expected type:

```
Grothendieck (G.functor ⋙ F) ≌ Grothendieck F ⥤ Grothendieck F' ≌ Grothendieck (G.functor ⋙ F')
```
-/
def mapWhiskerLeftIsoConjPreMap {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F') :
    map (whiskerLeft G.functor α) ≅
      (preEquivalence F G).functor ⋙ map α ⋙ (preEquivalence F' G).inverse :=
  (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (preEquivalence F' G).unitIso

end Pre

section FunctorFrom

variable {E : Type*} [Category* E]

set_option backward.isDefEq.respectTransparency.types false in
variable (F) in
/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its Grothendieck
construction. -/
@[simps obj map]
def ι (c : C) : F.obj c ⥤ Grothendieck F where
  obj d := ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
    simp only [eqToHom_comp_iff, Category.assoc, eqToHom_trans_assoc]
    apply Functor.congr_hom congr($(F.map_id _).toFunctor).symm

instance faithful_ι (c : C) : (ι F c).Faithful where
  map_injective f := by
    injection f with _ f
    rwa [cancel_epi] at f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
@[simps]
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ (F.map f).toFunctor ⋙ ι F Y where
  app d := ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'),
  fib c ⟶ (F.map f).toFunctor ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct a functor from `Grothendieck F` to another category `E` by providing a family of
functors on the fibers of `Grothendieck F`, a family of natural transformations on morphisms in the
base of `Grothendieck F` and coherence data for this family of natural transformations. -/
@[simps]
def functorFrom : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

set_option backward.defeqAttrib.useBackward true in
/-- `Grothendieck.ι F c` composed with `Grothendieck.functorFrom` is isomorphic a functor on a fiber
on `F` supplied as the first argument to `Grothendieck.functorFrom`. -/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

end FunctorFrom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The fiber inclusion `ι F c` composed with `map α` is isomorphic to `α.app c ⋙ ι F' c`. -/
@[simps!]
def ιCompMap {F' : C ⥤ Cat} (α : F ⟶ F') (c : C) : ι F c ⋙ map α ≅ (α.app c).toFunctor ⋙ ι F' c :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by simp [map])

end Grothendieck

end CategoryTheory
