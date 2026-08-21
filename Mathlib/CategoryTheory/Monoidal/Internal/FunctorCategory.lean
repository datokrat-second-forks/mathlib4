/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# `Mon (C ⥤ D) ≌ C ⥤ Mon D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `monFunctorCategoryEquivalence : Mon (C ⥤ D) ≌ C ⥤ Mon D`

The intended application is that as `Ring ≌ Mon Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon Ab) X ≌ Mon (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj ComonObj

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace MonFunctorCategoryEquivalence

variable {C D}

/-- A monoid object in a functor category sends any object to a monoid object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [MonObj A] (X : C) : Mon D where
  X := A.obj X
  mon :=
  { one := η[A].app X
    mul := μ[A].app X
    one_mul := congr_app (one_mul A) X
    mul_one := congr_app (mul_one A) X
    mul_assoc := congr_app (mul_assoc A) X }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A monoid object in a functor category induces a functor to the category of monoid objects. -/
@[simps]
def functorObj (A : C ⥤ D) [MonObj A] : C ⥤ Mon D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isMonHom_hom :=
        { one_hom := by dsimp; rw [← η[A].naturality, tensorUnit_map]; dsimp; rw [Category.id_comp]
          mul_hom := by dsimp; rw [← μ[A].naturality, tensorObj_map] } }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a monoid object in a functor category
to a functor into the category of monoid objects.
-/
@[simps]
def functor : Mon (C ⥤ D) ⥤ C ⥤ Mon D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isMonHom_hom :=
        { one_hom := congr_app (IsMonHom.one_hom f.hom) X
          mul_hom := congr_app (IsMonHom.mul_hom f.hom) X } } }

set_option backward.defeqAttrib.useBackward true in
/-- A functor to the category of monoid objects can be translated as a monoid object
in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ Mon D) : Mon (C ⥤ D) where
  X := F ⋙ Mon.forget D
  mon :=
  { one := { app X := η[(F.obj X).X] }
    mul := { app X := μ[(F.obj X).X] } }

set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a functor into the category of monoid objects
to a monoid object in the functor category
-/
@[simps]
def inverse : (C ⥤ Mon D) ⥤ Mon (C ⥤ D) where
  obj := inverseObj
  map α := .mk'
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg Mon.Hom.hom (α.naturality f) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
def unitIso : 𝟭 (Mon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := .mk' { app := fun _ => 𝟙 _ }
    inv := .mk' { app := fun _ => 𝟙 _ } })

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Mon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

#print counitIso_hom_app_app_hom

end MonFunctorCategoryEquivalence

open MonFunctorCategoryEquivalence

-- This file had three `backward.isDefEq.respectTransparency.instances false` sites. Two are now
-- removed and one stays, on `CommMonFunctorCategoryEquivalence.functor`. Before the repair,
-- removing them one at a time gave 42, 8 and 20 errors.
--
-- Trace with `.instances false` removed and the other options kept:
--   ❌ mvar type check:
--     ❌ MonObj (X ⋙ Mon.forget D) =?= MonObj (inverseObj X).X
--     assigned: `(inverseObj X).mon`
--     ❌ synth ("the instance could not be synthesized directly")
--     unification would not succeed at [implicit]. It needs [default].
--
-- `inverseObj` is a plain `def` with `X := F ⋙ Mon.forget D`. The two sides name the same
-- functor. One side spells it directly, the other reads it back out of `inverseObj`. `defeqAt`
-- probes, columns [reducible] [instances] [implicit] [default]:
--   (inverseObj F).X =?= F ⋙ Mon.forget D                false false false true
--   MonObj ((inverseObj F).X) =?= MonObj (F ⋙ Mon.forget D)  false false false true
--
-- All 680 rejected assignments in this file have this shape, in the `Mon`, `Comon` and `CommMon`
-- copies of the construction.
--
-- Where the metavariable comes from. The only field that fails is
-- `Equivalence.functor_unitIso_comp`, and it fails inside its auto-param proof, not in its type.
-- Measured: replacing that one auto-param by `functor_unitIso_comp _ := by sorry` takes the
-- diagnostic blocks for this declaration from 12 to 0. So the field's type elaborates fine and
-- the tactic is what creates the metavariable. Two further probes agree that the type is not the
-- trigger: `example : 𝟭 (Mon (C ⥤ D)) ≅ functor ⋙ inverse := unitIso` and
-- `example (X) : X ⟶ (functor ⋙ inverse).obj X := unitIso.hom.app X` both elaborate with no
-- diagnostics at all.
--
-- The field reads (`Mathlib/CategoryTheory/Equivalence.lean`):
--   functor_unitIso_comp (X : C) :
--     dsimp% functor.map (unitIso.hom.app X) ≫ counitIso.hom.app (functor.obj X)
--       = 𝟙 (functor.obj X) := by cat_disch
-- Here `cat_disch` is `aesop_cat`. `categoryTheoryDischarger` only picks `grind` when
-- `mathlib.tactic.category.grind` is true, and that `set_option` is scoped to the rest of
-- `Mathlib/CategoryTheory/Category/Basic.lean`, so it does not reach this file.
--
-- The failing part is aesop's normalisation simp, not its rule search. `trace.aesop` shows the
-- safe rules apply `ext` twice, giving
--   ((functor.map (unitIso.hom.app X) ≫ counitIso.hom.app (functorObj X.X)).app x).hom
--     = ((𝟙 (functorObj X.X)).app x).hom
-- and the rejected assignments appear directly under the `<norm simp>` line that follows.
-- Reproduced by hand: `ext x` alone gives 0 rejected assignments, `ext x; simp` gives 4.
-- `intros` and `dsimp` are also clean on their own.
--
-- Which simp lemma fails. No single one does. `functorObj (A : C ⥤ D) [MonObj A] : C ⥤ Mon D`
-- carries an instance argument. The `@[simps]` lemma `inverseObj_X : (inverseObj F).X =
-- F ⋙ Mon.forget D` rewrites the carrier argument of a `functorObj` application. The instance
-- argument must then move from `MonObj ((inverseObj F).X)` to `MonObj (F ⋙ Mon.forget D)`. That
-- is the pair in the diagnostic, at the round trip object `inverseObj (functorObj X.X)`, that is
-- `X` sent through `functor` and back through `inverse`:
--   ?inst : MonObj (functorObj X.X ⋙ Mon.forget D) := (inverseObj (functorObj X.X)).mon
-- The goal spells the carrier as `functorObj X.X ⋙ Mon.forget D`. The candidate is typed at
-- `(inverseObj (functorObj X.X)).X`. Only unfolding `inverseObj` joins them.
--
-- `inverseObj_X` on its own is harmless. The smallest list that reproduces the rejection is
--   simp only [functor_obj, inverse_obj, functorObj_obj, inverseObj_X, NatTrans.comp_app]
-- after `intro X; ext x : 3`. It gives 4 rejected assignments. Removing any one of the five gives
-- 0. Running the same five lemmas as two `simp only` calls in a row also gives 0. So the rejection
-- needs one traversal that rewrites the carrier and re-applies `NatTrans.comp_app` above it.
--
-- A rejected assignment is not always an error. The repaired proof still prints 8 of them and
-- compiles with `.instances false` removed. Under `cat_disch` the damage is that `simp` stops at
--   𝟙 (X.X.obj x) ≫ 𝟙 ((functorObj (functorObj X.X ⋙ Mon.forget D)).obj x).X = 𝟙 (X.X.obj x)
-- With `.instances false` the same `simp` closes the goal and prints no rejection.
--
-- No mark can help. The diagnostic says the instance could not be synthesized, so there is no
-- second term for a fallback unify to reach. The only comparison that runs is the type check
-- pinned at exactly [instances], and the gap needs [default]. These declarations carry
-- `respectTransparency.types false`, not the parent option, so this is also not the bump case of
-- `Mathlib/CategoryTheory/Bicategory/Yoneda.lean`.
--
-- fix: write the auto-param out by hand with `aesop_cat?`, then append `exact Category.comp_id _`.
-- That one extra line is the whole repair. The `aesop_cat?` script on its own is not enough.
-- Errors on `monFunctorCategoryEquivalence`, with and without `.instances false`:
--   the `aesop_cat?` script as printed                 option on: 0    option off: 1
--   the same script plus `exact Category.comp_id _`    option on: 41   option off: 0
--
-- The option and the `exact` exclude each other. `Category.comp_id` is already in the second lemma
-- list. With the option it fires and closes the goal, so the extra `exact` reports `No goals to be
-- solved`. Without the option the same `Category.comp_id` does not fire, and simp stops at
--   𝟙 (X.X.obj x) ≫ 𝟙 ((functorObj (functorObj X.X ⋙ Mon.forget D)).obj x).X = 𝟙 (X.X.obj x)
-- `Category.comp_id` does not fire because `functorObj_obj` did not fire, earlier in the same
-- pass. `trace.Meta.Tactic.simp.rewrite` on `intro X; ext x : 3; simp` gives two runs that agree
-- for 7 steps. Step 8 is where they part:
--   option on:   functorObj_obj   (functorObj (functorObj X.X ⋙ Mon.forget D)).obj x
--                             ==> functorObjObj (functorObj X.X ⋙ Mon.forget D) x
--   option off:  the 4 rejected assignments above, and no rewrite
-- `functorObj_obj : (functorObj A).obj x = functorObjObj A x` carries `[MonObj A]`. At
-- `A := functorObj X.X ⋙ Mon.forget D` simp must fill that instance argument, and the only value
-- present in the term is `(inverseObj (functorObj X.X)).mon`. So the rewrite is dropped, and with
-- it the four steps that normalise the object of the second identity: `functorObjObj_X`,
-- `Functor.comp_obj`, `Mon.forget_obj`, and a second `functorObjObj_X`.
--
-- With the option on, `Category.comp_id` then fires on `𝟙 (X.X.obj x) ≫ 𝟙 (X.X.obj x)`, where the
-- two objects are already the same expression. It never joins two spellings. Without the option
-- the two objects stay different expressions and no match is possible. `defeqAt` probes, columns
-- [reducible] [instances] [implicit] [default]:
--   X.X.obj x =?= ((functorObj (functorObj X.X ⋙ Mon.forget D)).obj x).X   false false false true
--   MonObj (F ⋙ Mon.forget D) =?= MonObj (inverseObj F).X                  false false false true
-- Both objects are the same functor, spelled differently, and only [default] joins them. simp
-- matches below that level. `exact` elaborates at [default] and closes the goal. `rfl` fails.
--
-- Dropping `Functor.comp_obj`, `Mon.forget_obj` and `Category.comp_id` from the second list is
-- cosmetic. After `exact` closes the goal those three are unused simp arguments, and the linter
-- warns about each. Keeping them costs 3 warnings and no errors.
-- `intro X; ext x : 3; simp; exact Category.comp_id _` also compiles, with the same 4 rejections.
--
-- `CommMonFunctorCategoryEquivalence.functor` keeps the option. The same technique works on its
-- `naturality` field, with
--   naturality _ _ g := by
--     ext
--     exact congr_arg Mon.Hom.hom
--       (((monFunctorCategoryEquivalence C D).functor.map f.hom).naturality g)
-- but that only moves the failure. Its other auto-params, and those of the declarations after it
-- in the `CommMon` section, then fail in the same way. Repairing that section needs several more
-- hand-written proofs and is left undone.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.instances false in
/-- When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the monoid objects of `D`.
-/
@[simps]
def monFunctorCategoryEquivalence : Mon (C ⥤ D) ≌ C ⥤ Mon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := by
    intro X
    simp_all only [functor_obj, inverse_obj, inverseObj_X]
    ext x : 3
    -- simp_all only [functorObj_obj, functorObjObj_X, NatTrans.comp_app, Mon.comp_hom',
    --   functor_map_app_hom, inverseObj_X, unitIso_hom_app_hom_app, counitIso_hom_app_app_hom,
    --   NatTrans.id_app, Mon.id_hom']
    -- exact Category.comp_id _
    -- `aesop_cat?` prints the script below. It needs `.instances false`. The three extra lemmas
    -- are unused once `exact Category.comp_id _` closes the goal.
    simp_all only [functorObj_obj, functorObjObj_X, NatTrans.comp_app, Mon.comp_hom',
      Functor.comp_obj, Mon.forget_obj, functor_map_app_hom, inverseObj_X,
      unitIso_hom_app_hom_app, counitIso_hom_app_app_hom, Category.comp_id, NatTrans.id_app,
      Mon.id_hom']

namespace ComonFunctorCategoryEquivalence

variable {C D}

/-- A comonoid object in a functor category sends any object to a comonoid object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [ComonObj A] (X : C) : Comon D where
  X := A.obj X
  comon :=
  { counit := ε[A].app X
    comul := Δ[A].app X
    counit_comul := congr_app (counit_comul A) X
    comul_counit := congr_app (comul_counit A) X
    comul_assoc := congr_app (comul_assoc A) X }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
A comonoid object in a functor category induces a functor to the category of comonoid objects.
-/
@[simps]
def functorObj (A : (C ⥤ D)) [ComonObj A] : C ⥤ Comon D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isComonHom_hom.hom_counit := by
        dsimp; rw [ε[A].naturality, tensorUnit_map]; dsimp; rw [Category.comp_id]
      isComonHom_hom.hom_comul := by dsimp; rw [Δ[A].naturality, tensorObj_map] }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a comonoid object in a functor category
to a functor into the category of comonoid objects.
-/
@[simps]
def functor : Comon (C ⥤ D) ⥤ C ⥤ Comon D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isComonHom_hom.hom_counit := congr_app (IsComonHom.hom_counit f.hom) X
      isComonHom_hom.hom_comul := congr_app (IsComonHom.hom_comul f.hom) X } }

set_option backward.defeqAttrib.useBackward true in
/-- A functor to the category of comonoid objects can be translated as a comonoid object
in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ Comon D) : Comon (C ⥤ D) where
  X := F ⋙ Comon.forget D
  comon :=
  { counit := { app X := ε[(F.obj X).X] }
    comul := { app X := Δ[(F.obj X).X] } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/-- Functor translating a functor into the category of comonoid objects
to a comonoid object in the functor category
-/
@[simps]
private def inverse : (C ⥤ Comon D) ⥤ Comon (C ⥤ D) where
  obj := inverseObj
  map α :=
    { hom :=
      { app := fun X => (α.app X).hom
        naturality := fun _ _ f => congr_arg Comon.Hom.hom (α.naturality f) }
      isComonHom_hom.hom_counit := by ext x; dsimp; rw [IsComonHom.hom_counit (α.app x).hom]
      isComonHom_hom.hom_comul := by ext x; dsimp; rw [IsComonHom.hom_comul (α.app x).hom] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/-- The unit for the equivalence `Comon (C ⥤ D) ≌ C ⥤ Comon D`.
-/
@[simps!]
private def unitIso : 𝟭 (Comon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
    { hom := .mk' { app := fun _ => 𝟙 _ }
      inv := .mk' { app := fun _ => 𝟙 _ } })

set_option backward.isDefEq.respectTransparency false in
-- probably this was originally also intended to be a private def
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The counit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Comon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

end ComonFunctorCategoryEquivalence

open ComonFunctorCategoryEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- When `D` is a monoidal category,
comonoid objects in `C ⥤ D` are the same thing
as functors from `C` into the comonoid objects of `D`.
-/
@[simps]
def comonFunctorCategoryEquivalence : Comon (C ⥤ D) ≌ C ⥤ Comon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := by
    intro X
    simp_all only [ComonFunctorCategoryEquivalence.functor_obj,
      ComonFunctorCategoryEquivalence.inverse_obj,
      ComonFunctorCategoryEquivalence.inverseObj_X]
    ext x : 3
    simp_all only [ComonFunctorCategoryEquivalence.functorObj_obj,
      ComonFunctorCategoryEquivalence.functorObjObj_X,
      ComonFunctorCategoryEquivalence.functor_map_app_hom,
      ComonFunctorCategoryEquivalence.inverseObj_X,
      ComonFunctorCategoryEquivalence.unitIso_hom_app_hom_app,
      ComonFunctorCategoryEquivalence.counitIso_hom_app_app_hom,
      NatTrans.comp_app, Comon.comp_hom', NatTrans.id_app, Comon.id_hom']
    exact Category.comp_id _

variable [BraidedCategory.{v₂} D]

namespace CommMonFunctorCategoryEquivalence

variable {C D}

set_option backward.isDefEq.respectTransparency.instances false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor translating a commutative monoid object in a functor category
to a functor into the category of commutative monoid objects.
-/
@[simps!]
def functor : CommMon (C ⥤ D) ⥤ C ⥤ CommMon D where
  obj A :=
    { obj X :=
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon).obj X with
          comm := { mul_comm := congr_app (IsCommMonObj.mul_comm A.X) X } }
      map f :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.obj A.toMon).map f) }
  map f :=
    { app X :=
        CommMon.homMk (((monFunctorCategoryEquivalence C D).functor.map f.hom).app X) }

/-- Functor translating a functor into the category of commutative monoid objects
to a commutative monoid object in the functor category
-/
@[simps!]
def inverse : (C ⥤ CommMon D) ⥤ CommMon (C ⥤ D) where
  obj F :=
    { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon.forget₂Mon D) with
      comm := { mul_comm := by ext X; exact IsCommMonObj.mul_comm (F.obj X).X } }
  map α :=
    CommMon.homMk ((monFunctorCategoryEquivalence C D).inverse.map (Functor.whiskerRight α _))

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit for the equivalence `CommMon (C ⥤ D) ≌ C ⥤ CommMon D`.
-/
@[simps!]
def unitIso : 𝟭 (CommMon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A => CommMon.mkIso (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit for the equivalence `CommMon (C ⥤ D) ≌ C ⥤ CommMon D`.
-/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon D) :=
  NatIso.ofComponents (fun A ↦ NatIso.ofComponents (fun X ↦ Iso.refl _))

end CommMonFunctorCategoryEquivalence

open CommMonFunctorCategoryEquivalence

/-- When `D` is a braided monoidal category,
commutative monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the commutative monoid objects of `D`.
-/
@[simps]
def commMonFunctorCategoryEquivalence : CommMon (C ⥤ D) ≌ C ⥤ CommMon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal
