/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
public import Mathlib.CategoryTheory.Limits.Final

meta import Lean.PostprocessTraces

/-!
# Inferring Filteredness from Filteredness of Costructured Arrow Categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8

-/

open Lean.PostprocessTraces

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits CategoryTheory.Functor

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

/-
We have a `simp; exact` combination.

1. `simp` makes the type of the category instance in `colim` mismatched with the type, at least
  looked at at instance transparency.
2. `exact`'s unification. Implicit and explicit args are unified before instance-implicit ones, so
  `C` (:= CostructuredArrow ..) and `colim` get unified before the `Category` instances. In the
  process of unifying `colim`, the `Category`
  instance mvar gets assigned, too, to the "bad" instance. The mvar isn't marked instance-typed;
  that only happens during instance search. So the assignment goes through, and we inherit the
  mismatch from `colimit`.
3. Finally, we synthesize the instance arguments of the lemma, including HasColimitsOfShape.
  (Synthesis by type runs for every instance-implicit argument, even those already assigned by
  unification; there, the synthesized instance is only cross-checked against the assignment, at
  default transparency.) We try
  to apply `Types.hasColimitsOfShape` which has the category instance as an instance-implicit arg,
  which becomes an instance-typed mvar.
  Therefore, we're required to reproduce the mismatch, but the mvar check prevents us from doing so.

* Same pattern (rewritten type index paired with an instance typed at the old spelling):
  `Mathlib/FieldTheory/Galois/Profinite.lean`, `Mathlib/CategoryTheory/Abelian/Subobject.lean`.
  Contrast `Mathlib/Algebra/Lie/BaseChange.lean`, where the unifier's own unfolding
  manufactures the mismatch.

`Category` is data-valued, so a Prop-exemption would not apply here.

Possible solutions:
* Make `Cat.of`/`Bundled.of` instance-reducible, so `↑(Cat.of C) =?= C` holds at `.instances`.
* Teach `simp` to re-synthesize (or re-type) dependent instance arguments whose type index it
  rewrote.
* Re-synthesize the `Category` instance after the rejected assignment
  (`instCategoryCostructuredArrow` would be found).
* Avoid the `Cat.of_α` simp rewrite that desyncs the shape carrier from its category instance.
-/

section
variable (L : A ⥤ T) (R : B ⥤ T) (b : B)

-- At the rewritten spelling, correctly-typed instances are also synthesizable.
/-- info: instCategoryCostructuredArrow_1 L (R.obj b) -/
#guard_msgs in
#synth Category (CostructuredArrow L (R.obj b))

/-- info: Types.hasColimitsOfShape -/
#guard_msgs in
#synth HasColimitsOfShape (CostructuredArrow L (R.obj b)) (Type u₁)

-- The rejected and the synthesized `Category` instances are defeq at `.implicit`, but only
-- with the `Cat.of`/`Bundled.of` lever.
attribute [local implicit_reducible] Cat.of Bundled.of in
example : (Cat.of (CostructuredArrow L (R.obj b))).str =
    (inferInstance : Category (CostructuredArrow L (R.obj b))) := by
  with_implicit apply_rfl

end

-- After `simp`, `colim` uses category type `CostructuredArrow ..`, but the instance's type is
-- `Category ↑(Cat.of (CostructuredArrow ..))`.
/--
trace: A : Type u₁
inst✝⁵ : SmallCategory A
B : Type u₁
inst✝⁴ : SmallCategory B
T : Type u₁
inst✝³ : SmallCategory T
L : @Functor A inst✝⁵ T inst✝³
R : @Functor B inst✝⁴ T inst✝³
inst✝² : @IsFiltered B inst✝⁴
inst✝¹ : @Final B inst✝⁴ T inst✝³ R
inst✝ :
  ∀ (b : B),
    @IsFiltered (@CostructuredArrow A inst✝⁵ T inst✝³ L (@obj B inst✝⁴ T inst✝³ R b))
      (@instCategoryCostructuredArrow_1 A inst✝⁵ T inst✝³ L (@obj B inst✝⁴ T inst✝³ R b))
J : Type u₁
x✝¹ : SmallCategory J
x✝ : @FinCategory J x✝¹
F : @Functor J x✝¹ (@Functor A inst✝⁵ (Type u₁) types) (@category A inst✝⁵ (Type u₁) types)
b : B
⊢ @PreservesLimitsOfShape
    (@Functor (@CostructuredArrow A inst✝⁵ T inst✝³ L (@obj B inst✝⁴ T inst✝³ R b))
      (@obj B inst✝⁴ Cat Cat.category
          (@comp B inst✝⁴ T inst✝³ Cat Cat.category R (@CostructuredArrow.functor A inst✝⁵ T inst✝³ L)) b).str
      (Type u₁) types)
    (@category
      (@Bundled.α Category.{u₁, u₁}
        (@obj B inst✝⁴ Cat Cat.category
          (@comp B inst✝⁴ T inst✝³ Cat Cat.category R (@CostructuredArrow.functor A inst✝⁵ T inst✝³ L)) b))
      (@obj B inst✝⁴ Cat Cat.category
          (@comp B inst✝⁴ T inst✝³ Cat Cat.category R (@CostructuredArrow.functor A inst✝⁵ T inst✝³ L)) b).str
      (Type u₁) types)
    (Type u₁) types J x✝¹
    (@colim (@CostructuredArrow A inst✝⁵ T inst✝³ L (@obj B inst✝⁴ T inst✝³ R b))
      (@Cat.of (@CostructuredArrow A inst✝⁵ T inst✝³ L (@obj B inst✝⁴ T inst✝³ R b))
          (@instCategoryCostructuredArrow_1 A inst✝⁵ T inst✝³ L (@obj B inst✝⁴ T inst✝³ R b))).str
      (Type u₁) types ⋯)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option linter.unusedTactic false in
set_option linter.style.setOption false in
set_option backward.isDefEq.instanceTypes false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
example (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    (set_option pp.explicit true in trace_state)
    exact filtered_colim_preservesFiniteLimits
  sorry

private meta partial def maxDepth (depth : Nat) : TracePostprocessor := fun trees =>
  let rec truncateTree (t : TraceTree) (depth : Nat) : TraceTree :=
    match t with
    | .leaf msg => TraceTree.leaf msg
    | .node data msg children wrap =>
      match depth with
      | 0 => .node data m!"{msg} (truncated)" #[] wrap
      | depth' + 1 => .node data msg (children.map (truncateTree · depth')) wrap
  return trees.map (truncateTree · depth)


-- `exact` unification: Everything of interest happens inside `colim =?= colim`.
/--
error: failed to synthesize instance of type class
  HasColimitsOfShape (CostructuredArrow L (R.obj b)) (Type u₁)
---
trace: [Meta.isDefEq] ✅️ [default] PreservesLimitsOfShape J colim =?= PreservesLimitsOfShape J colim
---
trace: [Meta.isDefEq] ✅️ [default] PreservesLimitsOfShape J colim =?= PreservesLimitsOfShape ?m.71 colim
  [Meta.isDefEq] ✅️ [default] Type u₁ =?= ?m.78
    [Meta.isDefEq] Type u₁ [nonassignable] =?= ?m.78 [assignable]
    [Meta.isDefEq] ✅️ [default] Type ?u.114 =?= Type (u₁ + 1)
  [Meta.isDefEq] ✅️ [default] types =?= ?m.79
    [Meta.isDefEq] types [nonassignable] =?= ?m.79 [assignable]
    [Meta.isDefEq] ✅️ [default] Category.{?u.117, u₁ + 1} (Type u₁) =?= Category.{u₁, u₁ + 1} (Type u₁)
      [Meta.isDefEq] ✅️ [default] Type u₁ =?= Type u₁ (truncated)
  [Meta.isDefEq] ✅️ [default] J =?= ?m.71
    [Meta.isDefEq] J [nonassignable] =?= ?m.71 [assignable]
    [Meta.isDefEq] ✅️ [default] Type ?u.116 =?= Type u₁
  [Meta.isDefEq] ✅️ [default] x✝¹ =?= ?m.73
    [Meta.isDefEq] x✝¹ [nonassignable] =?= ?m.73 [assignable]
    [Meta.isDefEq] ✅️ [default] SmallCategory J =?= SmallCategory J
      [Meta.isDefEq] ✅️ [default] Category.{u₁, u₁} J =?= Category.{u₁, u₁} J (truncated)
  [Meta.isDefEq] ✅️ [default] colim =?= colim
    [Meta.isDefEq] ✅️ [default] CostructuredArrow L (R.obj b) =?= ?m.72
      [Meta.isDefEq] CostructuredArrow L (R.obj b) [nonassignable] =?= ?m.72 [assignable] (truncated)
      [Meta.isDefEq] ✅️ [default] Type ?u.115 =?= Type u₁ (truncated)
    [Meta.isDefEq] ✅️ [default] (Cat.of (CostructuredArrow L (R.obj b))).str =?= ?m.74
      [Meta.isDefEq] (Cat.of (CostructuredArrow L (R.obj b))).str [nonassignable] =?= ?m.74 [assignable] (truncated)
      [Meta.isDefEq] ✅️ [default] Category.{?u.118, u₁}
            (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b))) (truncated)
    [Meta.isDefEq] ✅️ [default] Types.hasColimitsOfShape =?= ?m.85
      [Meta.isDefEq] Types.hasColimitsOfShape [nonassignable] =?= ?m.85 [assignable] (truncated)
      [Meta.isDefEq] ✅️ [default] HasColimitsOfShape (CostructuredArrow L (R.obj b))
            (Type u₁) =?= HasColimitsOfShape (↑((R ⋙ CostructuredArrow.functor L).obj b)) (Type u₁) (truncated)
    [Meta.isDefEq] ✅️ [default] Type u₁ =?= Type u₁
    [Meta.isDefEq] ✅️ [default] types =?= types
  [Meta.isDefEq] ✅️ [default] CostructuredArrow L (R.obj b) ⥤ Type u₁ =?= CostructuredArrow L (R.obj b) ⥤ Type u₁
    [Meta.isDefEq] ✅️ [default] CostructuredArrow L (R.obj b) =?= CostructuredArrow L (R.obj b)
    [Meta.isDefEq] ✅️ [default] Type u₁ =?= Type u₁
    [Meta.isDefEq] ✅️ [default] ((R ⋙ CostructuredArrow.functor L).obj
            b).str =?= (Cat.of (CostructuredArrow L (R.obj b))).str
    [Meta.isDefEq] ✅️ [default] types =?= types
  [Meta.isDefEq] ✅️ [default] category =?= category
    [Meta.isDefEq] ✅️ [default] ↑((R ⋙ CostructuredArrow.functor L).obj b) =?= CostructuredArrow L (R.obj b)
    [Meta.isDefEq] ✅️ [default] ((R ⋙ CostructuredArrow.functor L).obj
            b).str =?= (Cat.of (CostructuredArrow L (R.obj b))).str
    [Meta.isDefEq] ✅️ [default] Type u₁ =?= Type u₁
    [Meta.isDefEq] ✅️ [default] types =?= types
-/
#guard_msgs in
postprocess_traces
  maxDepth 3
  >=> filterSubtrees (fun x => (ofClass `Meta.isDefEq x) <&&> (containsString "[default] CategoryTheory.Limits.PreservesLimitsOfShape" x))
in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
example (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    set_option trace.Meta.isDefEq true in
    set_option trace.Meta.isDefEq.printTransparency true in
    set_option trace.Meta.synthInstance true in
    exact filtered_colim_preservesFiniteLimits
  refine lim.map ((colimitIsoColimitGrothendieck L F.flip).hom ≫
    (inv (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R'))) ≫
    (colimitLimitIso (R' ⋙ CostructuredArrow.grothendieckProj L ⋙ F.flip).flip).inv ≫
    colim.map ?_ ≫
    colimit.pre _ R' ≫
    (colimitIsoColimitGrothendieck L (limit F)).inv
  exact (limitCompWhiskeringLeftIsoCompLimit F (R' ⋙ CostructuredArrow.grothendieckProj L)).hom

-- During `exact`'s unification phase, the following happens:
-- 1. The explicit `colimit` arguments are unified before anything else that is of interest to us
--    While unifying `colimit`, the
--    mvars for the category type and instance are inherited from the `colimit` term.
--    `exact` doesn't make mvars instance-typed.
-- 2. Instance-implicit args are synthesized, including `HasColimitsOfShape`. Its arguments involve
--    the mismatch of category type and instance, but this time, an instance-typed mvar denies the
--    assignment.
set_option linter.style.longLine false in
/--
error: failed to synthesize instance of type class
  HasColimitsOfShape (CostructuredArrow L (R.obj b)) (Type u₁)
---
trace: [Meta.isDefEq] ✅️ [default] PreservesLimitsOfShape J colim =?= PreservesLimitsOfShape ?m.60 colim
  [Meta.isDefEq] ✅️ [default] colim =?= colim
    [Meta.isDefEq] ✅️ [default] (Cat.of (CostructuredArrow L (R.obj b))).str =?= ?m.63
      [Meta.isDefEq.assign.checkTypes] ✅️ (?m.63 : Category.{?u.107, u₁}
            (CostructuredArrow L
              (R.obj
                b))) := ((Cat.of
              (CostructuredArrow L (R.obj b))).str : Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b))))
        [Meta.isDefEq] ✅️ [default] Category.{?u.107, u₁}
              (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b)))
          [Meta.isDefEq] ✅️ [default] CostructuredArrow L (R.obj b) =?= ↑(Cat.of (CostructuredArrow L (R.obj b)))
            [Meta.isDefEq] ✅️ [default] Comma L (fromPUnit (R.obj b)) =?= ↑(Cat.of (CostructuredArrow L (R.obj b)))
              [Meta.isDefEq] ✅️ [default] Comma L (fromPUnit (R.obj b)) =?= (Cat.of (CostructuredArrow L (R.obj b))).1
                [Meta.isDefEq] ✅️ [default] Comma L (fromPUnit (R.obj b)) =?= CostructuredArrow L (R.obj b)
                  [Meta.isDefEq] ✅️ [default] Comma L (fromPUnit (R.obj b)) =?= Comma L (fromPUnit (R.obj b))
[Meta.synthInstance] ❌️ HasColimitsOfShape (CostructuredArrow L (R.obj b)) (Type u₁)
  [Meta.synthInstance.apply] ❌️ apply @Types.hasColimitsOfShape to HasColimitsOfShape (CostructuredArrow L (R.obj b))
        (Type u₁)
    [Meta.synthInstance.tryResolve] ❌️ HasColimitsOfShape (CostructuredArrow L (R.obj b))
          (Type u₁) ≟ HasColimitsOfShape ?m.79 (Type ?u.120)
      [Meta.isDefEq] ❌️ [instances] HasColimitsOfShape (CostructuredArrow L (R.obj b))
            (Type u₁) =?= HasColimitsOfShape ?m.79 (Type ?u.120)
        [Meta.isDefEq] ❌️ [instances] (Cat.of (CostructuredArrow L (R.obj b))).str =?= ?m.80
          [Meta.isDefEq.assign.checkTypes] ❌️ (?m.80 : Category.{?u.121, u₁}
                (CostructuredArrow L
                  (R.obj
                    b))) := ((Cat.of
                  (CostructuredArrow L (R.obj b))).str : Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b))))
            [Meta.isDefEq] ❌️ [instances] Category.{?u.121, u₁}
                  (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b)))
              [Meta.isDefEq] ❌️ [instances] CostructuredArrow L (R.obj b) =?= ↑(Cat.of (CostructuredArrow L (R.obj b)))
                [Meta.isDefEq] ❌️ [instances] CostructuredArrow L
                      (R.obj b) =?= (Cat.of (CostructuredArrow L (R.obj b))).1
                  [Meta.isDefEq.onFailure] ❌️ CostructuredArrow L
                        (R.obj b) =?= (Cat.of (CostructuredArrow L (R.obj b))).1
              [Meta.isDefEq.onFailure] ❌️ Category.{?u.121, u₁}
                    (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b)))
              [Meta.isDefEq.onFailure] ❌️ Category.{?u.121, u₁}
                    (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b)))
-/
#guard_msgs in
postprocess_traces
  filterSubtrees (fun x => do
    ((ofClass `Meta.synthInstance.apply x) <&&>
      (containsString "CategoryTheory.Limits.Types.hasColimitsOfShape" x)) <||>
    ((ofClass `Meta.isDefEq.assign.checkTypes x) <&&>
      (containsString "Cat.of" x) <&&> (return !(← failed x)))) >=>
  filterSubtrees (containsString ".str : Category") in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
example (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    set_option trace.Meta.synthInstance true in
    set_option trace.Meta.isDefEq true in
    set_option trace.Meta.isDefEq.printTransparency true in
    set_option trace.Meta.isDefEq.assign.checkTypes true in
    exact filtered_colim_preservesFiniteLimits
  sorry

set_option backward.isDefEq.instanceTypes false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma isFiltered_of_isFiltered_costructuredArrow_small (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    exact filtered_colim_preservesFiniteLimits
  refine lim.map ((colimitIsoColimitGrothendieck L F.flip).hom ≫
    (inv (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R'))) ≫
    (colimitLimitIso (R' ⋙ CostructuredArrow.grothendieckProj L ⋙ F.flip).flip).inv ≫
    colim.map ?_ ≫
    colimit.pre _ R' ≫
    (colimitIsoColimitGrothendieck L (limit F)).inv
  exact (limitCompWhiskeringLeftIsoCompLimit F (R' ⋙ CostructuredArrow.grothendieckProj L)).hom

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

/-- Given functors `L : A ⥤ T` and `R : B ⥤ T` with a common codomain we can conclude that `A`
is filtered given that `R` is final, `B` is filtered and each costructured arrow category
`CostructuredArrow L (R.obj b)` is filtered. -/
theorem isFiltered_of_isFiltered_costructuredArrow (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let sC : ∀ b, CostructuredArrow (sA.inverse ⋙ L ⋙ sT.functor)
      ((sB.inverse ⋙ R ⋙ sT.functor).obj ⟨b⟩) ≌ CostructuredArrow L (R.obj b) := fun b =>
    (CostructuredArrow.pre sA.inverse (L ⋙ sT.functor) _).asEquivalence.trans
      (CostructuredArrow.post L sT.functor _).asEquivalence.symm
  have : ∀ b, IsFiltered (CostructuredArrow _ ((sB.inverse ⋙ R ⋙ sT.functor).obj b)) :=
    fun b => IsFiltered.of_equivalence (sC b.1).symm
  have := isFiltered_of_isFiltered_costructuredArrow_small
    (sA.inverse ⋙ L ⋙ sT.functor) (sB.inverse ⋙ R ⋙ sT.functor)
  exact IsFiltered.of_equivalence sA.symm

end CategoryTheory
