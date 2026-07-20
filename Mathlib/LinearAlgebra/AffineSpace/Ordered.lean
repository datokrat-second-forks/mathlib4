/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Module.Synonym
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.LinearAlgebra.AffineSpace.Slope
meta import Lean.PostprocessTraces

/-!
# Ordered modules as affine spaces

In this file we prove some theorems about `slope` and `lineMap` in the case when the module `E`
acting on the codomain `PE` of a function is an ordered module over its domain `k`. We also prove
inequalities that can be used to link convexity of a function on an interval to monotonicity of the
slope, see section docstring below for details.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered module interpreted as an affine space.

## Tags

affine space, ordered module, slope
-/

public section


open AffineMap

variable {k E PE : Type*}

/-!
### Monotonicity of `lineMap`

In this section we prove that `lineMap a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/


section OrderedRing

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
variable {a a' b b' : E} {r r' : k}

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_mono_left (ha : a ≤ a') (hr : r ≤ 1) : lineMap a b r ≤ lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_nonneg.2 hr

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_strict_mono_left (ha : a < a') (hr : r < 1) : lineMap a b r < lineMap a' b r := by
  simp only [lineMap_apply_module]
  gcongr
  exact sub_pos.2 hr

set_option backward.isDefEq.respectTransparency false in
omit [IsOrderedRing k] in
theorem lineMap_mono_right (hb : b ≤ b') (hr : 0 ≤ r) : lineMap a b r ≤ lineMap a b' r := by
  simp only [lineMap_apply_module]
  gcongr

set_option backward.isDefEq.respectTransparency false in
omit [IsOrderedRing k] in
theorem lineMap_strict_mono_right (hb : b < b') (hr : 0 < r) : lineMap a b r < lineMap a b' r := by
  simp only [lineMap_apply_module]; gcongr

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r ≤ lineMap a' b' r :=
  (lineMap_mono_left ha h₁).trans (lineMap_mono_right hb h₀)

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r < lineMap a' b' r := by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)

variable [PosSMulReflectLT k E]

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_lt_lineMap_iff_of_lt (h : r < r') : lineMap a b r < lineMap a b r' ↔ a < b := by
  simp only [lineMap_apply_module]
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos_left (sub_pos.2 h)]

set_option backward.isDefEq.respectTransparency false in
theorem left_lt_lineMap_iff_lt (h : 0 < r) : a < lineMap a b r ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)

/-
`lineMap_lt_left_iff_lt` and `right_lt_lineMap_iff_lt` transport a lemma stated at `E` along the
order dual: the proof applies the other lemma at `E := Eᵒᵈ` to a goal stated at `E`. Two phases:

1. Unifying the lemma's conclusion (at `Eᵒᵈ`) with the goal (at `E`) assigns the goal's E-side
   data to the lemma's binder mvars, in particular `?inst : Module k Eᵒᵈ := ‹Module k E›`.
   These mvars come from the elaborator, not from instance search, so they are not marked
   instance-typed, and the assignment is accepted at default transparency, where the type synonym
   `OrderDual` unfolds.
2. `[PosSMulReflectLT k Eᵒᵈ]` does not occur in the conclusion, so it is left over for synthesis
   by type. After step 1, that type spells its `SMul k Eᵒᵈ` slot as a projection of the assigned
   `Module k E` instance. The candidate `OrderDual.instPosSMulReflectLT : PosSMulReflectLT α βᵒᵈ`
   forces `?β := E` by matching `βᵒᵈ` structurally; its own `SMul` slot then unfolds (at
   synthesis transparency) to a bare mvar of type `SMul k E` — instance-typed, created by
   `tryResolve` — which has to swallow the goal's `SMul k Eᵒᵈ`-typed slot value. The mvar check
   compares `SMul k E =?= SMul k Eᵒᵈ` at `.instances`, where the plain def `OrderDual` does not
   unfold, and rejects the assignment; the synthesis fails. (The hypothesis `‹PosSMulReflectLT
   k E›` itself is no candidate: `Eᵒᵈ ≟ E` already fails in `tryResolve`, on any toolchain.)

A standalone `#synth PosSMulReflectLT k Eᵒᵈ` succeeds: a freshly elaborated goal spells its
`SMul` slot via `OrderDual.instSMul`, which the candidate matches structurally, so no
heterogeneously-typed assignment is needed. Only the goal type baked in step 1 is poisoned.

* The other leftover instance arguments (`Module k Eᵒᵈ`, `IsStrictOrderedModule k Eᵒᵈ`, …)
  synthesize fine: their `OrderDual` candidates expose bare unassigned instance mvars that the
  unifier solves by `trySynthPending` (synthesis at `E`), not by swallowing a mismatched value.
* Same two-phase shape as `Mathlib/CategoryTheory/Filtered/CostructuredArrow.lean` (lenient
  unification bakes a mismatch into a later synthesis goal); here the heterogeneity comes from
  the deliberate `OrderDual` defeq abuse of `(E := Eᵒᵈ)` transport, not from a simp rewrite.
* `PosSMulReflectLT` is a Prop, but the rejected mvar is its data-valued `SMul` argument, so a
  Prop-exemption would not help here.

Possible solutions:
* State the `OrderDual` transfer instances so that their data slots match projection spellings
  (not realistic), or prove the two lemmas directly instead of by `(E := Eᵒᵈ)` transport.
* Making `OrderDual` reducible at `.instances` would fix the check but is off the table: the
  synonym must stay opaque so that the order instances of `E` and `Eᵒᵈ` do not collide.
-/

section InstanceTypesDemos

open Lean.PostprocessTraces

-- Phase 1: `exact`'s unification leniently assigns the E-side `Module` instance to the
-- lemma's `Module k Eᵒᵈ` binder mvar. (Run with the workaround so the demo compiles.)
/--
trace: [Meta.isDefEq.assign.checkTypes] ✅️ (?m.40 : Module k Eᵒᵈ) := (inst✝² : Module k E)
-/
#guard_msgs in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.isDefEq.assign.checkTypes x)
    <&&> (containsString "Module k Eᵒᵈ) := (inst" x))
in
set_option backward.isDefEq.instanceTypes false in
set_option backward.isDefEq.respectTransparency false in
example (h : 0 < r) : lineMap a b r < a ↔ b < a := by
  set_option trace.Meta.isDefEq.assign.checkTypes true in
  exact left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

-- Phase 2: synthesis of the leftover `PosSMulReflectLT k Eᵒᵈ` fails on the strict check:
-- the candidate's `SMul` mvar has type `SMul k E`, the goal's slot value has type
-- `SMul k Eᵒᵈ`, and `OrderDual` does not unfold at `.instances`.
/--
error: failed to synthesize instance of type class
  PosSMulReflectLT k Eᵒᵈ
---
trace: [Meta.synthInstance] ❌️ PosSMulReflectLT k Eᵒᵈ
  [Meta.synthInstance.apply] ❌️ apply @OrderDual.instPosSMulReflectLT to PosSMulReflectLT k Eᵒᵈ
    [Meta.synthInstance.tryResolve] ❌️ PosSMulReflectLT k Eᵒᵈ ≟ PosSMulReflectLT ?m.47 ?m.48ᵒᵈ
      [Meta.isDefEq] ❌️ [instances] PosSMulReflectLT k Eᵒᵈ =?= PosSMulReflectLT ?m.47 ?m.48ᵒᵈ
        [Meta.isDefEq] ✅️ [instances] k =?= ?m.47
          [Meta.isDefEq] k [nonassignable] =?= ?m.47 [assignable]
          [Meta.isDefEq.assign.checkTypes] ✅️ (?m.47 : Type ?u.50) := (k : Type u_1)
            [Meta.isDefEq] ✅️ [default] Type ?u.50 =?= Type u_1
        [Meta.isDefEq] ✅️ [instances] Eᵒᵈ =?= ?m.48ᵒᵈ
          [Meta.isDefEq] ✅️ [instances] E =?= ?m.48
            [Meta.isDefEq] E [nonassignable] =?= ?m.48 [assignable]
            [Meta.isDefEq.assign.checkTypes] ✅️ (?m.48 : Type ?u.51) := (E : Type u_2)
              [Meta.isDefEq] ✅️ [default] Type ?u.51 =?= Type u_2
        [Meta.isDefEq] ✅️ [instances] inst✝⁷.toPreorder =?= ?m.49
          [Meta.isDefEq] inst✝⁷.toPreorder [nonassignable] =?= ?m.49 [assignable]
          [Meta.isDefEq.assign.checkTypes] ✅️ (?m.49 : Preorder k) := (inst✝⁷.toPreorder : Preorder k)
            [Meta.isDefEq] ✅️ [instances] Preorder k =?= Preorder k
              [Meta.isDefEq] ✅️ [instances] k =?= k
        [Meta.isDefEq] ✅️ [instances] instMulZeroClassOfSemiring.toZero =?= ?m.52
          [Meta.isDefEq] instMulZeroClassOfSemiring.toZero [nonassignable] =?= ?m.52 [assignable]
          [Meta.isDefEq.assign.checkTypes] ✅️ (?m.52 : Zero k) := (instMulZeroClassOfSemiring.toZero : Zero k)
            [Meta.isDefEq] ✅️ [instances] Zero k =?= Zero k
              [Meta.isDefEq] ✅️ [instances] k =?= k
        [Meta.isDefEq] ❌️ [default] DistribMulAction.toDistribSMul.toSMul =?= OrderDual.instSMul
          [Meta.isDefEq] ❌️ [default] DistribMulAction.toDistribSMul.toSMul =?= ?m.51
            [Meta.isDefEq] DistribMulAction.toDistribSMul.toSMul [nonassignable] =?= ?m.51 [assignable]
            [Meta.isDefEq.assign.checkTypes] ❌️ (?m.51 : SMul k
                  E) := (DistribMulAction.toDistribSMul.toSMul : SMul k Eᵒᵈ)
              [Meta.isDefEq] ❌️ [instances] SMul k E =?= SMul k Eᵒᵈ
                [Meta.isDefEq] ✅️ [instances] k =?= k
                [Meta.isDefEq] ❌️ [instances] E =?= Eᵒᵈ
                  [Meta.isDefEq.onFailure] ❌️ E =?= Eᵒᵈ
                [Meta.isDefEq.onFailure] ❌️ SMul k E =?= SMul k Eᵒᵈ
                [Meta.isDefEq.onFailure] ❌️ SMul k E =?= SMul k Eᵒᵈ
            [Meta.isDefEq.assign.checkTypes] ❌️ (?m.51 : SMul k E) := (inst✝².toSemigroupAction.1 : SMul k Eᵒᵈ)
              [Meta.isDefEq] ❌️ [instances] SMul k E =?= SMul k Eᵒᵈ
        [Meta.isDefEq.onFailure] ❌️ PosSMulReflectLT k Eᵒᵈ =?= PosSMulReflectLT ?m.47 ?m.48ᵒᵈ
        [Meta.isDefEq.onFailure] ❌️ PosSMulReflectLT k Eᵒᵈ =?= PosSMulReflectLT ?m.47 ?m.48ᵒᵈ
-/
#guard_msgs in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.synthInstance.apply x)
    <&&> (containsString "OrderDual.instPosSMulReflectLT" x))
  >=> filterSubtrees unsuccessful
in
set_option backward.isDefEq.respectTransparency false in
example (h : 0 < r) : lineMap a b r < a ↔ b < a := by
  set_option trace.Meta.synthInstance true in
  set_option trace.Meta.isDefEq true in
  set_option trace.Meta.isDefEq.printTransparency true in
  set_option trace.Meta.isDefEq.assign.checkTypes true in
  exact left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

-- Contrast: with a freshly elaborated goal type, the same synthesis succeeds.
/-- info: OrderDual.instPosSMulReflectLT -/
#guard_msgs in
#synth PosSMulReflectLT k Eᵒᵈ

end InstanceTypesDemos

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.instanceTypes false in
theorem lineMap_lt_left_iff_lt (h : 0 < r) : lineMap a b r < a ↔ b < a :=
  left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_lt_right_iff_lt (h : r < 1) : lineMap a b r < b ↔ a < b :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.instanceTypes false in
theorem right_lt_lineMap_iff_lt (h : r < 1) : b < lineMap a b r ↔ b < a :=
  lineMap_lt_right_iff_lt (E := Eᵒᵈ) h

end OrderedRing

section LinearOrderedRing

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_le_lineMap_iff_of_lt' (h : a < b) : lineMap a b r ≤ lineMap a b r' ↔ r ≤ r' := by
  simp only [lineMap_apply_module']
  rw [add_le_add_iff_right, smul_le_smul_iff_of_pos_right (sub_pos.mpr h)]

set_option backward.isDefEq.respectTransparency false in
theorem left_le_lineMap_iff_nonneg (h : a < b) : a ≤ lineMap a b r ↔ 0 ≤ r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_le_left_iff_nonpos (h : a < b) : lineMap a b r ≤ a ↔ r ≤ 0 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
theorem right_le_lineMap_iff_one_le (h : a < b) : b ≤ lineMap a b r ↔ 1 ≤ r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_le_right_iff_le_one (h : a < b) : lineMap a b r ≤ b ↔ r ≤ 1 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_lt_lineMap_iff_of_lt' (h : a < b) : lineMap a b r < lineMap a b r' ↔ r < r' := by
  simp only [lineMap_apply_module']
  rw [add_lt_add_iff_right, smul_lt_smul_iff_of_pos_right (sub_pos.mpr h)]

set_option backward.isDefEq.respectTransparency false in
theorem left_lt_lineMap_iff_pos (h : a < b) : a < lineMap a b r ↔ 0 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_lt_left_iff_neg (h : a < b) : lineMap a b r < a ↔ r < 0 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
theorem right_lt_lineMap_iff_one_lt (h : a < b) : b < lineMap a b r ↔ 1 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_lt_right_iff_lt_one (h : a < b) : lineMap a b r < b ↔ r < 1 := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_one]

theorem midpoint_le_midpoint [Invertible (2 : k)] (ha : a ≤ a') (hb : b ≤ b') :
    midpoint k a b ≤ midpoint k a' b' :=
  lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) <| invOf_le_one one_le_two

end LinearOrderedRing

section LinearOrderedField

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

section

variable {a b : E} {r r' : k}

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_le_lineMap_iff_of_lt (h : r < r') : lineMap a b r ≤ lineMap a b r' ↔ a ≤ b := by
  simp only [lineMap_apply_module]
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos_left (sub_pos.2 h)]

set_option backward.isDefEq.respectTransparency false in
theorem left_le_lineMap_iff_le (h : 0 < r) : a ≤ lineMap a b r ↔ a ≤ b :=
  Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]
theorem left_le_midpoint : a ≤ midpoint k a b ↔ a ≤ b :=
  left_le_lineMap_iff_le <| inv_pos.2 zero_lt_two

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_le_left_iff_le (h : 0 < r) : lineMap a b r ≤ a ↔ b ≤ a :=
  left_le_lineMap_iff_le (E := Eᵒᵈ) h

@[simp]
theorem midpoint_le_left : midpoint k a b ≤ a ↔ b ≤ a :=
  lineMap_le_left_iff_le <| inv_pos.2 zero_lt_two

set_option backward.isDefEq.respectTransparency false in
theorem lineMap_le_right_iff_le (h : r < 1) : lineMap a b r ≤ b ↔ a ≤ b :=
  Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt h)

@[simp]
theorem midpoint_le_right : midpoint k a b ≤ b ↔ a ≤ b := lineMap_le_right_iff_le two_inv_lt_one

set_option backward.isDefEq.respectTransparency false in
theorem right_le_lineMap_iff_le (h : r < 1) : b ≤ lineMap a b r ↔ b ≤ a :=
  lineMap_le_right_iff_le (E := Eᵒᵈ) h

@[simp]
theorem right_le_midpoint : b ≤ midpoint k a b ↔ b ≤ a := right_le_lineMap_iff_le two_inv_lt_one

end

/-!
### Convexity and slope

Given an interval `[a, b]` and a point `c ∈ (a, b)`, `c = lineMap a b r`, there are a few ways to
say that the point `(c, f c)` is above/below the segment `[(a, f a), (b, f b)]`:

* compare `f c` to `lineMap (f a) (f b) r`;
* compare `slope f a c` to `slope f a b`;
* compare `slope f c b` to `slope f a b`;
* compare `slope f a c` to `slope f c b`.

In this section we prove equivalence of these four approaches. In order to make the statements more
readable, we introduce local notation `c = lineMap a b r`. Then we prove lemmas like

```
lemma map_le_lineMap_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f a b :=
```

For each inequality between `f c` and `lineMap (f a) (f b) r` we provide 3 lemmas:

* `*_left` relates it to an inequality on `slope f a c` and `slope f a b`;
* `*_right` relates it to an inequality on `slope f a b` and `slope f c b`;
* no-suffix version relates it to an inequality on `slope f a c` and `slope f c b`.

These inequalities can be used to restate `convexOn` in terms of monotonicity of the slope.
-/


variable {f : k → E} {a b r : k}

local notation "c" => lineMap a b r

section
omit [IsStrictOrderedRing k]

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f a b`. -/
theorem map_le_lineMap_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f a b := by
  rw [lineMap_apply, lineMap_apply, slope, slope, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub,
    vadd_eq_add, vadd_eq_add, smul_eq_mul, add_sub_cancel_right, smul_sub, smul_sub, smul_sub,
    sub_le_iff_le_add, mul_inv_rev, mul_smul, mul_smul, ← smul_sub, ← smul_sub, ← smul_add,
    smul_smul, ← mul_inv_rev, inv_smul_le_iff_of_pos h, smul_smul,
    mul_inv_cancel_right₀ (right_ne_zero_of_mul h.ne'), smul_add,
    smul_inv_smul₀ (left_ne_zero_of_mul h.ne')]

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f a c`. -/
theorem lineMap_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f a b ≤ slope f a c :=
  map_le_lineMap_iff_slope_le_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f a b`. -/
theorem map_lt_lineMap_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f a b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_left h)
    (map_le_lineMap_iff_slope_le_slope_left h)

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f a c`. -/
theorem lineMap_lt_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f a b < slope f a c :=
  map_lt_lineMap_iff_slope_lt_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f c b`. -/
theorem map_le_lineMap_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a b ≤ slope f c b := by
  rw [← lineMap_apply_one_sub, ← lineMap_apply_one_sub _ _ r]
  revert h; generalize 1 - r = r'; clear! r; intro h
  simp_rw [lineMap_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  rw [sub_add_eq_sub_sub_swap, sub_self, zero_sub, neg_mul_eq_mul_neg, neg_sub,
    le_inv_smul_iff_of_pos h, smul_smul, mul_inv_cancel_right₀, le_sub_comm, ← neg_sub (f b),
    smul_neg, neg_add_eq_sub]
  · exact right_ne_zero_of_mul h.ne'

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a b`. -/
theorem lineMap_le_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a b :=
  map_le_lineMap_iff_slope_le_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`. -/
theorem map_lt_lineMap_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    f c < lineMap (f a) (f b) r ↔ slope f a b < slope f c b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope_right h)
    (map_le_lineMap_iff_slope_le_slope_right h)

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a b`. -/
theorem lineMap_lt_map_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a b :=
  map_lt_lineMap_iff_slope_lt_slope_right (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

end

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f c b`. -/
theorem map_le_lineMap_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c ≤ lineMap (f a) (f b) r ↔ slope f a c ≤ slope f c b := by
  rw [map_le_lineMap_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab)), ←
    lineMap_slope_lineMap_slope_lineMap f a b r, right_le_lineMap_iff_le h₁]

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a c`. -/
theorem lineMap_le_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a c :=
  map_le_lineMap_iff_slope_le_slope (E := Eᵒᵈ) hab h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f c b`. -/
theorem map_lt_lineMap_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    f c < lineMap (f a) (f b) r ↔ slope f a c < slope f c b :=
  lt_iff_lt_of_le_iff_le' (lineMap_le_map_iff_slope_le_slope hab h₀ h₁)
    (map_le_lineMap_iff_slope_le_slope hab h₀ h₁)

set_option backward.isDefEq.respectTransparency false in
/-- Given `c = lineMap a b r`, `a < c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a c`. -/
theorem lineMap_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a c :=
  map_lt_lineMap_iff_slope_lt_slope (E := Eᵒᵈ) hab h₀ h₁

end LinearOrderedField


lemma slope_pos_iff {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : x₀ < b) :
    0 < slope f x₀ b ↔ f x₀ < f b := by
  simp [slope, hb]

lemma slope_pos_iff_gt {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜} (hb : b < x₀) :
    0 < slope f x₀ b ↔ f b < f x₀ := by
  rw [slope_comm, slope_pos_iff hb]

lemma pos_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜}
    (hb : x₀ < b) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : 0 < f b := by
  simp_all [slope]

lemma neg_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜}
    (hb : b < x₀) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : f b < 0 := by
  rwa [slope_pos_iff_gt, hf] at hbf
  exact hb
