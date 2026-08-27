/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Notation

/-! # Tangent bundles

This file defines the tangent bundle as a `C^n` vector bundle.

Let `M` be a manifold with model `I` on `(E, H)`. The tangent space `TangentSpace I (x : M)` has
already been defined as a type synonym for `E`, and the tangent bundle `TangentBundle I M` as an
abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

In this file, when `M` is `C^1`, we construct a vector bundle structure
on `TangentBundle I M` using the `VectorBundleCore` construction indexed by the charts of `M`
with fibers `E`. Given two charts `i, j : OpenPartialHomeomorph M H`, the coordinate change
between `i` and `j` at a point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a vector bundle `TangentBundle` with fibers `TangentSpace`.

## Main definitions and results

* `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.

* When `M` is a `C^{n+1}` manifold, `TangentBundle I M` has a `C^n` vector bundle
  structure over `M`. In particular, it is a topological space, a vector bundle, a fiber bundle,
  and a `C^n` manifold.
-/

@[expose] public section


open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

noncomputable section

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Auxiliary lemma for tangent spaces: the derivative of a coordinate change between two charts is
  `C^n` on its source. -/
theorem contDiffOn_fderiv_coord_change [IsManifold I (n + 1) M]
    (i j : atlas H M) :
    ContDiffOn 𝕜 n (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source := by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I := by
    refine I.extendCoordChange_source.trans_subset ?_; apply image_subset_range
  intro x hx
  refine (ContDiffWithinAt.fderivWithin_right ?_ I.uniqueDiffOn le_rfl
    <| h hx).mono h
  refine (I.contDiffOn_extendCoordChange (subset_maximalAtlas i.2)
    (subset_maximalAtlas j.2) x hx).mono_of_mem_nhdsWithin ?_
  exact I.extendCoordChange_source_mem_nhdsWithin hx

open IsManifold

variable [IsManifold I 1 M] [IsManifold I' 1 M']

variable (I M) in
/-- Let `M` be a `C^1` manifold with model `I` on `(E, H)`.
Then `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`. -/
@[simps indexAt coordChange]
def tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_fun_id, ContinuousLinearMap.id_apply]
    · exact I.uniqueDiffWithinAt_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hx]
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + 1) M := by simpa
    refine (contDiffOn_fderiv_coord_change (n := 0) i j).continuousOn.comp
      (i.1.continuousOn_extend.mono ?_) ?_
    · rw [i.1.extend_source]; exact inter_subset_left
    exact mapsTo_iff_image_subset.2 (i.1.extend_image_source_inter j.1).subset
  coordChange_comp := by
    have : IsManifold I (0 + 1) M := by simpa
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds (I := I) hxi (j.1.extend_source_mem_nhds (I := I) hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hxi, j.1.extend_left_inv hxj]
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas j.2)
        (subset_maximalAtlas k.2) hxj hxk).differentiableWithinAt one_ne_zero
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas i.2)
        (subset_maximalAtlas j.2) hxi hxj).differentiableWithinAt one_ne_zero
    · intro x _; exact mem_range_self _
    · exact I.uniqueDiffWithinAt_image
    · rw [Function.comp_apply, i.1.extend_left_inv hxi]

/-- `simp`-normal form is `tangentBundleCore_localTriv_baseSet`. -/
theorem tangentBundleCore_baseSet (i) : (tangentBundleCore I M).baseSet i = i.1.source := rfl

@[simp]
theorem tangentBundleCore_localTriv_baseSet (i) :
    ((tangentBundleCore I M).localTriv i).baseSet = i.1.source := rfl

theorem tangentBundleCore_coordChange_achart (x x' z : M) :
    (tangentBundleCore I M).coordChange (achart H x) (achart H x') z =
      fderivWithin 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl

section tangentCoordChange

variable (I) in
/-- In a manifold `M`, given two preferred charts indexed by `x y : M`, `tangentCoordChange I x y`
is the family of derivatives of the corresponding change-of-coordinates map. It takes junk values
outside the intersection of the sources of the two charts.

Note that this definition takes advantage of the fact that `tangentBundleCore` has the same base
sets as the preferred charts of the base manifold. -/
abbrev tangentCoordChange (x y : M) : M → E →L[𝕜] E :=
  (tangentBundleCore I M).coordChange (achart H x) (achart H y)

lemma tangentCoordChange_def {x y z : M} : tangentCoordChange I x y z =
    fderivWithin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) := rfl

lemma tangentCoordChange_self {x z : M} {v : E} (h : z ∈ (extChartAt I x).source) :
    tangentCoordChange I x x z v = v := by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

lemma tangentCoordChange_comp {w x y z : M} {v : E}
    (h : z ∈ (extChartAt I w).source ∩ (extChartAt I x).source ∩ (extChartAt I y).source) :
    tangentCoordChange I x y z (tangentCoordChange I w x z v) = tangentCoordChange I w y z v := by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h

lemma hasFDerivWithinAt_tangentCoordChange {x y z : M}
    (h : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) :
    HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I x).symm) (tangentCoordChange I x y z)
      (range I) (extChartAt I x z) :=
  have h' : extChartAt I x z ∈ ((extChartAt I x).symm ≫ (extChartAt I y)).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact mem_image_of_mem _ h
  ((contDiffWithinAt_ext_coord_change y x h').differentiableWithinAt one_ne_zero).hasFDerivWithinAt

lemma continuousOn_tangentCoordChange (x y : M) : ContinuousOn (tangentCoordChange I x y)
    ((extChartAt I x).source ∩ (extChartAt I y).source) := by
  convert! (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

end tangentCoordChange

local notation "TM" => TangentBundle I M

section TangentBundleInstances

instance : TopologicalSpace TM :=
  (tangentBundleCore I M).totalSpaceTopologyAlong (tangentSpaceCastModel I)

instance TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).fiberBundleAlong (tangentSpaceCastModel I)

instance TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).vectorBundleAlong (tangentSpaceCastModel I)

namespace TangentBundle

protected theorem chartAt (p : TM) :
    chartAt (ModelProd H E) p =
      ((tangentBundleCore I M).localTrivAtAlong (tangentSpaceCastModel I)
        p.1).toOpenPartialHomeomorph ≫ₕ
        (chartAt H p.1).prod (OpenPartialHomeomorph.refl E) :=
  rfl

theorem chartAt_toPartialEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toPartialEquiv =
      ((tangentBundleCore I M).localTrivAtAlong (tangentSpaceCastModel I) p.1).toPartialEquiv ≫
        (chartAt H p.1).toPartialEquiv.prod (PartialEquiv.refl E) :=
  rfl

theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).localTrivAtAlong (tangentSpaceCastModel I) x :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source =
      π E (TangentSpace I) ⁻¹' (chartAt H x).source :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl

theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
        ((chartAt H z.1).extend I z.1) (tangentSpaceCastModel I z.1 z.2)) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace I) x z).1 = z.1 :=
  rfl

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : TM) :
    p ∈ (chartAt (ModelProd H E) q).source ↔ p.1 ∈ (chartAt H q.1).source := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]

@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × E) (q : TM) :
    p ∈ (chartAt (ModelProd H E) q).target ↔ p.1 ∈ (chartAt H q.1).target := by
  /- porting note: was
  simp +contextual only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [PartialEquiv.prod_symm]
  simp +contextual only [and_iff_left_iff_imp, mfld_simps]

@[simp, mfld_simps]
theorem coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1 :=
  rfl

@[simp, mfld_simps]
theorem coe_chartAt_symm_fst (p : H × E) (q : TM) :
    ((chartAt (ModelProd H E) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl

/-- The trivialization of the tangent space can be expressed in terms of the tangent bundle core,
composed with the definitional identification `tangentSpaceCastModel`. This lemma is
implementation-facing; to write the trivialization as the manifold derivative of `extChartAt`,
see `TangentBundle.continuousLinearMapAt_trivializationAt`. -/
theorem continuousLinearMapAt_trivializationAt_eq_core {b₀ b : M} (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt 𝕜 b =
      ((tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b).comp
        (tangentSpaceCastModel I b : TangentSpace I b →L[𝕜] E) :=
  (tangentBundleCore I M).localTrivAlong_continuousLinearMapAt (tangentSpaceCastModel I)
    (achart H b₀) hb

/-- The inverse trivialization of the tangent space can be expressed in terms of the tangent bundle
core, composed with the definitional identification `tangentSpaceCastModel`. This lemma is
implementation-facing; to write the inverse trivialization as the manifold derivative of
`(extChartAt I b₀).symm`, see `TangentBundle.symmL_trivializationAt`. -/
theorem symmL_trivializationAt_eq_core {b₀ b : M} (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b =
      ((tangentSpaceCastModel I b).symm : E →L[𝕜] TangentSpace I b).comp
        ((tangentBundleCore I M).coordChange (achart H b₀) (achart H b) b) :=
  (tangentBundleCore I M).localTrivAlong_symmL (tangentSpaceCastModel I) (achart H b₀) hb

/-! The lemmas below have high priority because `simp` simplifies the LHS to `.id _ _`;
we prefer `1` as the simp-normal form. -/
@[simp high, mfld_simps]
theorem coordChange_model_space (b b' x : F) :
    (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1 := by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using!
    fderivWithin_id uniqueDiffWithinAt_univ

@[simp high, mfld_simps]
theorem symmL_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).symmL 𝕜 b' =
      ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) b').symm : F →L[𝕜] TangentSpace 𝓘(𝕜, F) b') := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_univ _), coordChange_model_space]
  ext v
  rfl

@[simp high, mfld_simps]
theorem continuousLinearMapAt_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' =
      (NormedSpace.fromTangentSpace (𝕜 := 𝕜) b' : TangentSpace 𝓘(𝕜, F) b' →L[𝕜] F) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_univ _),
    coordChange_model_space]
  ext v
  rfl

end TangentBundle

omit [IsManifold I 1 M] in
lemma tangentBundleCore.isContMDiff [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (tangentBundleCore I M).IsContMDiff I n := by
  have : IsManifold I n M := .of_le (n := n + 1) (le_self_add)
  refine ⟨fun i j => ?_⟩
  rw [contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas i.2),
    contMDiffOn_iff_contDiffOn]
  · refine ((contDiffOn_fderiv_coord_change (I := I) i j).congr fun x hx => ?_).mono ?_
    · rw [PartialEquiv.trans_source'] at hx
      simp_rw [Function.comp_apply, tangentBundleCore_coordChange, (i.1.extend I).right_inv hx.1]
    · exact (i.1.extend_image_source_inter j.1).subset
  · apply inter_subset_left

omit [IsManifold I 1 M] in
lemma TangentBundle.contMDiffVectorBundle [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  exact (tangentBundleCore I M).contMDiffVectorBundleAlong (tangentSpaceCastModel I)

omit [IsManifold I 1 M] in
instance [h : IsManifold I ∞ M] :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
instance [IsManifold I ω M] :
    ContMDiffVectorBundle ω E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
instance [h : IsManifold I 2 M] :
    ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I := by
  have : IsManifold I (1 + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

end TangentBundleInstances

/-! ## The tangent bundle to the model space -/

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
theorem trivializationAt_model_space_apply (p : TangentBundle I H) (x : H) :
    trivializationAt E (TangentSpace I) x p = (p.1, I.fromTangentSpace p.1 p.2) := by
  simp only [TangentBundle.trivializationAt_apply]
  have : fderivWithin 𝕜 (↑I ∘ ↑I.symm) (range I) (I p.proj) =
      fderivWithin 𝕜 id (range I) (I p.proj) :=
    fderivWithin_congr' (fun y hy ↦ by simp [hy]) (mem_range_self p.proj)
  simp [this, fderivWithin_id (ModelWithCorners.uniqueDiffWithinAt_image I),
    ModelWithCorners.fromTangentSpace]

/-- The canonical identification `I.fromTangentSpace` between the tangent space to the model
space and the model vector space is the fiberwise linear part of the trivialization of the
tangent bundle: this anchors its mathematical meaning. -/
theorem ModelWithCorners.fromTangentSpace_eq_continuousLinearMapAt (x : H) :
    (I.fromTangentSpace x : TangentSpace I x →L[𝕜] E) =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 x := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source H x)]
  ext v
  exact ((tangentBundleCore I H).coordChange_self (achart H x) x (mem_chart_source H x) _).symm

/-- The inverse of the canonical identification `I.fromTangentSpace` between the tangent space
to the model space and the model vector space is the inverse trivialization of the tangent
bundle: this anchors its mathematical meaning. -/
theorem ModelWithCorners.fromTangentSpace_symm_eq_symmL (x : H) :
    ((I.fromTangentSpace x).symm : E →L[𝕜] TangentSpace I x) =
      (trivializationAt E (TangentSpace I) x).symmL 𝕜 x := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source H x)]
  ext v
  exact congrArg (I.fromTangentSpace x).symm
    ((tangentBundleCore I H).coordChange_self (achart H x) x (mem_chart_source H x) v).symm

variable (I) in
/-- The canonical identification between the tangent bundle to the model space and the
product space. For the homeomorphism version, see `tangentBundleModelSpaceHomeomorph`; for
the diffeomorphism version, see `tangentBundleModelSpaceDiffeomorph`. -/
def tangentBundleModelSpaceEquiv : TangentBundle I H ≃ ModelProd H E where
  toFun p := (p.1, I.fromTangentSpace p.1 p.2)
  invFun p := ⟨p.1, (I.fromTangentSpace p.1).symm p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp, mfld_simps]
theorem tangentBundleModelSpaceEquiv_apply (p : TangentBundle I H) :
    tangentBundleModelSpaceEquiv I p = (p.1, I.fromTangentSpace p.1 p.2) :=
  rfl

@[simp, mfld_simps]
theorem tangentBundleModelSpaceEquiv_symm_apply (p : ModelProd H E) :
    (tangentBundleModelSpaceEquiv I).symm p = ⟨p.1, (I.fromTangentSpace p.1).symm p.2⟩ :=
  rfl

/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `tangentBundleModelSpaceEquiv`. -/
@[simp, mfld_simps]
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toPartialEquiv =
      (tangentBundleModelSpaceEquiv I).toPartialEquiv := by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1)
      (I.fromTangentSpace x.1 x.2)
  · ext; · rfl
    apply heq_of_eq
    exact congrArg (I.fromTangentSpace x.1).symm <|
      (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  exact eq_univ_of_forall fun x ↦ (TangentBundle.mem_chart_source_iff x p).2 (mem_univ _)

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = tangentBundleModelSpaceEquiv I := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv, tangentBundle_model_space_chartAt]; rfl

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) =
      (tangentBundleModelSpaceEquiv I).symm := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.symm_toPartialEquiv,
    tangentBundle_model_space_chartAt]; rfl

theorem tangentBundleCore_coordChange_model_space (x x' z : H) :
    (tangentBundleCore I H).coordChange (achart H x) (achart H x') z =
    ContinuousLinearMap.id 𝕜 E := by
  ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism. For the diffeomorphism version, see `tangentBundleModelSpaceDiffeomorph`. -/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { tangentBundleModelSpaceEquiv I with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), 0⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), 0⟩
      have : Continuous (chartAt (ModelProd H E) p).symm := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).symm.continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe :
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H → ModelProd H E) =
      tangentBundleModelSpaceEquiv I :=
  rfl

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E → TangentBundle I H) =
      (tangentBundleModelSpaceEquiv I).symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_tangentBundleModelSpaceHomeomorph :
    ContMDiff I.tangent (I.prod 𝓘(𝕜, E)) n
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H → ModelProd H E) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y ↦ ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, tangentBundleModelSpaceEquiv, Equiv.coe_fn_symm_mk,
    forall_exists_index, Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simp [PartialEquiv.prod]

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_tangentBundleModelSpaceHomeomorph_symm :
    ContMDiff I.tangent I.tangent n
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E → TangentBundle I H) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y ↦ ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, tangentBundleModelSpaceEquiv, Equiv.coe_fn_symm_mk,
    forall_exists_index, Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simp [PartialEquiv.prod]

variable (H I) in
/-- In the tangent bundle to the model space, the second projection is `C^n`. -/
lemma contMDiff_snd_tangentBundle_modelSpace :
    ContMDiff I.tangent 𝓘(𝕜, E) n
      (fun (p : TangentBundle I H) ↦ I.fromTangentSpace p.1 p.2) := by
  change CMDiff n ((id Prod.snd : ModelProd H E → E) ∘ (tangentBundleModelSpaceHomeomorph I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert! contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} {x : E} :
    CMDiffAt[s] n (T% V) x ↔
      ContDiffWithinAt 𝕜 n (fun y ↦ NormedSpace.fromTangentSpace y (V y)) s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ContMDiffWithinAt.contDiffWithinAt <|
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ h
  · apply Bundle.contMDiffWithinAt_totalSpace.2
    refine ⟨contMDiffWithinAt_id, ?_⟩
    convert! h.contMDiffWithinAt with y
    simp [NormedSpace.fromTangentSpace, ModelWithCorners.fromTangentSpace]

set_option backward.isDefEq.respectTransparency false in
/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiffAt_vectorSpace_iff_contDiffAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {x : E} :
    CMDiffAt n (T% V) x ↔ ContDiffAt 𝕜 n (fun y ↦ NormedSpace.fromTangentSpace y (V y)) x := by
  simp only [← contMDiffWithinAt_univ, ← contDiffWithinAt_univ,
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiffOn_vectorSpace_iff_contDiffOn
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    CMDiff[s] n (T% V) ↔ ContDiffOn 𝕜 n (fun y ↦ NormedSpace.fromTangentSpace y (V y)) s := by
  simp only [ContMDiffOn, ContDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

set_option backward.isDefEq.respectTransparency false in
/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
lemma contMDiff_vectorSpace_iff_contDiff {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} :
    CMDiff n (T% V) ↔ ContDiff 𝕜 n (fun y ↦ NormedSpace.fromTangentSpace y (V y)) := by
  simp only [← contMDiffOn_univ, ← contDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn]

section inTangentCoordinates

variable {N : Type*}

/-- The map `inCoordinates` for the tangent bundle is trivial on the model spaces -/
theorem inCoordinates_tangent_bundle_core_model_space (x₀ x : H) (y₀ y : H')
    (ϕ : TangentSpace I x →L[𝕜] TangentSpace I' y) :
    inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀ x y₀ y ϕ =
      (I'.fromTangentSpace y : TangentSpace I' y →L[𝕜] E') ∘L ϕ ∘L
        ((I.fromTangentSpace x).symm : E →L[𝕜] TangentSpace I x) := by
  rw [ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_univ _),
    TangentBundle.symmL_trivializationAt_eq_core (mem_univ _),
    tangentBundleCore_coordChange_model_space, tangentBundleCore_coordChange_model_space]
  ext v
  rfl

variable (I I') in
/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
in charts around `g x`, `inTangentCoordinates I I' f g ϕ x₀ x` is a coordinate change of
this continuous linear map that makes sense from charts around `f x₀` to charts around `g x₀`
by composing it with appropriate coordinate changes.

This is the underlying function of the trivializations of the hom of (pullbacks of) tangent spaces.
-/
def inTangentCoordinates (f : N → M) (g : N → M')
    (ϕ : Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)) : N → N → E →L[𝕜] E' :=
  fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

theorem inTangentCoordinates_model_space (f : N → H) (g : N → H')
    (ϕ : Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)) (x₀ x : N) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      (I'.fromTangentSpace (g x) : TangentSpace I' (g x) →L[𝕜] E') ∘L ϕ x ∘L
        ((I.fromTangentSpace (f x)).symm : E →L[𝕜] TangentSpace I (f x)) := by
  simp only [inTangentCoordinates, inCoordinates_tangent_bundle_core_model_space]

/-- To write a linear map between tangent spaces in coordinates amounts to precomposing and
postcomposing it with suitable coordinate changes. For a concrete version expressing the
change of coordinates as derivatives of extended charts,
see `inTangentCoordinates_eq_mfderiv_comp`. -/
theorem inTangentCoordinates_eq (f : N → M) (g : N → M')
    (ϕ : Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)) {x₀ x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source) (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      (tangentBundleCore I' M').coordChange (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L
        (tangentSpaceCastModel I' (g x) : TangentSpace I' (g x) →L[𝕜] E') ∘L ϕ x ∘L
        ((tangentSpaceCastModel I (f x)).symm : E →L[𝕜] TangentSpace I (f x)) ∘L
        (tangentBundleCore I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x) := by
  rw [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy,
    TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

end inTangentCoordinates

end General
