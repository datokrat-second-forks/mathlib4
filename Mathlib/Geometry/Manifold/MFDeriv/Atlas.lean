/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of models with corners and (extended) charts

In this file, we analyse the differentiability of charts, models with corners and extended charts.
We show that
* models with corners are differentiable
* charts are differentiable on their source
* `mdifferentiableOn_extChartAt`: `extChartAt` is differentiable on its source

Suppose an open partial homeomorphism `e` is differentiable. This file shows
* `OpenPartialHomeomorph.MDifferentiable.mfderiv`: its derivative is a continuous linear equivalence
* `OpenPartialHomeomorph.MDifferentiable.mfderiv_bijective`: its derivative is bijective;
  there are also spellings with trivial kernel and full range

In particular, (extended) charts have bijective differential.

## Tags
charts, differentiable, bijective
-/

@[expose] public section

noncomputable section

open Bundle Set

open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

section ModelWithCorners
namespace ModelWithCorners

/- In general, the model with corner `I` is implicit in most theorems in differential geometry, but
this section is about `I` as a map, not as a parameter. Therefore, we make it explicit. -/
variable (I)

/-! #### Model with corners -/

/-- The derivative of the model embedding `I : H → E` at `x` is the canonical identification
`ModelWithCorners.fromTangentSpace`. -/
protected theorem hasMFDerivAt {x} :
    HasMFDerivAt I 𝓘(𝕜, E) I x
      ((I.fromTangentSpace x : TangentSpace I x →L[𝕜] E).toTangentSpaceAt (I x)) := by
  refine ⟨I.continuousAt, ?_⟩
  have key :
      (tangentSpaceCastModel 𝓘(𝕜, E) (I x) : TangentSpace 𝓘(𝕜, E) (I x) →L[𝕜] E) ∘L
        (((I.fromTangentSpace x : TangentSpace I x →L[𝕜] E).toTangentSpaceAt (I x)) ∘L
          ((tangentSpaceCastModel I x).symm : E →L[𝕜] TangentSpace I x)) =
        ContinuousLinearMap.id 𝕜 E := by
    ext v
    simp [ModelWithCorners.fromTangentSpace, NormedSpace.fromTangentSpace, tangentSpaceCastModel]
  rw [key]
  exact (hasFDerivWithinAt_id _ _).congr' I.rightInvOn (mem_range_self _)

protected theorem hasMFDerivWithinAt {s x} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x
      ((I.fromTangentSpace x : TangentSpace I x →L[𝕜] E).toTangentSpaceAt (I x)) :=
  I.hasMFDerivAt.hasMFDerivWithinAt

protected theorem mdifferentiableWithinAt {s x} : MDiffAt[s] I x :=
  I.hasMFDerivWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableAt {x} : MDiffAt I x :=
  I.hasMFDerivAt.mdifferentiableAt

protected theorem mdifferentiableOn {s} : MDiff[s] I := fun _ _ =>
  I.mdifferentiableWithinAt

protected theorem mdifferentiable : MDiff I := fun _ => I.mdifferentiableAt

theorem hasMFDerivWithinAt_symm {x} (hx : x ∈ range I) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x
      ((I.fromTangentSpace (I.symm x)).symm.toContinuousLinearMap ∘L
        (NormedSpace.fromTangentSpace x).toContinuousLinearMap) := by
  refine ⟨I.continuousWithinAt_symm, ?_⟩
  have key :
      (tangentSpaceCastModel I (I.symm x) : TangentSpace I (I.symm x) →L[𝕜] E) ∘L
        (((I.fromTangentSpace (I.symm x)).symm.toContinuousLinearMap ∘L
            (NormedSpace.fromTangentSpace x).toContinuousLinearMap) ∘L
          ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm : E →L[𝕜] TangentSpace 𝓘(𝕜, E) x)) =
        ContinuousLinearMap.id 𝕜 E := by
    ext v
    simp [ModelWithCorners.fromTangentSpace, NormedSpace.fromTangentSpace, tangentSpaceCastModel]
  rw [key]
  exact (hasFDerivWithinAt_id _ _).congr' (fun _y hy => I.rightInvOn hy.1) ⟨hx, mem_range_self _⟩

theorem mdifferentiableOn_symm : MDiff[range I] I.symm := fun _x hx =>
  (I.hasMFDerivWithinAt_symm hx).mdifferentiableWithinAt

theorem mdifferentiableWithinAt_symm {z : E} (hz : z ∈ range I) :
    MDiffAt[range I] I.symm z :=
  I.mdifferentiableOn_symm z hz

end ModelWithCorners

end ModelWithCorners

section Charts

variable {e : OpenPartialHomeomorph M H}

theorem mdifferentiableAt_of_mem_maximalAtlas
    (h : e ∈ IsManifold.maximalAtlas I 1 M) {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  (contMDiffAt_of_mem_maximalAtlas h hx).mdifferentiableAt one_ne_zero

lemma mdifferentiableAt_symm_of_mem_maximalAtlas
    (h : e ∈ IsManifold.maximalAtlas I 1 M) {x : H} (hx : x ∈ e.target) :
    MDiffAt e.symm x :=
  contMDiffAt_symm_of_mem_maximalAtlas h hx |>.mdifferentiableAt one_ne_zero

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I'' 1 M'']

theorem mdifferentiableAt_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx
    |>.mdifferentiableAt one_ne_zero

theorem mdifferentiableOn_atlas (h : e ∈ atlas H M) : MDiff[e.source] e :=
  fun _x hx => (mdifferentiableAt_atlas h hx).mdifferentiableWithinAt

theorem mdifferentiableAt_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
    MDiffAt e.symm x :=
  mdifferentiableAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas h) hx

theorem mdifferentiableOn_atlas_symm (h : e ∈ atlas H M) : MDiff[e.target] e.symm :=
  fun _x hx => (mdifferentiableAt_atlas_symm h hx).mdifferentiableWithinAt

theorem mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.MDifferentiable I I :=
  ⟨mdifferentiableOn_atlas h, mdifferentiableOn_atlas_symm h⟩

theorem mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I :=
  mdifferentiable_of_mem_atlas (chart_mem_atlas _ _)

end Charts

/-! ### Differentiable open partial homeomorphisms -/

namespace OpenPartialHomeomorph.MDifferentiable
variable {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I')
  {e' : OpenPartialHomeomorph M' M''}
include he

nonrec theorem symm : e.symm.MDifferentiable I' I := he.symm

protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MDiffAt e x :=
  (he.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx)

theorem mdifferentiableAt_symm {x : M'} (hx : x ∈ e.target) : MDiffAt e.symm x :=
  (he.2 x hx).mdifferentiableAt (e.open_target.mem_nhds hx)

/-- The derivative of `e.symm` composed with that of `e` is the identity -- up to the
identification `tangentSpaceCast` of the tangent spaces at `x` and at `e.symm (e x)`, which are
propositionally but not definitionally the same point. -/
theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv% e.symm (e x)).comp (mfderiv% e x) =
      (tangentSpaceCast I x (e.symm (e x)) :
        TangentSpace I x →L[𝕜] TangentSpace I (e.symm (e x))) := by
  have hcomp : mfderiv% (e.symm ∘ e) x = (mfderiv% e.symm (e x)).comp (mfderiv% e x) :=
    mfderiv_comp x (he.mdifferentiableAt_symm (e.map_source hx)) (he.mdifferentiableAt hx)
  have hEq : (e.symm ∘ e : M → M) =ᶠ[𝓝 x] _root_.id :=
    Filter.mem_of_superset (e.open_source.mem_nhds hx) (by mfld_set_tac)
  rw [← hcomp, hEq.mfderiv_eq, mfderiv_id, ContinuousLinearMap.comp_id]
  rfl

theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv% e (e.symm x)).comp (mfderiv% e.symm x) =
      (tangentSpaceCast I' x (e (e.symm x)) :
        TangentSpace I' x →L[𝕜] TangentSpace I' (e (e.symm x))) :=
  he.symm.symm_comp_deriv hx

/-- The derivative of a differentiable open partial homeomorphism, as a continuous linear
equivalence between the tangent spaces at `x` and `e x`. -/
protected def mfderiv (he : e.MDifferentiable I I') {x : M} (hx : x ∈ e.source) :
    TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv% e x with
    invFun := tangentSpaceCast I (e.symm (e x)) x ∘ mfderiv% e.symm (e x)
    continuous_toFun := (mfderiv% e x).cont
    continuous_invFun :=
      (tangentSpaceCast I (e.symm (e x)) x).continuous.comp (mfderiv% e.symm (e x)).cont
    left_inv := fun y => by
      change tangentSpaceCast I (e.symm (e x)) x
          (((mfderiv% e.symm (e x)).comp (mfderiv% e x)) y) = y
      rw [he.symm_comp_deriv hx]
      rfl
    right_inv := fun y => by
      change (mfderiv% e x)
          (tangentSpaceCast I (e.symm (e x)) x ((mfderiv% e.symm (e x)) y)) = y
      rw [mfderiv_congr_point (f := (e : M → M')) (e.left_inv hx).symm]
      change tangentSpaceCast I' (e (e.symm (e x))) (e x)
          (((mfderiv% e (e.symm (e x))).comp (mfderiv% e.symm (e x))) y) = y
      rw [he.comp_symm_deriv (e.map_source hx)]
      rfl }

theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv% e x) :=
  (he.mfderiv hx).bijective

theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv% e x) :=
  (he.mfderiv hx).injective

theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv% e x) :=
  (he.mfderiv hx).surjective

theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : (mfderiv% e x).ker = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker

theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : (mfderiv% e x).range = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range

theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv% e x) = univ :=
  (he.mfderiv_surjective hx).range_eq

theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' := by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiableAt hx.2).comp _ (he.mdifferentiableAt hx.1)).mdifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiableAt hx.2).comp _
          (he'.symm.mdifferentiableAt hx.1)).mdifferentiableWithinAt

end OpenPartialHomeomorph.MDifferentiable

/-! ### Differentiability of `extChartAt` -/

section

open IsManifold

variable {e : OpenPartialHomeomorph M H}

theorem OpenPartialHomeomorph.mdifferentiableAt_extend
    {x : M} (he : e ∈ maximalAtlas I 1 M) (hx : x ∈ e.source) :
    MDiffAt (e.extend I) x :=
  e.contMDiffAt_extend he hx |>.mdifferentiableAt (by simp)

theorem OpenPartialHomeomorph.mdifferentiableOn_extend (he : e ∈ maximalAtlas I 1 M) :
    MDiff[e.source] (e.extend I) :=
  e.contMDiffOn_extend he |>.mdifferentiableOn (by simp)

variable {z : E}

theorem mdifferentiableWithinAt_extend_symm
    (he : e ∈ maximalAtlas I 1 M) (h : z ∈ (e.extend I).target) :
    MDiffAt[range I] (e.extend I).symm z := by
  have Z : MDiffAt[range ↑I] I.symm z :=
    I.mdifferentiableWithinAt_symm (e.extend_target_subset_range h)
  apply MDifferentiableAt.comp_mdifferentiableWithinAt _ _ Z
  exact mdifferentiableAt_symm_of_mem_maximalAtlas he (by simp_all)

theorem mdifferentiableOn_extend_symm (he : e ∈ maximalAtlas I 1 M) :
    MDiff[(e.extend I).target] (e.extend I).symm := by
  intro y hy
  exact mdifferentiableWithinAt_extend_symm he hy |>.mono (e.extend_target_subset_range)

/-- A congruence lemma for `mfderivWithin` at two propositionally equal points, expressed via the
definitional identification `tangentSpaceCast` between the tangent spaces.
TODO: move next to `mfderiv_congr_point` in `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean`. -/
theorem mfderivWithin_congr_point {f : M → M'} {s : Set M} {x x' : M} (h : x = x') :
    mfderiv[s] f x =
      (tangentSpaceCast I' (f x') (f x) : TangentSpace I' (f x') →L[𝕜] TangentSpace I' (f x)) ∘L
        mfderiv[s] f x' ∘L
        (tangentSpaceCast I x x' : TangentSpace I x →L[𝕜] TangentSpace I x') := by
  subst h; rfl

/-- The composition of the derivative of an extended chart `e.extend I` with the derivative of its
inverse `(e.extend I).symm` gives the identity. The two derivatives do not compose on the nose:
the target of the first is the tangent space at `e.extend I ((e.extend I).symm y)`, which is only
propositionally the point `y`, whence the `tangentSpaceCast`.
Version where the basepoint belongs to `(e.extend I).target`. -/
lemma mfderiv_extend_comp_mfderivWithin_extend_symm
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (tangentSpaceCast 𝓘(𝕜, E) ((e.extend I) ((e.extend I).symm y)) y :
        TangentSpace 𝓘(𝕜, E) ((e.extend I) ((e.extend I).symm y)) →L[𝕜]
          TangentSpace 𝓘(𝕜, E) y) ∘L
      ((mfderiv% (e.extend I) ((e.extend I).symm y)) ∘L
        (mfderiv[range I] (e.extend I).symm y)) =
      ContinuousLinearMap.id 𝕜 (TangentSpace 𝓘(𝕜, E) y) := by
  have U : UniqueMDiffAt[range I] y := by
    apply I.uniqueMDiffOn
    apply e.extend_target_subset_range hy
  have h'y : (e.extend I).symm y ∈ e.source := PartialEquiv.map_target _ (by simp_all)
  have hry : (e.extend I) ((e.extend I).symm y) = y := (e.extend I).right_inv hy
  have hEq : ((e.extend I) ∘ (e.extend I).symm) =ᶠ[𝓝[range I] y] _root_.id := by
    filter_upwards [hry ▸ e.extend_target_mem_nhdsWithin h'y (I := I)] with z hz
    simp_all
  rw [← mfderiv_comp_mfderivWithin]; rotate_left
  · exact e.mdifferentiableAt_extend he h'y
  · exact mdifferentiableWithinAt_extend_symm he hy
  · exact U
  rw [hEq.mfderivWithin_eq hry, mfderivWithin_id U, ContinuousLinearMap.comp_id]
  rfl

/-- The composition of the derivative of the inverse of an extended chart `e.extend I` with the
derivative of `e.extend I` gives the identity.
Version where the basepoint belongs to `(e.extend I).target`. -/
lemma mfderivWithin_extend_symm_comp_mfderiv_extend
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (mfderiv[range I] (e.extend I).symm y) ∘L
      ((tangentSpaceCast 𝓘(𝕜, E) ((e.extend I) ((e.extend I).symm y)) y :
          TangentSpace 𝓘(𝕜, E) ((e.extend I) ((e.extend I).symm y)) →L[𝕜]
            TangentSpace 𝓘(𝕜, E) y) ∘L
        (mfderiv% (e.extend I) ((e.extend I).symm y))) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I ((e.extend I).symm y)) := by
  have h'y : (e.extend I).symm y ∈ e.source := by simp_all
  have hry : (e.extend I) ((e.extend I).symm y) = y := (e.extend I).right_inv hy
  have U' : UniqueMDiffAt[(e.extend I).source] ((e.extend I).symm y) := by
    rw [e.extend_source]
    exact e.open_source.uniqueMDiffWithinAt h'y
  have hmf : mfderiv% (e.extend I) ((e.extend I).symm y)
      = mfderiv[(e.extend I).source] (e.extend I) ((e.extend I).symm y) := by
    rw [mfderivWithin_eq_mfderiv U']
    exact e.mdifferentiableAt_extend he h'y
  have key : mfderiv[(e.extend I).source]
        ((e.extend I).symm ∘ (e.extend I)) ((e.extend I).symm y)
      = (mfderiv[range I] (e.extend I).symm ((e.extend I) ((e.extend I).symm y))).comp
        (mfderiv[(e.extend I).source] (e.extend I) ((e.extend I).symm y)) :=
    mfderivWithin_comp_of_eq (mdifferentiableWithinAt_extend_symm he hy)
      ((e.mdifferentiableAt_extend he h'y).mdifferentiableWithinAt)
      (fun z hz ↦ e.extend_target_subset_range ((e.extend I).map_source hz)) U' hry
  have hEq : ((e.extend I).symm ∘ (e.extend I))
      =ᶠ[𝓝[(e.extend I).source] ((e.extend I).symm y)] _root_.id := by
    filter_upwards [e.extend_source_mem_nhdsWithin (I := I) h'y] with z hz
    simp only [Function.comp_def, PartialEquiv.left_inv (e.extend I) hz, id_eq]
  have hlz : ((e.extend I).symm ∘ (e.extend I)) ((e.extend I).symm y)
      = _root_.id ((e.extend I).symm y) := by
    simp only [Function.comp_def, PartialEquiv.right_inv (e.extend I) hy, id_eq]
  rw [hEq.mfderivWithin_eq hlz, mfderivWithin_id U', ContinuousLinearMap.comp_id] at key
  rw [hmf, mfderivWithin_congr_point (f := ((e.extend I).symm : E → M)) hry.symm]
  change (tangentSpaceCast I ((e.extend I).symm ((e.extend I) ((e.extend I).symm y)))
      ((e.extend I).symm y)).toContinuousLinearMap ∘L
      ((mfderiv[range I] (e.extend I).symm ((e.extend I) ((e.extend I).symm y))) ∘L
        (mfderiv[(e.extend I).source] (e.extend I) ((e.extend I).symm y))) = _
  rw [← key]
  rfl

/-- The composition of the derivative of an extended chart `e.extend I` with the derivative of its
inverse `(e.extend I).symm` gives the identity.
Version where the basepoint belongs to `(e.extend I).source`. -/
lemma mfderiv_extend_comp_mfderivWithin_extend_symm'
    {y : M} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).source) :
    (mfderiv% (e.extend I) y) ∘L
      ((tangentSpaceCast I ((e.extend I).symm (e.extend I y)) y :
          TangentSpace I ((e.extend I).symm (e.extend I y)) →L[𝕜] TangentSpace I y) ∘L
        (mfderiv[range I] (e.extend I).symm (e.extend I y))) =
      ContinuousLinearMap.id 𝕜 (TangentSpace 𝓘(𝕜, E) (e.extend I y)) := by
  have hly : (e.extend I).symm (e.extend I y) = y := (e.extend I).left_inv hy
  rw [mfderiv_congr_point (f := ((e.extend I) : M → E)) hly.symm]
  change (tangentSpaceCast 𝓘(𝕜, E) ((e.extend I) ((e.extend I).symm (e.extend I y)))
      (e.extend I y)).toContinuousLinearMap ∘L
      ((mfderiv% (e.extend I) ((e.extend I).symm (e.extend I y))) ∘L
        (mfderiv[range I] (e.extend I).symm (e.extend I y))) = _
  exact mfderiv_extend_comp_mfderivWithin_extend_symm he ((e.extend I).map_source hy)

/-- The composition of the derivative of the inverse of an extended chart `e.extend I` with the
derivative of `e.extend I` gives the identity.
Version where the basepoint belongs to `e.source`. -/
lemma mfderivWithin_extend_symm_comp_mfderiv_extend'
    {y : M} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ e.source) :
    (tangentSpaceCast I ((e.extend I).symm (e.extend I y)) y :
        TangentSpace I ((e.extend I).symm (e.extend I y)) →L[𝕜] TangentSpace I y) ∘L
      ((mfderiv[range I] (e.extend I).symm (e.extend I y)) ∘L (mfderiv% (e.extend I) y))
      = ContinuousLinearMap.id 𝕜 (TangentSpace I y) := by
  have hy' : y ∈ (e.extend I).source := by simpa using hy
  have hly : (e.extend I).symm (e.extend I y) = y := (e.extend I).left_inv hy'
  rw [mfderiv_congr_point (f := ((e.extend I) : M → E)) hly.symm]
  change (tangentSpaceCast I ((e.extend I).symm (e.extend I y)) y).toContinuousLinearMap ∘L
      (((mfderiv[range I] (e.extend I).symm (e.extend I y)) ∘L
        ((tangentSpaceCast 𝓘(𝕜, E) ((e.extend I) ((e.extend I).symm (e.extend I y)))
            (e.extend I y)).toContinuousLinearMap ∘L
          (mfderiv% (e.extend I) ((e.extend I).symm (e.extend I y))))) ∘L
        (tangentSpaceCast I y ((e.extend I).symm (e.extend I y))).toContinuousLinearMap) = _
  rw [mfderivWithin_extend_symm_comp_mfderiv_extend he ((e.extend I).map_source hy')]
  rfl

lemma isInvertible_mfderivWithin_extend_symm
    {y : E} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ (e.extend I).target) :
    (mfderiv[range I] (e.extend I).symm y).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extend_symm_comp_mfderiv_extend he hy)
    (mfderiv_extend_comp_mfderivWithin_extend_symm he hy)

lemma isInvertible_mfderiv_extend {y : M} (he : e ∈ maximalAtlas I 1 M) (hy : y ∈ e.source) :
    (mfderiv% (e.extend I) y).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extend_comp_mfderivWithin_extend_symm' he (by simpa using hy))
    (mfderivWithin_extend_symm_comp_mfderiv_extend' he hy)

end

section extChartAt

variable [IsManifold I 1 M] {s : Set M} {x y : M} {z : E}

theorem hasMFDerivAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt% (extChartAt I x) y
      (((I.fromTangentSpace (chartAt H x y) :
            TangentSpace I (chartAt H x y) →L[𝕜] E).toTangentSpaceAt (I (chartAt H x y))).comp
        (mfderiv% (chartAt H x) y)) :=
  I.hasMFDerivAt.comp y ((mdifferentiable_chart x).mdifferentiableAt h).hasMFDerivAt

theorem hasMFDerivWithinAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt[s] (extChartAt I x) y
      (((I.fromTangentSpace (chartAt H x y) :
            TangentSpace I (chartAt H x y) →L[𝕜] E).toTangentSpaceAt (I (chartAt H x y))).comp
        (mfderiv% (chartAt H x) y)) :=
  (hasMFDerivAt_extChartAt h).hasMFDerivWithinAt

theorem mdifferentiableAt_extChartAt (h : y ∈ (chartAt H x).source) :
    MDiffAt (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt h).mdifferentiableAt

theorem mdifferentiableOn_extChartAt : MDiff[(chartAt H x).source] (extChartAt I x) :=
  fun _y hy ↦ (hasMFDerivWithinAt_extChartAt hy).mdifferentiableWithinAt

theorem mdifferentiableWithinAt_extChartAt_symm (h : z ∈ (extChartAt I x).target) :
    MDiffAt[range I] (extChartAt I x).symm z :=
  mdifferentiableWithinAt_extend_symm (IsManifold.chart_mem_maximalAtlas x) h

theorem mdifferentiableOn_extChartAt_symm :
    MDiff[(extChartAt I x).target] (extChartAt I x).symm :=
  mdifferentiableOn_extend_symm (IsManifold.chart_mem_maximalAtlas x)

/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm {x : M}
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (tangentSpaceCast 𝓘(𝕜, E) ((extChartAt I x) ((extChartAt I x).symm y)) y :
        TangentSpace 𝓘(𝕜, E) ((extChartAt I x) ((extChartAt I x).symm y)) →L[𝕜]
          TangentSpace 𝓘(𝕜, E) y) ∘L
      ((mfderiv% (extChartAt I x) ((extChartAt I x).symm y)) ∘L
        (mfderiv[range I] (extChartAt I x).symm y)) =
      ContinuousLinearMap.id 𝕜 (TangentSpace 𝓘(𝕜, E) y) :=
  mfderiv_extend_comp_mfderivWithin_extend_symm (IsManifold.chart_mem_maximalAtlas x) hy

/-- The composition of the derivative of `extChartAt` with the derivative of the inverse of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' {x : M}
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y) ∘L
      ((tangentSpaceCast I ((extChartAt I x).symm (extChartAt I x y)) y :
          TangentSpace I ((extChartAt I x).symm (extChartAt I x y)) →L[𝕜] TangentSpace I y) ∘L
        (mfderiv[range I] (extChartAt I x).symm (extChartAt I x y))) =
      ContinuousLinearMap.id 𝕜 (TangentSpace 𝓘(𝕜, E) (extChartAt I x y)) :=
  mfderiv_extend_comp_mfderivWithin_extend_symm' (IsManifold.chart_mem_maximalAtlas x) hy

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).target`. -/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y) ∘L
      ((tangentSpaceCast 𝓘(𝕜, E) ((extChartAt I x) ((extChartAt I x).symm y)) y :
          TangentSpace 𝓘(𝕜, E) ((extChartAt I x) ((extChartAt I x).symm y)) →L[𝕜]
            TangentSpace 𝓘(𝕜, E) y) ∘L
        (mfderiv% (extChartAt I x) ((extChartAt I x).symm y))) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I ((extChartAt I x).symm y)) :=
  mfderivWithin_extend_symm_comp_mfderiv_extend (IsManifold.chart_mem_maximalAtlas x) hy

/-- The composition of the derivative of the inverse of `extChartAt` with the derivative of
`extChartAt` gives the identity.
Version where the basepoint belongs to `(extChartAt I x).source`. -/
lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    {y : M} (hy : y ∈ (extChartAt I x).source) :
    (tangentSpaceCast I ((extChartAt I x).symm (extChartAt I x y)) y :
        TangentSpace I ((extChartAt I x).symm (extChartAt I x y)) →L[𝕜] TangentSpace I y) ∘L
      ((mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)) ∘L
        (mfderiv% (extChartAt I x) y)) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I y) :=
  mfderivWithin_extend_symm_comp_mfderiv_extend' (IsManifold.chart_mem_maximalAtlas x)
    (by simpa using hy)

lemma isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv[range I] (extChartAt I x).symm y).IsInvertible :=
  isInvertible_mfderivWithin_extend_symm (IsManifold.chart_mem_maximalAtlas x) hy

lemma isInvertible_mfderiv_extChartAt {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv% (extChartAt I x) y).IsInvertible :=
  isInvertible_mfderiv_extend (IsManifold.chart_mem_maximalAtlas x) (by simpa using hy)

set_option backward.isDefEq.respectTransparency false in
/-- The trivialization of the tangent bundle at a point is the manifold derivative of the
extended chart, read into the tangent space to `E` at the chart point through
`NormedSpace.fromTangentSpace`. -/
theorem TangentBundle.continuousLinearMapAt_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x).toTangentSpaceAt
        (extChartAt I x₀ x) =
      mfderiv% (extChartAt I x₀) x := by
  have : MDiffAt (extChartAt I x₀) x := mdifferentiableAt_extChartAt hx
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe] at this
  simp only [mfderiv, this, mfld_simps]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse trivialization of the tangent bundle at a point is the manifold derivative of the
inverse of the extended chart, read through `NormedSpace.fromTangentSpace` on the source and
through `tangentSpaceCast` on the target (the two base points `x` and
`(extChartAt I x₀).symm (extChartAt I x₀ x)` are only propositionally equal). -/
theorem TangentBundle.symmL_trivializationAt
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (tangentSpaceCast I x ((extChartAt I x₀).symm (extChartAt I x₀ x))).toContinuousLinearMap ∘L
        ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x ∘L
          (NormedSpace.fromTangentSpace (extChartAt I x₀ x)).toContinuousLinearMap) =
      mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x) := by
  have : MDiffAt[range I] ((chartAt H x₀).symm ∘ I.symm) (I (chartAt H x₀ x)) := by
    simpa using mdifferentiableWithinAt_extChartAt_symm (by simp [hx])
  simp only [hx, mfderivWithin, this, mfld_simps]
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

omit [IsManifold I 1 M] in
/-- The `fderivWithin` of the round-trip composition `(extChartAt I x) ∘ (extChartAt I x).symm`
at the chart point in `range I` equals the identity. -/
lemma fderivWithin_extChartAt_comp_extChartAt_symm_range :
    fderivWithin 𝕜 ((extChartAt I x) ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) =
      ContinuousLinearMap.id 𝕜 _ := by
  set φ := extChartAt I x
  have eq_nhd : ((extChartAt I x) ∘ (extChartAt I x).symm) =ᶠ[𝓝[range I] (extChartAt I x x)] id :=
    Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
      (fun _ ↦ (extChartAt I x).right_inv)
  rw [eq_nhd.fderivWithin_eq (by simp)]
  exact fderivWithin_id <| I.uniqueDiffOn.uniqueDiffWithinAt (mem_range_self _)

/-- The manifold derivative of `extChartAt` at the basepoint is the definitional identification
`tangentSpaceCastModel`. This is the characterization announced in the docstring of
`tangentSpaceCastModel`: the technical cast *is* the derivative of the extended chart. -/
lemma mfderiv_extChartAt_self :
    mfderiv% (extChartAt I x) x =
      ((tangentSpaceCastModel I x : TangentSpace I x →L[𝕜] E).toTangentSpaceAt
        (extChartAt I x x)) := by
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt (by simp),
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp)]
  ext v
  exact congrArg (fun w ↦ (NormedSpace.fromTangentSpace (extChartAt I x x)).symm w)
    ((tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x)
      (tangentSpaceCastModel I x v))

-- TODO: should there be a version for `extChartAt`?
/-- The manifold derivative within `range I` of `(extChartAt I x).symm` at the chart point is the
inverse of `tangentSpaceCastModel`, read between the relevant tangent spaces. -/
lemma mfderivWithin_range_extChartAt_symm :
    mfderiv[range I] (extChartAt I x).symm (extChartAt I x x) =
      (((NormedSpace.fromTangentSpace (extChartAt I x x)).trans
          ((tangentSpaceCastModel I x).symm.trans
            (tangentSpaceCast I x ((extChartAt I x).symm (extChartAt I x x))))) :
        TangentSpace 𝓘(𝕜, E) (extChartAt I x x) →L[𝕜]
          TangentSpace I ((extChartAt I x).symm (extChartAt I x x))) := by
  rw [← TangentBundle.symmL_trivializationAt (by simp),
    TangentBundle.symmL_trivializationAt_eq_core (by simp)]
  ext v
  exact congrArg (fun w ↦ tangentSpaceCast I x ((extChartAt I x).symm (extChartAt I x x))
      ((tangentSpaceCastModel I x).symm w))
    ((tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x)
      (NormedSpace.fromTangentSpace (extChartAt I x x) v))

/-- The inverse of the derivative of `(extChartAt I x).symm` at the chart point,
applied to a tangent vector, gives back the tangent vector. -/
lemma mfderivWithin_extChartAt_symm_inverse_apply (v : TangentSpace I x) :
    (mfderiv[range I] (extChartAt I x).symm (extChartAt I x x)).inverse
        (tangentSpaceCast I x ((extChartAt I x).symm (extChartAt I x x)) v) =
      ((tangentSpaceCastModel I x : TangentSpace I x →L[𝕜] E).toTangentSpaceAt
        (extChartAt I x x)) v := by
  rw [mfderivWithin_range_extChartAt_symm, ContinuousLinearMap.inverse_equiv]
  rfl

end extChartAt
