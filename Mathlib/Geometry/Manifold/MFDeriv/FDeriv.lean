/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.Notation

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Fréchet derivative `fderiv`. In this section, we prove
this and related statements.
-/

public section

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'}
  {s : Set E} {x : E}

section MFDerivFDeriv

theorem uniqueMDiffWithinAt_iff_uniqueDiffWithinAt :
    UniqueMDiffAt[s] x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp only [UniqueMDiffWithinAt, mfld_simps]
  exact Iff.rfl

alias ⟨UniqueMDiffWithinAt.uniqueDiffWithinAt, UniqueDiffWithinAt.uniqueMDiffWithinAt⟩ :=
  uniqueMDiffWithinAt_iff_uniqueDiffWithinAt

theorem uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiff[s] ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMDiffOn, UniqueDiffOn, uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]

alias ⟨UniqueMDiffOn.uniqueDiffOn, UniqueDiffOn.uniqueMDiffOn⟩ := uniqueMDiffOn_iff_uniqueDiffOn

theorem ModelWithCorners.uniqueMDiffOn {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : UniqueMDiff[Set.range I] :=
  I.uniqueDiffOn.uniqueMDiffOn

@[simp, mfld_simps]
theorem writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f :=
  rfl

variable {f' : E →L[𝕜] E'}

/-- On a model vector space, a map has a manifold derivative at `x` within `s` iff it has the
corresponding Fréchet derivative there. The manifold-side derivative is the given
`f' : E →L[𝕜] E'` read through the canonical identification `NormedSpace.fromTangentSpace`
between the tangent spaces of the model space and the model space itself. -/
theorem hasMFDerivWithinAt_iff_hasFDerivWithinAt :
    HasMFDerivAt[s] f x
      (((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).symm :
          E' →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)) ∘L
        f' ∘L (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x : TangentSpace 𝓘(𝕜, E) x →L[𝕜] E)) ↔
      HasFDerivWithinAt f f' s x := by
  have key : (tangentSpaceCastModel 𝓘(𝕜, E') (f x) :
        TangentSpace 𝓘(𝕜, E') (f x) →L[𝕜] E') ∘L
      (((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).symm :
          E' →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)) ∘L
        f' ∘L (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x : TangentSpace 𝓘(𝕜, E) x →L[𝕜] E)) ∘L
      ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm : E →L[𝕜] TangentSpace 𝓘(𝕜, E) x) = f' := by
    ext v
    simp [NormedSpace.fromTangentSpace]
  simp only [HasMFDerivWithinAt, key, mfld_simps]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.continuousWithinAt, h⟩⟩

alias ⟨HasMFDerivWithinAt.hasFDerivWithinAt, HasFDerivWithinAt.hasMFDerivWithinAt⟩ :=
  hasMFDerivWithinAt_iff_hasFDerivWithinAt

/-- On a model vector space, a map has a manifold derivative at `x` iff it has the corresponding
Fréchet derivative there; see `hasMFDerivWithinAt_iff_hasFDerivWithinAt` for the way the two
derivatives correspond. -/
theorem hasMFDerivAt_iff_hasFDerivAt :
    HasMFDerivAt% f x
      (((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).symm :
          E' →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)) ∘L
        f' ∘L (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x : TangentSpace 𝓘(𝕜, E) x →L[𝕜] E)) ↔
      HasFDerivAt f f' x := by
  rw [← hasMFDerivWithinAt_univ, hasMFDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_univ]

alias ⟨HasMFDerivAt.hasFDerivAt, HasFDerivAt.hasMFDerivAt⟩ := hasMFDerivAt_iff_hasFDerivAt

/-- For maps between vector spaces, `MDifferentiableWithinAt` and `DifferentiableWithinAt`
coincide -/
theorem mdifferentiableWithinAt_iff_differentiableWithinAt :
    MDiffAt[s] f x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [mdifferentiableWithinAt_iff', mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousWithinAt, H⟩⟩

alias ⟨MDifferentiableWithinAt.differentiableWithinAt,
    DifferentiableWithinAt.mdifferentiableWithinAt⟩ :=
  mdifferentiableWithinAt_iff_differentiableWithinAt

/-- For maps between vector spaces, `MDifferentiableAt` and `DifferentiableAt` coincide -/
theorem mdifferentiableAt_iff_differentiableAt :
    MDiffAt f x ↔ DifferentiableAt 𝕜 f x := by
  simp only [mdifferentiableAt_iff, differentiableWithinAt_univ, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.continuousAt, H⟩⟩

alias ⟨MDifferentiableAt.differentiableAt, DifferentiableAt.mdifferentiableAt⟩ :=
  mdifferentiableAt_iff_differentiableAt

/-- For maps between vector spaces, `MDifferentiableOn` and `DifferentiableOn` coincide -/
theorem mdifferentiableOn_iff_differentiableOn :
    MDiff[s] f ↔ DifferentiableOn 𝕜 f s := by
  simp only [MDifferentiableOn, DifferentiableOn,
    mdifferentiableWithinAt_iff_differentiableWithinAt]

alias ⟨MDifferentiableOn.differentiableOn, DifferentiableOn.mdifferentiableOn⟩ :=
  mdifferentiableOn_iff_differentiableOn

/-- For maps between vector spaces, `MDifferentiable` and `Differentiable` coincide -/
theorem mdifferentiable_iff_differentiable : MDiff f ↔ Differentiable 𝕜 f := by
  simp only [MDifferentiable, Differentiable, mdifferentiableAt_iff_differentiableAt]

alias ⟨MDifferentiable.differentiable, Differentiable.mdifferentiable⟩ :=
  mdifferentiable_iff_differentiable

/-- For maps between vector spaces, `mfderivWithin` and `fderivWithin` coincide, through the
canonical identification `NormedSpace.fromTangentSpace` of the tangent spaces of the model space
with the model space itself. -/
@[simp]
theorem mfderivWithin_eq_fderivWithin :
    mfderiv[s] f x =
      ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).symm : E' →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)) ∘L
        fderivWithin 𝕜 f s x ∘L
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x : TangentSpace 𝓘(𝕜, E) x →L[𝕜] E) := by
  by_cases h : MDiffAt[s] f x
  · rw [h.mfderivWithin]
    simp [NormedSpace.fromTangentSpace, chartAt_self_eq, mfld_simps]
  · have h' := mdifferentiableWithinAt_iff_differentiableWithinAt.not.1 h
    rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt h',
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide, through the canonical
identification `NormedSpace.fromTangentSpace` of the tangent spaces of the model space with the
model space itself. -/
@[simp]
theorem mfderiv_eq_fderiv :
    mfderiv% f x =
      ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).symm : E' →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)) ∘L
        fderiv 𝕜 f x ∘L
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x : TangentSpace 𝓘(𝕜, E) x →L[𝕜] E) := by
  rw [← mfderivWithin_univ, ← fderivWithin_univ]
  exact mfderivWithin_eq_fderivWithin

end MFDerivFDeriv
