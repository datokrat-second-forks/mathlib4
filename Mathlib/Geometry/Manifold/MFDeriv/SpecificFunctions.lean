/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of specific functions

In this file, we establish differentiability results for
- continuous linear maps and continuous linear equivalences
- the identity
- constant functions
- products
- arithmetic operations (such as addition and scalar multiplication).

-/

public section

noncomputable section

open scoped Manifold
open Bundle Set Topology

section SpecificFunctions

/-! ### Differentiability of specific functions -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']

/-- The canonical identification between the tangent space to a product manifold at `p` and the
product of the tangent spaces at `p.1` and `p.2`. Unlike `tangentSpaceCast`, this identification is
mathematically meaningful. -/
@[expose] def tangentSpaceProd (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] (p : M × M') :
    TangentSpace (I.prod I') p ≃L[𝕜] TangentSpace I p.1 × TangentSpace I' p.2 where
  toFun v := (⟨v.inner.1⟩, ⟨v.inner.2⟩)
  invFun w := ⟨(w.1.inner, w.2.inner)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_induced_rng.2 (continuous_fst.comp continuous_induced_dom)
    · exact continuous_induced_rng.2 (continuous_snd.comp continuous_induced_dom)
  continuous_invFun :=
    continuous_induced_rng.2 ((continuous_induced_dom.comp continuous_fst).prodMk
      (continuous_induced_dom.comp continuous_snd))

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

open NormedSpace in
/-- A continuous linear map `f : E →L[𝕜] E'` between vector spaces, read as a map between the
tangent space at `x` and the tangent space at `f x`, using the canonical identification
`NormedSpace.fromTangentSpace`. This is the derivative of `f` at `x`, see
`ContinuousLinearMap.mfderiv_eq`. -/
@[expose] def toTangentSpace (x : E) : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x) :=
  (fromTangentSpace (f x)).symm.toContinuousLinearMap ∘L f ∘L
    (fromTangentSpace x).toContinuousLinearMap

open NormedSpace in
/-- If a continuous linear map is injective, so is the map of tangent spaces it induces
through `ContinuousLinearMap.toTangentSpace`. -/
theorem _root_.Function.Injective.toTangentSpace (hf : Function.Injective f) (x : E) :
    Function.Injective (f.toTangentSpace x) := fun _ _ h ↦
  (fromTangentSpace x).injective (hf ((fromTangentSpace (f x)).symm.injective h))

protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x (f.toTangentSpace x) :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt% f x (f.toTangentSpace x) :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv% f x = f.toTangentSpace x :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] f x = f.toTangentSpace x :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt :
    HasMFDerivAt[s] f x ((f : E →L[𝕜] E').toTangentSpace x) :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt% f x ((f : E →L[𝕜] E').toTangentSpace x) :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv% f x = (f : E →L[𝕜] E').toTangentSpace x :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] f x = (f : E →L[𝕜] E').toTangentSpace x :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/

theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt% (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) := by
  refine ⟨continuousAt_id, ?_⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]

theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivAt[s] (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) :=
  (hasMFDerivAt_id x).hasMFDerivWithinAt

theorem mdifferentiableAt_id : MDiffAt (@id M) x :=
  (hasMFDerivAt_id x).mdifferentiableAt

theorem mdifferentiableWithinAt_id : MDiffAt[s] (@id M) x :=
  mdifferentiableAt_id.mdifferentiableWithinAt

theorem mdifferentiable_id : MDiff (@id M) := fun _ ↦ mdifferentiableAt_id

theorem mdifferentiableOn_id : MDiff[s] (@id M) :=
  mdifferentiable_id.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) :=
  (hasMFDerivAt_id x).mfderiv

theorem mfderivWithin_id (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_id hxs]
  exact mfderiv_id

@[simp, mfld_simps]
theorem tangentMap_id : tangentMap% (@id M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]

theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (id : M → M) p = p := by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

end id

section Const

/-! #### Constants -/


variable {c : M'}

theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt% (fun _ : M ↦ c) x (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  ⟨by fun_prop, by simp [Function.comp_def, hasFDerivWithinAt_const]⟩

theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivAt[s] (fun _ : M ↦ c) x (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).hasMFDerivWithinAt

theorem mdifferentiableAt_const : MDiffAt (fun _ : M ↦ c) x :=
  (hasMFDerivAt_const c x).mdifferentiableAt

theorem mdifferentiableWithinAt_const : MDiffAt[s] (fun _ : M ↦ c) x :=
  mdifferentiableAt_const.mdifferentiableWithinAt

theorem mdifferentiable_const : MDiff fun _ : M ↦ c := fun _ ↦ mdifferentiableAt_const

theorem mdifferentiableOn_const : MDiff[s] (fun _ : M ↦ c) :=
  mdifferentiable_const.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_const :
    mfderiv% (fun _ : M ↦ c) x = (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).mfderiv

theorem mfderivWithin_const :
    mfderiv[s] (fun _ : M ↦ c) x = (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivWithinAt_const _ _ _).mfderivWithin_eq_zero

end Const

section Prod

/-! ### Operations on the product of two manifolds -/

theorem MDifferentiableWithinAt.prodMk {f : M → M'} {g : M → M''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDiffAt[s] (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` within `s` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg` within `s`. -/
theorem HasMFDerivWithinAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace% x →L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt[s] f x df)
    {dg : TangentSpace% x →L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt[s] g x dg) :
    HasMFDerivAt[s] (fun y ↦ (f y, g y)) x
      ((tangentSpaceProd I' I'' (f x, g x)).symm.toContinuousLinearMap ∘L (df.prod dg)) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

lemma mfderivWithin_prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] (fun x ↦ (f x, g x)) x =
      (tangentSpaceProd I' I'' (f x, g x)).symm.toContinuousLinearMap
        ∘L ((mfderiv[s] f x).prod (mfderiv[s] g x)) :=
  (hf.hasMFDerivWithinAt.prodMk hg.hasMFDerivWithinAt).mfderivWithin hs

lemma mfderiv_prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mfderiv% (fun x ↦ (f x, g x)) x =
      (tangentSpaceProd I' I'' (f x, g x)).symm.toContinuousLinearMap
        ∘L ((mfderiv% f x).prod (mfderiv% g x)) := by
  simp_rw [← mfderivWithin_univ]
  exact mfderivWithin_prodMk hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I)

theorem MDifferentiableAt.prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDiffAt (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg`. -/
theorem HasMFDerivAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace% x →L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt% f x df)
    {dg : TangentSpace% x →L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt% g x dg) :
    HasMFDerivAt% (fun y ↦ (f y, g y)) x
      ((tangentSpaceProd I' I'' (f x, g x)).symm.toContinuousLinearMap ∘L (df.prod dg)) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableWithinAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableOn.prodMk {f : M → M'} {g : M → M''} (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (fun x ↦ (f x, g x)) := fun x hx ↦ (hf x hx).prodMk (hg x hx)

theorem MDifferentiable.prodMk {f : M → M'} {g : M → M''} (hf : MDiff f) (hg : MDiff g) :
    MDiff fun x ↦ (f x, g x) := fun x ↦ (hf x).prodMk (hg x)

theorem MDifferentiableOn.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prodMk_space (hg x hx)

theorem MDifferentiable.prodMk_space {f : M → E'} {g : M → E''} (hf : MDiff f) (hg : MDiff g) :
    MDifferentiable I 𝓘(𝕜, E' × E'') fun x ↦ (f x, g x) :=
fun x ↦ (hf x).prodMk_space (hg x)

theorem hasMFDerivAt_fst (x : M × M') :
    HasMFDerivAt% (@Prod.fst M M') x
      ((ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap)) := by
  refine ⟨continuous_fst.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I x.1).right_inv hy.1
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  -- Porting note: next line was `simp only [mfld_simps]`
  exact (extChartAt I x.1).right_inv <| (extChartAt I x.1).map_source (mem_extChartAt_source _)

theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.fst M M') x
      ((ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap)) :=
  (hasMFDerivAt_fst x).hasMFDerivWithinAt

theorem mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Prod.fst M M') x :=
  (hasMFDerivAt_fst x).mdifferentiableAt

theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.fst M M') x :=
  mdifferentiableAt_fst.mdifferentiableWithinAt

theorem mdifferentiable_fst : MDiff (@Prod.fst M M') := fun _ ↦ mdifferentiableAt_fst

theorem mdifferentiableOn_fst {s : Set (M × M')} : MDiff[s] (@Prod.fst M M') :=
  mdifferentiable_fst.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_fst {x : M × M'} :
    mfderiv% (@Prod.fst M M') x =
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap) :=
  (hasMFDerivAt_fst x).mfderiv

theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.fst M M') x =
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_fst hxs]; exact mfderiv_fst

@[simp, mfld_simps]
theorem tangentMap_prodFst {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.fst M M') p = ⟨p.proj.1, (tangentSpaceProd I I' p.proj p.2).1⟩ := by
  simp [tangentMap]

theorem tangentMapWithin_prodFst {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.fst M M') p = ⟨p.proj.1, (tangentSpaceProd I I' p.proj p.2).1⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs

theorem hasMFDerivAt_snd (x : M × M') :
    HasMFDerivAt% (@Prod.snd M M') x
      ((ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap)) := by
  refine ⟨continuous_snd.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I' x.2).right_inv hy.2
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  -- Porting note: the next line was `simp only [mfld_simps]`
  exact (extChartAt I' x.2).right_inv <| (extChartAt I' x.2).map_source (mem_extChartAt_source _)

theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.snd M M') x
      ((ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap)) :=
  (hasMFDerivAt_snd x).hasMFDerivWithinAt

theorem mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Prod.snd M M') x :=
  (hasMFDerivAt_snd x).mdifferentiableAt

theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.snd M M') x := mdifferentiableAt_snd.mdifferentiableWithinAt

theorem mdifferentiable_snd : MDiff (@Prod.snd M M') := fun _ ↦ mdifferentiableAt_snd

theorem mdifferentiableOn_snd {s : Set (M × M')} : MDiff[s] (@Prod.snd M M') :=
  mdifferentiable_snd.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_snd {x : M × M'} :
    mfderiv% (@Prod.snd M M') x =
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap) :=
  (hasMFDerivAt_snd x).mfderiv

theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.snd M M') x =
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) ∘L
        (tangentSpaceProd I I' x).toContinuousLinearMap) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_snd hxs]; exact mfderiv_snd

theorem MDifferentiableWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : MDiffAt[s] f x) : MDiffAt[s] (fun x ↦ (f x).1) x :=
  mdifferentiableAt_fst.comp_mdifferentiableWithinAt x hf

theorem MDifferentiableAt.fst {f : N → M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (f x).1) x :=
  mdifferentiableAt_fst.comp x hf

theorem MDifferentiable.fst {f : N → M × M'} (hf : MDiff f) : MDiff fun x ↦ (f x).1 :=
  mdifferentiable_fst.comp hf

theorem MDifferentiableWithinAt.snd {f : N → M × M'} {s : Set N} {x : N} (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ (f x).2) x :=
  mdifferentiableAt_snd.comp_mdifferentiableWithinAt x hf

theorem MDifferentiableAt.snd {f : N → M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (f x).2) x :=
  mdifferentiableAt_snd.comp x hf

theorem MDifferentiable.snd {f : N → M × M'} (hf : MDiff f) : MDiff fun x ↦ (f x).2 :=
  mdifferentiable_snd.comp hf

theorem mdifferentiableWithinAt_prod_iff (f : M → M' × N') :
    MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

section prod_module

-- `F₁` and `F₂` are normed spaces.
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {s : Set M} {x : M}

theorem mdifferentiableWithinAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₁ × F₂) f s x ↔
      MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_iff (f : M → M' × N') :
    MDiffAt f x ↔ MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableAt I 𝓘(𝕜, F₁ × F₂) f x ↔
      MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f

theorem mdifferentiableOn_prod_iff (f : M → M' × N') :
    MDiff[s] f ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx ↦ (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

theorem mdifferentiableOn_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableOn I 𝓘(𝕜, F₁ × F₂) f s ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f

theorem mdifferentiable_prod_iff (f : M → M' × N') :
    MDiff f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ by convert! h.1.prodMk h.2⟩

theorem mdifferentiable_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiable I 𝓘(𝕜, F₁ × F₂) f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f

end prod_module


section prodMap

variable {f : M → M'} {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem MDifferentiableWithinAt.prodMap' {p : M × N}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[r] g p.2) :
    MDiffAt[s ×ˢ r] (Prod.map f g) p :=
  (hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiableWithinAt.prodMap (hf : MDiffAt[s] f x) (hg : MDiffAt[r] g y) :
    MDiffAt[s ×ˢ r] (Prod.map f g) (x, y) :=
  hf.prodMap' hg

theorem MDifferentiableAt.prodMap (hf : MDiffAt f x) (hg : MDiffAt g y) :
    MDiffAt (Prod.map f g) (x, y) := by
  rw [← mdifferentiableWithinAt_univ] at *
  convert! hf.prodMap hg
  exact univ_prod_univ.symm

/-- Variant of `MDifferentiableAt.prod_map` in which the point in the product is given as `p`
instead of a pair `(x, y)`. -/
theorem MDifferentiableAt.prodMap' {p : M × N}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) : MDiffAt (Prod.map f g) p :=
  hf.prodMap hg

theorem MDifferentiableOn.prodMap (hf : MDiff[s] f) (hg : MDiff[r] g) :
    MDiff[s ×ˢ r] (Prod.map f g) :=
  (hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiable.prodMap (hf : MDiff f) (hg : MDiff g) : MDiff (Prod.map f g) := fun p ↦
  (hf p.1).prodMap' (hg p.2)

lemma HasMFDerivWithinAt.prodMap {s : Set <| M × M'} {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace% p.1 →L[𝕜] TangentSpace% (f p.1)}
    (hf : HasMFDerivAt[Prod.fst '' s] f p.1 df)
    {dg : TangentSpace% p.2 →L[𝕜] TangentSpace% (g p.2)}
    (hg : HasMFDerivAt[Prod.snd '' s] g p.2 dg) :
    HasMFDerivAt[s] (Prod.map f g) p
      ((tangentSpaceProd J J' (Prod.map f g p)).symm.toContinuousLinearMap ∘L
        ((df.prodMap dg) ∘L (tangentSpaceProd I I' p).toContinuousLinearMap)) := by
  refine ⟨hf.1.prodMap hg.1 |>.mono (by grind), ?_⟩
  have better : ((extChartAt (I.prod I') p).symm ⁻¹' s ∩ range ↑(I.prod I')) ⊆
      ((extChartAt I p.1).symm ⁻¹' (Prod.fst '' s) ∩ range I) ×ˢ
        ((extChartAt I' p.2).symm ⁻¹' (Prod.snd '' s) ∩ range I') := by
    simp only [mfld_simps]
    rw [range_prodMap, I.toPartialEquiv.prod_symm, (chartAt H p.1).toPartialEquiv.prod_symm]
    intro p₀ ⟨hp₀, ⟨hp₁₁, hp₁₂⟩⟩
    exact ⟨⟨by simp_all; grind, by assumption⟩, ⟨by simp_all; grind, by assumption⟩⟩
  rw [writtenInExtChartAt_prod]
  refine HasFDerivWithinAt.mono ?_ better
  exact HasFDerivWithinAt.prodMap (extChartAt (I.prod I') p p)
    (hf.2.mono (fst_image_prod_subset ..)) (hg.2.mono (snd_image_prod_subset ..))

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace% p.1 →L[𝕜] TangentSpace% (f p.1)} (hf : HasMFDerivAt% f p.1 df)
    {dg : TangentSpace% p.2 →L[𝕜] TangentSpace% (g p.2)} (hg : HasMFDerivAt% g p.2 dg) :
    HasMFDerivAt% (Prod.map f g) p
      ((tangentSpaceProd J J' (Prod.map f g p)).symm.toContinuousLinearMap ∘L
        (((mfderiv% f p.1).prodMap (mfderiv% g p.2)) ∘L
          (tangentSpaceProd I I' p).toContinuousLinearMap)) := by
  simp_rw [← hasMFDerivWithinAt_univ, ← mfderivWithin_univ, ← univ_prod_univ]
  convert! hf.hasMFDerivWithinAt.prodMap hg.hasMFDerivWithinAt
  · rw [mfderivWithin_univ]; exact hf.mfderiv
  · rw [mfderivWithin_univ]; exact hg.mfderiv

-- Note: this lemma does not apply easily to an arbitrary subset `s ⊆ M × M'` as
-- unique differentiability on `(Prod.fst '' s)` and `(Prod.snd '' s)` does not imply
-- unique differentiability on `s`: a priori, `(Prod.fst '' s) × (Prod.fst '' s)`
-- could be a strict superset of `s`.
lemma mfderivWithin_prodMap {p : M × M'} {t : Set M'} {f : M → N} {g : M' → N'}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[t] g p.2)
    (hs : UniqueMDiffAt[s] p.1) (ht : UniqueMDiffAt[t] p.2) :
    mfderiv[s ×ˢ t] (Prod.map f g) p =
      (tangentSpaceProd J J' (Prod.map f g p)).symm.toContinuousLinearMap ∘L
        (((mfderiv[s] f p.1).prodMap (mfderiv[t] g p.2)) ∘L
          (tangentSpaceProd I I' p).toContinuousLinearMap) := by
  have hf' : HasMFDerivAt[Prod.fst '' s ×ˢ t] f p.1 (mfderiv[s] f p.1) :=
    hf.hasMFDerivWithinAt.mono (by grind)
  have hg' : HasMFDerivAt[Prod.snd '' s ×ˢ t] g p.2 (mfderiv[t] g p.2) :=
    hg.hasMFDerivWithinAt.mono (by grind)
  exact (hf'.prodMap hg').mfderivWithin (hs.prod ht)

lemma mfderiv_prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) :
    mfderiv% (Prod.map f g) p =
      (tangentSpaceProd J J' (Prod.map f g p)).symm.toContinuousLinearMap ∘L
        (((mfderiv% f p.1).prodMap (mfderiv% g p.2)) ∘L
          (tangentSpaceProd I I' p).toContinuousLinearMap) := by
  simp_rw [← mfderivWithin_univ, ← univ_prod_univ]
  exact mfderivWithin_prodMap hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I) (uniqueMDiffWithinAt_univ I')

end prodMap

@[simp, mfld_simps]
theorem tangentMap_prodSnd {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.snd M M') p = ⟨p.proj.2, (tangentSpaceProd I I' p.proj p.2).2⟩ := by
  simp [tangentMap]

theorem tangentMapWithin_prodSnd {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.snd M M') p = ⟨p.proj.2, (tangentSpaceProd I I' p.proj p.2).2⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd hs]
  rcases p with ⟨⟩; rfl

-- Kept as an alias for discoverability.
alias MDifferentiableAt.mfderiv_prod := mfderiv_prodMk

theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (x : M) ↦ (x, y₀)) x₀ =
      (tangentSpaceProd I I' (x₀, y₀)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inl 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_id.mfderiv_prod mdifferentiableAt_const).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inl]
  rfl

-- TODO: better error when the type of x is left open
theorem tangentMap_prod_left {p : TangentBundle I M} {y₀ : M'} :
    tangentMap% (fun (x : M) ↦ (x, y₀)) p =
      ⟨(p.1, y₀), (tangentSpaceProd I I' (p.1, y₀)).symm (p.2, 0)⟩ := by
  simp only [tangentMap, mfderiv_prod_left]
  rfl

theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (y : M') ↦ (x₀, y)) y₀ =
      (tangentSpaceProd I I' (x₀, y₀)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inr 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_id).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inr]
  rfl

theorem tangentMap_prod_right {p : TangentBundle I' M'} {x₀ : M} :
    tangentMap% (fun (y : M') ↦ (x₀, y)) p =
      ⟨(x₀, p.1), (tangentSpaceProd I I' (x₀, p.1)).symm (0, p.2)⟩ := by
  simp only [tangentMap, mfderiv_prod_right]
  rfl

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. -/
theorem mfderiv_prod_eq_add {f : M × M' → M''} {p : M × M'}
    (hf : MDiffAt f p) :
    mfderiv% f p =
        mfderiv% (fun z : M × M' ↦ f (z.1, p.2)) p +
        mfderiv% (fun z : M × M' ↦ f (p.1, z.2)) p := by
  erw [mfderiv_comp_of_eq hf (mdifferentiableAt_fst.prodMk mdifferentiableAt_const) rfl,
    mfderiv_comp_of_eq hf (mdifferentiableAt_const.prodMk mdifferentiableAt_snd) rfl,
    ← ContinuousLinearMap.comp_add,
    mdifferentiableAt_fst.mfderiv_prod mdifferentiableAt_const,
    mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_snd, mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
  convert! ContinuousLinearMap.comp_id <| mfderiv% f (p.1, p.2)
  ext v
  apply (tangentSpaceProd I I' (p.1, p.2)).injective
  simp

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
theorem mfderiv_prod_eq_add_comp {f : M × M' → M''} {p : M × M'} (hf : MDiffAt f p) :
    mfderiv% f p =
        (mfderiv% (fun z : M ↦ f (z, p.2)) p.1) ∘L
          (ContinuousLinearMap.fst 𝕜 (TangentSpace% p.1) (TangentSpace% p.2) ∘L
            (tangentSpaceProd I I' p).toContinuousLinearMap) +
        (mfderiv% (fun z : M' ↦ f (p.1, z)) p.2) ∘L
          (ContinuousLinearMap.snd 𝕜 (TangentSpace% p.1) (TangentSpace% p.2) ∘L
            (tangentSpaceProd I I' p).toContinuousLinearMap) := by
  rw [mfderiv_prod_eq_add hf]
  congr
  · change mfderiv% ((fun z : M ↦ f (z, p.2)) ∘ (Prod.fst : M × M' → M)) p = _
    rw [mfderiv_comp (I' := I)]
    · simp only [mfderiv_fst]
    · exact hf.comp _ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    · exact mdifferentiableAt_fst
  · change mfderiv% ((fun z : M' ↦ f (p.1, z)) ∘ (Prod.snd : M × M' → M')) p = _
    rw [mfderiv_comp (I' := I')]
    · simp only [mfderiv_snd]
    · exact hf.comp _ (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    · exact mdifferentiableAt_snd

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
theorem mfderiv_prod_eq_add_apply {f : M × M' → M''} {p : M × M'} {v : TangentSpace% p}
    (hf : MDiffAt f p) :
    mfderiv% f p v =
      mfderiv% (fun z : M ↦ f (z, p.2)) p.1 (tangentSpaceProd I I' p v).1 +
        mfderiv% (fun z : M' ↦ f (p.1, z)) p.2 (tangentSpaceProd I I' p v).2 := by
  rw [mfderiv_prod_eq_add_comp hf]
  rfl

end Prod

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {p : M ⊕ M'}

/-- The canonical identification between the tangent space to `M` at `x` and the tangent space to
`M ⊕ M'` at `Sum.inl x`. This is the derivative of the open embedding `Sum.inl`. -/
@[expose] def tangentSpaceSumInl (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace I (Sum.inl x : M ⊕ M') where
  toFun v := ⟨v.inner⟩
  invFun v := ⟨v.inner⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_induced_dom

/-- The canonical identification between the tangent space to `M'` at `x` and the tangent space to
`M ⊕ M'` at `Sum.inr x`. This is the derivative of the open embedding `Sum.inr`. -/
@[expose] def tangentSpaceSumInr (x : M') :
    TangentSpace I x ≃L[𝕜] TangentSpace I (Sum.inr x : M ⊕ M') where
  toFun v := ⟨v.inner⟩
  invFun v := ⟨v.inner⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_induced_dom

/-- The canonical identification between the tangent spaces to `M ⊕ M'` at `p` and to `M' ⊕ M` at
`Sum.swap p`. This is the derivative of `Sum.swap`. -/
@[expose] def tangentSpaceSumSwap (p : M ⊕ M') :
    TangentSpace I p ≃L[𝕜] TangentSpace I (Sum.swap p) where
  toFun v := ⟨v.inner⟩
  invFun v := ⟨v.inner⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_induced_dom

/-- In extended charts at `p`, `Sum.swap` looks like the identity near `p`. -/
lemma writtenInExtChartAt_sumSwap_eventuallyEq_id :
    writtenInExtChartAt I I p Sum.swap =ᶠ[𝓝[range I] (I <| chartAt H p p)] id := by
  cases p with
    | inl x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inl x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inr_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)
    | inr x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inr x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inr,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inl_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)

theorem hasMFDerivAt_sumSwap :
    HasMFDerivAt% (@Sum.swap M M') p (tangentSpaceSumSwap (I := I) p).toContinuousLinearMap := by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp

@[simp]
theorem mfderivWithin_sumSwap {s : Set (M ⊕ M')} (hs : UniqueMDiffAt[s] p) :
    mfderiv[s] (@Sum.swap M M') p = (tangentSpaceSumSwap p).toContinuousLinearMap :=
  hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin hs

@[simp]
theorem mfderiv_sumSwap :
    mfderiv% (@Sum.swap M M') p = (tangentSpaceSumSwap p).toContinuousLinearMap := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumSwap (uniqueMDiffWithinAt_univ I))

variable {f : M → N} {q : M} {q' : M'}

lemma writtenInExtChartAt_sumInl_eventuallyEq_id :
    (writtenInExtChartAt I I q (@Sum.inl M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q q)] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q).target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inl,
    Sum.inl_injective.extend_apply <| chartAt H q,
    (chartAt H q).right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

lemma writtenInExtChartAt_sumInr_eventuallyEq_id :
    (writtenInExtChartAt I I q' (@Sum.inr M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q' q')] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q').target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q' q') := by
    rw [← I.image_eq (chartAt H q').target]
    exact (chartAt H q').extend_image_target_mem_nhds (mem_chart_source H q')
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inr,
    Sum.inr_injective.extend_apply <| chartAt H q',
    (chartAt H q').right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

theorem hasMFDerivWithinAt_inl :
    HasMFDerivAt[s] (@Sum.inl M M') q
      (tangentSpaceSumInl (I := I) (M' := M') q).toContinuousLinearMap := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q (@Sum.inl M M'))
      =ᶠ[𝓝[(extChartAt I q).symm ⁻¹' s ∩ Set.range I] (extChartAt I q q)] id :=
    writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q q) _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_inl :
    HasMFDerivAt% (@Sum.inl M M') q
      (tangentSpaceSumInl (I := I) (M' := M') q).toContinuousLinearMap := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inl (s := Set.univ)

theorem hasMFDerivWithinAt_inr {t : Set M'} :
    HasMFDerivAt[t] (@Sum.inr M M') q'
      (tangentSpaceSumInr (I := I) (M := M) q').toContinuousLinearMap := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q' (@Sum.inr M M'))
      =ᶠ[𝓝[(extChartAt I q').symm ⁻¹' t ∩ Set.range I] (extChartAt I q' q')] id :=
    writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q' q') _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_inr :
    HasMFDerivAt% (@Sum.inr M M') q'
      (tangentSpaceSumInr (I := I) (M := M) q').toContinuousLinearMap := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inr (t := Set.univ)

theorem mfderivWithin_sumInl (hU : UniqueMDiffAt[s] q) :
    mfderiv[s] (@Sum.inl M M') q = (tangentSpaceSumInl (M' := M') q).toContinuousLinearMap :=
  hasMFDerivWithinAt_inl.mfderivWithin hU

theorem mfderiv_sumInl :
    mfderiv% (@Sum.inl M M') q = (tangentSpaceSumInl (M' := M') q).toContinuousLinearMap := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInl (uniqueMDiffWithinAt_univ I))

theorem mfderivWithin_sumInr {t : Set M'} (hU : UniqueMDiffAt[t] q') :
    mfderiv[t] (@Sum.inr M M') q' = (tangentSpaceSumInr (M := M) q').toContinuousLinearMap :=
  hasMFDerivWithinAt_inr.mfderivWithin hU

theorem mfderiv_sumInr :
    mfderiv% (@Sum.inr M M') q' = (tangentSpaceSumInr (M := M) q').toContinuousLinearMap := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInr (uniqueMDiffWithinAt_univ I))

end disjointUnion

section Arithmetic

/-! #### Arithmetic

The derivative of a map `f : M → E'` with values in a normed space lands in
`TangentSpace 𝓘(𝕜, E') (f z)`, a fiber that depends on the point `f z`. The derivatives of `f`, `g`
and `f + g` therefore live in three different fibers and cannot be added directly. The lemmas below
state the derivatives as maps into `E'` itself, inserting the canonical identification
`NormedSpace.fromTangentSpace` explicitly through `ContinuousLinearMap.toTangentSpaceAt` and
`ContinuousLinearMap.ofTangentSpaceAt`.
-/

section TangentSpaceAt

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

open NormedSpace in
/-- A continuous linear map with values in a normed space `W`, read as a map with values in the
tangent space to `W` at `y`, using the canonical identification `NormedSpace.fromTangentSpace`. -/
@[expose] def ContinuousLinearMap.toTangentSpaceAt (f' : V →L[𝕜] W) (y : W) :
    V →L[𝕜] TangentSpace 𝓘(𝕜, W) y :=
  (fromTangentSpace y).symm.toContinuousLinearMap ∘L f'

open NormedSpace in
/-- A continuous linear map with values in the tangent space to a normed space `W` at `y`, read as
a map with values in `W` itself, using the canonical identification
`NormedSpace.fromTangentSpace`. -/
@[expose] def ContinuousLinearMap.ofTangentSpaceAt {y : W} (f' : V →L[𝕜] TangentSpace 𝓘(𝕜, W) y) :
    V →L[𝕜] W :=
  (fromTangentSpace y).toContinuousLinearMap ∘L f'

namespace ContinuousLinearMap

open NormedSpace in
@[simp]
theorem toTangentSpaceAt_apply (f' : V →L[𝕜] W) (y : W) (v : V) :
    f'.toTangentSpaceAt y v = (fromTangentSpace y).symm (f' v) :=
  rfl

open NormedSpace in
@[simp]
theorem ofTangentSpaceAt_apply {y : W} (f' : V →L[𝕜] TangentSpace 𝓘(𝕜, W) y) (v : V) :
    f'.ofTangentSpaceAt v = fromTangentSpace y (f' v) :=
  rfl

@[simp]
theorem toTangentSpaceAt_ofTangentSpaceAt {y : W} (f' : V →L[𝕜] TangentSpace 𝓘(𝕜, W) y) :
    f'.ofTangentSpaceAt.toTangentSpaceAt y = f' := by
  ext v; simp

@[simp]
theorem ofTangentSpaceAt_toTangentSpaceAt (f' : V →L[𝕜] W) (y : W) :
    (f'.toTangentSpaceAt y).ofTangentSpaceAt = f' := by
  ext v; simp

theorem toTangentSpaceAt_injective (y : W) :
    Function.Injective fun f' : V →L[𝕜] W ↦ f'.toTangentSpaceAt y :=
  fun _ _ h ↦ congrArg ContinuousLinearMap.ofTangentSpaceAt h

end ContinuousLinearMap

open NormedSpace in
/-- If a continuous linear map is surjective, so is the map of tangent spaces it induces
through `ContinuousLinearMap.toTangentSpaceAt`. -/
theorem Function.Surjective.toTangentSpaceAt {f' : V →L[𝕜] W} (hf' : Function.Surjective f')
    (y : W) : Function.Surjective (f'.toTangentSpaceAt y) := fun w ↦
  (hf' (fromTangentSpace y w)).imp fun _ h ↦ by simp [h]

open NormedSpace in
/-- If a continuous linear map is injective, so is the map of tangent spaces it induces
through `ContinuousLinearMap.toTangentSpaceAt`. -/
theorem Function.Injective.toTangentSpaceAt {f' : V →L[𝕜] W} (hf' : Function.Injective f')
    (y : W) : Function.Injective (f'.toTangentSpaceAt y) := fun _ _ h ↦
  hf' ((fromTangentSpace y).symm.injective h)

/-- The derivative of an `MDifferentiableWithinAt` map into a normed space, in the shape used by
the arithmetic lemmas below. -/
theorem MDifferentiableWithinAt.hasMFDerivWithinAt_ofTangentSpaceAt {h : M → W} {z : M}
    {s : Set M} (hh : MDifferentiableWithinAt I 𝓘(𝕜, W) h s z) :
    HasMFDerivWithinAt I 𝓘(𝕜, W) h s z
      ((mfderivWithin I 𝓘(𝕜, W) h s z).ofTangentSpaceAt.toTangentSpaceAt (h z)) := by
  rw [ContinuousLinearMap.toTangentSpaceAt_ofTangentSpaceAt]
  exact hh.hasMFDerivWithinAt

/-- The derivative of an `MDifferentiableAt` map into a normed space, in the shape used by the
arithmetic lemmas below. -/
theorem MDifferentiableAt.hasMFDerivAt_ofTangentSpaceAt {h : M → W} {z : M}
    (hh : MDifferentiableAt I 𝓘(𝕜, W) h z) :
    HasMFDerivAt I 𝓘(𝕜, W) h z
      ((mfderiv I 𝓘(𝕜, W) h z).ofTangentSpaceAt.toTangentSpaceAt (h z)) := by
  rw [ContinuousLinearMap.toTangentSpaceAt_ofTangentSpaceAt]
  exact hh.hasMFDerivAt

end TangentSpaceAt

section Group

variable {z : M} {f g : M → E'} {f' g' : TangentSpace% z →L[𝕜] E'}

theorem HasMFDerivWithinAt.add {s : Set M}
    (hf : HasMFDerivAt[s] f z (f'.toTangentSpaceAt (f z)))
    (hg : HasMFDerivAt[s] g z (g'.toTangentSpaceAt (g z))) :
    HasMFDerivAt[s] (f + g) z ((f' + g').toTangentSpaceAt ((f + g) z)) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem HasMFDerivAt.add (hf : HasMFDerivAt% f z (f'.toTangentSpaceAt (f z)))
    (hg : HasMFDerivAt% g z (g'.toTangentSpaceAt (g z))) :
    HasMFDerivAt% (f + g) z ((f' + g').toTangentSpaceAt ((f + g) z)) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem MDifferentiableWithinAt.add {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f + g) z :=
  (HasMFDerivWithinAt.add (f' := (mfderiv[s] f z).ofTangentSpaceAt)
    (g' := (mfderiv[s] g z).ofTangentSpaceAt)
    hf.hasMFDerivWithinAt hg.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.add (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f + g) z :=
  (HasMFDerivAt.add (f' := (mfderiv% f z).ofTangentSpaceAt)
    (g' := (mfderiv% g z).ofTangentSpaceAt) hf.hasMFDerivAt hg.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.add {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (f + g) :=
  fun x hx ↦ (hf x hx).add (hg x hx)

theorem MDifferentiable.add (hf : MDiff f) (hg : MDiff g) : MDiff (f + g) :=
  fun x ↦ (hf x).add (hg x)

-- TODO: this lemma (and others below) uses the identification of tangent spaces silently
-- Deprecate all these lemmas in favour of a version using `mvfderiv(Within)`
theorem mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f + g) z).ofTangentSpaceAt =
      (mfderiv% f z).ofTangentSpaceAt + (mfderiv% g z).ofTangentSpaceAt :=
  congrArg ContinuousLinearMap.ofTangentSpaceAt
    (HasMFDerivAt.add (f' := (mfderiv% f z).ofTangentSpaceAt)
      (g' := (mfderiv% g z).ofTangentSpaceAt) hf.hasMFDerivAt hg.hasMFDerivAt).mfderiv

theorem mfderivWithin_add (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f + g) z).ofTangentSpaceAt =
      (mfderiv[s] f z).ofTangentSpaceAt + (mfderiv[s] g z).ofTangentSpaceAt :=
  congrArg ContinuousLinearMap.ofTangentSpaceAt
    ((HasMFDerivWithinAt.add (f' := (mfderiv[s] f z).ofTangentSpaceAt)
      (g' := (mfderiv[s] g z).ofTangentSpaceAt)
      hf.hasMFDerivWithinAt hg.hasMFDerivWithinAt).mfderivWithin hs)

section sum
variable {ι : Type} {t : Finset ι} {f : ι → M → E'} {f' : ι → TangentSpace% z →L[𝕜] E'}

lemma HasMFDerivWithinAt.sum
    (hf : ∀ i ∈ t, HasMFDerivAt[s] (f i) z ((f' i).toTangentSpaceAt (f i z))) :
    HasMFDerivAt[s] (∑ i ∈ t, f i) z
      ((∑ i ∈ t, f' i).toTangentSpaceAt ((∑ i ∈ t, f i) z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i s hi IH => grind [HasMFDerivWithinAt.add]

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.sum
    (hf : ∀ i ∈ t, HasMFDerivAt% (f i) z ((f' i).toTangentSpaceAt (f i z))) :
    HasMFDerivAt% (∑ i ∈ t, f i) z ((∑ i ∈ t, f' i).toTangentSpaceAt ((∑ i ∈ t, f i) z)) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf

lemma MDifferentiableWithinAt.sum
    (hf : ∀ i ∈ t, MDiffAt[s] (f i) z) : MDiffAt[s] (∑ i ∈ t, f i) z :=
  (HasMFDerivWithinAt.sum (f' := fun i ↦ (mfderiv[s] (f i) z).ofTangentSpaceAt)
    fun i hi ↦ (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

lemma MDifferentiableAt.sum (hf : ∀ i ∈ t, MDiffAt (f i) z) : MDiffAt (∑ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact .sum hf

lemma MDifferentiableOn.sum (hf : ∀ i ∈ t, MDiff[s] (f i)) : MDiff[s] (∑ i ∈ t, f i) :=
  fun z hz ↦ .sum fun i hi ↦ hf i hi z hz

lemma MDifferentiable.sum (hf : ∀ i ∈ t, MDiff (f i)) : MDiff (∑ i ∈ t, f i) :=
  fun z ↦ .sum fun i hi ↦ hf i hi z

end sum

theorem HasMFDerivWithinAt.const_smul (hf : HasMFDerivAt[s] f z (f'.toTangentSpaceAt (f z)))
    (a : 𝕜) :
    HasMFDerivAt[s] (a • f) z ((a • f').toTangentSpaceAt ((a • f) z)) :=
  ⟨hf.1.const_smul a, hf.2.const_smul a⟩

theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt% f z (f'.toTangentSpaceAt (f z))) (s : 𝕜) :
    HasMFDerivAt% (s • f) z ((s • f').toTangentSpaceAt ((s • f) z)) :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩

theorem MDifferentiableWithinAt.const_smul (hf : MDiffAt[s] f z) (a : 𝕜) : MDiffAt[s] (a • f) z :=
  (HasMFDerivWithinAt.const_smul (f' := (mfderiv[s] f z).ofTangentSpaceAt)
    hf.hasMFDerivWithinAt a).mdifferentiableWithinAt

theorem MDifferentiableAt.const_smul (hf : MDiffAt f z) (s : 𝕜) : MDiffAt (s • f) z :=
  (HasMFDerivAt.const_smul (f' := (mfderiv% f z).ofTangentSpaceAt)
    hf.hasMFDerivAt s).mdifferentiableAt

theorem MDifferentiableOn.const_smul (a : 𝕜) (hf : MDiff[s] f) : MDiff[s] (a • f) :=
  fun x hx ↦ (hf x hx).const_smul a

theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDiff f) : MDiff (s • f) :=
  fun x ↦ (hf x).const_smul s

theorem const_smul_mfderiv (hf : MDiffAt f z) (s : 𝕜) :
    (mfderiv% (s • f) z).ofTangentSpaceAt = s • (mfderiv% f z).ofTangentSpaceAt :=
  congrArg ContinuousLinearMap.ofTangentSpaceAt
    (HasMFDerivAt.const_smul (f' := (mfderiv% f z).ofTangentSpaceAt) hf.hasMFDerivAt s).mfderiv

theorem HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDerivAt[s] f z (f'.toTangentSpaceAt (f z))) :
    HasMFDerivAt[s] (-f) z ((-f').toTangentSpaceAt ((-f) z)) :=
  ⟨hf.1.neg, hf.2.neg⟩

theorem HasMFDerivAt.neg (hf : HasMFDerivAt% f z (f'.toTangentSpaceAt (f z))) :
    HasMFDerivAt% (-f) z ((-f').toTangentSpaceAt ((-f) z)) :=
  ⟨hf.1.neg, hf.2.neg⟩

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_neg :
    HasMFDerivAt% (-f) z ((-f').toTangentSpaceAt ((-f) z)) ↔
      HasMFDerivAt% f z (f'.toTangentSpaceAt (f z)) :=
  ⟨fun hf ↦ by convert! hf.neg <;> rw [neg_neg], fun hf ↦ hf.neg⟩

theorem MDifferentiableWithinAt.neg {s : Set M} (hf : MDiffAt[s] f z) : MDiffAt[s] (-f) z :=
  (HasMFDerivWithinAt.neg (f' := (mfderiv[s] f z).ofTangentSpaceAt)
    hf.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.neg (hf : MDiffAt f z) : MDiffAt (-f) z :=
  (HasMFDerivAt.neg (f' := (mfderiv% f z).ofTangentSpaceAt) hf.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.neg {s : Set M} (hf : MDiff[s] f) : MDiff[s] (-f) :=
  fun x hx ↦ (hf x hx).neg

theorem mdifferentiableWithinAt_neg : MDiffAt[s] (-f) z ↔ MDiffAt[s] f z :=
  ⟨fun hf ↦ by convert hf.neg; rw [neg_neg], fun hf ↦ hf.neg⟩

theorem mdifferentiableAt_neg : MDiffAt (-f) z ↔ MDiffAt f z :=
  ⟨fun hf ↦ by convert! hf.neg; rw [neg_neg], fun hf ↦ hf.neg⟩

theorem MDifferentiable.neg (hf : MDiff f) : MDiff (-f) := fun x ↦ (hf x).neg

set_option backward.isDefEq.respectTransparency false in
theorem mfderivWithin_neg (hs : UniqueMDiffAt[s] x) :
    (mfderiv[s] (-f) x).ofTangentSpaceAt = -(mfderiv[s] f x).ofTangentSpaceAt := by
  by_cases hf : MDiffAt[s] f x
  · exact congrArg ContinuousLinearMap.ofTangentSpaceAt
      ((HasMFDerivWithinAt.neg (f' := (mfderiv[s] f x).ofTangentSpaceAt)
        hf.hasMFDerivWithinAt).mfderivWithin hs)
  · have hf' : ¬ MDiffAt[s] (-f) x := fun h ↦ hf (mdifferentiableWithinAt_neg.1 h)
    simp_rw [mfderivWithin, ite_eq_right hf, ite_eq_right hf']
    ext v
    simp

theorem mfderiv_neg :
    (mfderiv% (-f) x).ofTangentSpaceAt = -(mfderiv% f x).ofTangentSpaceAt := by
  rw [← mfderivWithin_univ, mfderivWithin_neg (uniqueMDiffWithinAt_univ I), mfderivWithin_univ]

theorem HasMFDerivWithinAt.sub (hf : HasMFDerivAt[s] f z (f'.toTangentSpaceAt (f z)))
    (hg : HasMFDerivAt[s] g z (g'.toTangentSpaceAt (g z))) :
    HasMFDerivAt[s] (f - g) z ((f' - g').toTangentSpaceAt ((f - g) z)) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem HasMFDerivAt.sub (hf : HasMFDerivAt% f z (f'.toTangentSpaceAt (f z)))
    (hg : HasMFDerivAt% g z (g'.toTangentSpaceAt (g z))) :
    HasMFDerivAt% (f - g) z ((f' - g').toTangentSpaceAt ((f - g) z)) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem MDifferentiableWithinAt.sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f - g) z :=
  (HasMFDerivWithinAt.sub (f' := (mfderiv[s] f z).ofTangentSpaceAt)
    (g' := (mfderiv[s] g z).ofTangentSpaceAt)
    hf.hasMFDerivWithinAt hg.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.sub (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f - g) z :=
  (HasMFDerivAt.sub (f' := (mfderiv% f z).ofTangentSpaceAt)
    (g' := (mfderiv% g z).ofTangentSpaceAt) hf.hasMFDerivAt hg.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.sub (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (f - g) :=
  fun x hx ↦ (hf x hx).sub (hg x hx)

theorem MDifferentiable.sub (hf : MDiff f) (hg : MDiff g) : MDiff (f - g) :=
  fun x ↦ (hf x).sub (hg x)

theorem mfderivWithin_sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f - g) z).ofTangentSpaceAt =
      (mfderiv[s] f z).ofTangentSpaceAt - (mfderiv[s] g z).ofTangentSpaceAt :=
  congrArg ContinuousLinearMap.ofTangentSpaceAt
    ((HasMFDerivWithinAt.sub (f' := (mfderiv[s] f z).ofTangentSpaceAt)
      (g' := (mfderiv[s] g z).ofTangentSpaceAt)
      hf.hasMFDerivWithinAt hg.hasMFDerivWithinAt).mfderivWithin hs)

theorem mfderiv_sub (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f - g) z).ofTangentSpaceAt =
      (mfderiv% f z).ofTangentSpaceAt - (mfderiv% g z).ofTangentSpaceAt :=
  congrArg ContinuousLinearMap.ofTangentSpaceAt
    (HasMFDerivAt.sub (f' := (mfderiv% f z).ofTangentSpaceAt)
      (g' := (mfderiv% g z).ofTangentSpaceAt) hf.hasMFDerivAt hg.hasMFDerivAt).mfderiv

end Group

section AlgebraOverRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

theorem HasMFDerivWithinAt.mul'
    (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z (p'.toTangentSpaceAt (p z)))
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z (q'.toTangentSpaceAt (q z))) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z
      ((p z • q' + p' <• q z).toTangentSpaceAt ((p * q) z)) :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using! hp.2.mul' hq.2⟩

theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z (p'.toTangentSpaceAt (p z)))
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z (q'.toTangentSpaceAt (q z))) :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z ((p z • q' + p' <• q z).toTangentSpaceAt ((p * q) z)) :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt

theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.hasMFDerivWithinAt_ofTangentSpaceAt.mul'
    hq.hasMFDerivWithinAt_ofTangentSpaceAt).mdifferentiableWithinAt

theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.hasMFDerivAt_ofTangentSpaceAt.mul'
    hq.hasMFDerivAt_ofTangentSpaceAt).mdifferentiableAt

theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s :=
  fun x hx ↦ (hp x hx).mul <| hq x hx

theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) :=
  fun x ↦ (hp x).mul (hq x)

theorem MDifferentiableWithinAt.pow (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (n : ℕ) : MDifferentiableWithinAt I 𝓘(𝕜, F') (p ^ n) s z := by
  induction n with
  | zero => simpa [pow_zero] using! mdifferentiableWithinAt_const
  | succ n hn => simpa [pow_succ] using! hn.mul hp

theorem MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : ℕ) :
    MDifferentiableAt I 𝓘(𝕜, F') (p ^ n) z :=
  mdifferentiableWithinAt_univ.mp (hp.mdifferentiableWithinAt.pow n)

theorem MDifferentiableOn.pow (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : ℕ) :
    MDifferentiableOn I 𝓘(𝕜, F') (p ^ n) s := fun x hx ↦ (hp x hx).pow n

theorem MDifferentiable.pow (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, F') (p ^ n) := fun x ↦ (hp x).pow n

end AlgebraOverRing

section AlgebraOverCommRing

variable {z : M} {F' : Type*} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
theorem HasMFDerivWithinAt.mul
    (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z (p'.toTangentSpaceAt (p z)))
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z (q'.toTangentSpaceAt (q z))) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z
      ((p z • q' + q z • p').toTangentSpaceAt ((p * q) z)) := by
  convert! hp.mul' hq
  ext _
  apply mul_comm

theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z (p'.toTangentSpaceAt (p z)))
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z (q'.toTangentSpaceAt (q z))) :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z ((p z • q' + q z • p').toTangentSpaceAt ((p * q) z)) :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

section prod
variable {ι : Type} {t : Finset ι} {f : ι → M → F'} {f' : ι → TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivWithinAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z ((f' i).toTangentSpaceAt (f i z))) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z
      ((∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)).toTangentSpaceAt ((∏ i ∈ t, f i) z)) := by
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i t hi IH =>
    rw [t.forall_mem_insert] at hf
    have hderiv : ∑ j ∈ insert i t, (∏ k ∈ (insert i t).erase j, f k z) • f' j =
        f i z • (∑ j ∈ t, (∏ k ∈ t.erase j, f k z) • f' j) + (∏ j ∈ t, f j) z • f' i := by
      rw [t.sum_insert hi, t.erase_insert hi, add_comm]
      congr 1
      · simp only [t.smul_sum, ← mul_smul]
        refine t.sum_congr rfl (fun j hj ↦ ?_)
        rw [t.erase_insert_of_ne (by grind), Finset.prod_insert (by grind)]
      · simp
    rw [t.prod_insert hi, hderiv]
    exact hf.1.mul (IH hf.2)

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivAt I 𝓘(𝕜, F') (f i) z ((f' i).toTangentSpaceAt (f i z))) :
    HasMFDerivAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z
      ((∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)).toTangentSpaceAt ((∏ i ∈ t, f i) z)) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.prod hf

lemma MDifferentiableWithinAt.prod
    (hf : ∀ i ∈ t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z := by
  -- `by classical exact` to avoid needing a `DecidableEq` argument
  classical exact (HasMFDerivWithinAt.prod
    fun i hi ↦ (hf i hi).hasMFDerivWithinAt_ofTangentSpaceAt).mdifferentiableWithinAt

lemma MDifferentiableAt.prod (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z) :
    MDifferentiableAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact MDifferentiableWithinAt.prod hf

lemma MDifferentiableOn.prod (hf : ∀ i ∈ t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s) :
    MDifferentiableOn I 𝓘(𝕜, F') (∏ i ∈ t, f i) s :=
  fun z hz ↦ .prod fun i hi ↦ hf i hi z hz

lemma MDifferentiable.prod (hf : ∀ i ∈ t, MDifferentiable I 𝓘(𝕜, F') (f i)) :
    MDifferentiable I 𝓘(𝕜, F') (∏ i ∈ t, f i) :=
  fun z ↦ .prod fun i hi ↦ hf i hi z

end prod

end AlgebraOverCommRing

section DivisionRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedDivisionRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' : TangentSpace% z →L[𝕜] F'}

set_option maxHeartbeats 1000000 in
-- The composition below has to unify the tangent-space wrappers on both sides of `comp`, which is
-- expensive; raising the heartbeat budget is cheaper than restating the lemma.
lemma HasMFDerivWithinAt.inv'
    (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z (p'.toTangentSpaceAt (p z))) (hp_ne : p z ≠ 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z
      ((-((p z)⁻¹ •> p' <• (p z)⁻¹)).toTangentSpaceAt (p⁻¹ z)) :=
  (hasFDerivAt_inv' hp_ne).hasMFDerivAt.comp_hasMFDerivWithinAt (hf := hp)

lemma HasMFDerivAt.inv' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z (p'.toTangentSpaceAt (p z)))
    (hp_ne : p z ≠ 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z ((-((p z)⁻¹ •> p' <• (p z)⁻¹)).toTangentSpaceAt (p⁻¹ z)) :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.inv' hp_ne

lemma MDifferentiableWithinAt.inv (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hp_ne : p z ≠ 0) : MDifferentiableWithinAt I 𝓘(𝕜, F') p⁻¹ s z :=
  (hp.hasMFDerivWithinAt_ofTangentSpaceAt.inv' hp_ne).mdifferentiableWithinAt

lemma MDifferentiableAt.inv (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hp_ne : p z ≠ 0) :
    MDifferentiableAt I 𝓘(𝕜, F') p⁻¹ z :=
  mdifferentiableWithinAt_univ.mp <| hp.mdifferentiableWithinAt.inv hp_ne

theorem MDifferentiableOn.inv (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hp_ne : ∀ z ∈ s, p z ≠ 0) :
    MDifferentiableOn I 𝓘(𝕜, F') p⁻¹ s :=
  fun x hx ↦ (hp x hx).inv (hp_ne x hx)

theorem MDifferentiable.inv (hp : MDifferentiable I 𝓘(𝕜, F') p) (hp_ne : ∀ z, p z ≠ 0) :
    MDifferentiable I 𝓘(𝕜, F') p⁻¹ :=
  fun x ↦ (hp x).inv (hp_ne x)

lemma MDifferentiableWithinAt.div (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) (hq_ne : q z ≠ 0) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p / q) s z := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

lemma MDifferentiableAt.div (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) (hq_ne : q z ≠ 0) :
    MDifferentiableAt I 𝓘(𝕜, F') (p / q) z := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

lemma MDifferentiableOn.div (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) (hq_ne : ∀ z ∈ s, q z ≠ 0) :
    MDifferentiableOn I 𝓘(𝕜, F') (p / q) s := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

lemma MDifferentiable.div (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) (hq_ne : ∀ z, q z ≠ 0) :
    MDifferentiable I 𝓘(𝕜, F') (p / q) := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

end DivisionRing

section Field
open scoped RightActions

variable {z : M} {F' : Type*} [NormedField F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency.types false in
lemma HasMFDerivWithinAt.inv
    (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z (p'.toTangentSpaceAt (p z))) (hp_ne : p z ≠ 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z
      ((-(p z ^ 2)⁻¹ • p').toTangentSpaceAt (p⁻¹ z)) := by
  have hderiv : -(p z ^ 2)⁻¹ • p' = -((p z)⁻¹ •> p' <• (p z)⁻¹) := by
    ext v
    simp
    ring_nf
  rw [hderiv]
  exact hp.inv' hp_ne

lemma HasMFDerivAt.inv (hp : HasMFDerivAt I 𝓘(𝕜, F') p z (p'.toTangentSpaceAt (p z)))
    (hp_ne : p z ≠ 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z ((-(p z ^ 2)⁻¹ • p').toTangentSpaceAt (p⁻¹ z)) :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.inv hp_ne

set_option backward.isDefEq.respectTransparency.types false in
lemma HasMFDerivWithinAt.div
    (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z (p'.toTangentSpaceAt (p z)))
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z (q'.toTangentSpaceAt (q z))) (hq_ne : q z ≠ 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p / q) s z
      (((1 / q z) • p' - (p z / q z ^ 2) • q').toTangentSpaceAt ((p / q) z)) := by
  have hfun : p / q = p * q⁻¹ := by simp [div_eq_mul_inv]
  have hderiv : (1 / q z) • p' - (p z / q z ^ 2) • q' =
      p z • (-(q z ^ 2)⁻¹ • q') + (q z)⁻¹ • p' := by
    ext v
    simp [div_eq_mul_inv]
    ring
  rw [hfun, hderiv]
  exact hp.mul (hq.inv hq_ne)

lemma HasMFDerivAt.div (hp : HasMFDerivAt I 𝓘(𝕜, F') p z (p'.toTangentSpaceAt (p z)))
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z (q'.toTangentSpaceAt (q z))) (hq_ne : q z ≠ 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p / q) z
      (((1 / q z) • p' - (p z / q z ^ 2) • q').toTangentSpaceAt ((p / q) z)) :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.div hq.hasMFDerivWithinAt hq_ne

end Field

end Arithmetic

end SpecificFunctions
