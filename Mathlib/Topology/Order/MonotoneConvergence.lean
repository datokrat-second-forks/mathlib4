/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `IsLUB`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `Prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/

public section

open Filter Set Function
open scoped Topology

variable {α β : Type*}

open OrderDual in
private lemma tendsto_toDual_atBot {ι : Type*} [Preorder ι] :
    Tendsto (toDual : ι → ιᵒᵈ) atBot atTop :=
  tendsto_atTop.2 fun b ↦ mem_of_superset (Iic_mem_atBot (ofDual b)) fun _ hx ↦ hx

open OrderDual in
private lemma tendsto_toDual_atTop {ι : Type*} [Preorder ι] :
    Tendsto (toDual : ι → ιᵒᵈ) atTop atBot :=
  tendsto_atBot.2 fun b ↦ mem_of_superset (Ici_mem_atTop (ofDual b)) fun _ hx ↦ hx

open OrderDual in
private lemma tendsto_ofDual_atTop {ι : Type*} [Preorder ι] :
    Tendsto (ofDual : ιᵒᵈ → ι) atTop atBot :=
  tendsto_atBot.2 fun b ↦ mem_of_superset (Ici_mem_atTop (toDual b)) fun _ hx ↦ hx

open OrderDual in
private lemma tendsto_ofDual_atBot {ι : Type*} [Preorder ι] :
    Tendsto (ofDual : ιᵒᵈ → ι) atBot atTop :=
  tendsto_atTop.2 fun b ↦ mem_of_superset (Iic_mem_atBot (toDual b)) fun _ hx ↦ hx

open OrderDual in
private lemma tendsto_toDual_nhds_iff {β : Type*} [TopologicalSpace α] {l : Filter β} {f : β → α}
    {a : α} : Tendsto (toDual ∘ f) l (𝓝 (toDual a)) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h ↦ (continuous_ofDual.tendsto _).comp h, fun h ↦ (continuous_toDual.tendsto _).comp h⟩

open OrderDual in
private lemma range_toDual_comp {ι : Type*} {f : ι → α} :
    Set.range (toDual ∘ f ∘ ofDual) = ofDual ⁻¹' Set.range f := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨ofDual i, rfl⟩
  · rintro ⟨i, hi⟩
    exact ⟨toDual i, congrArg toDual hi⟩

open OrderDual in
private lemma iSup_comp_ofDual {ι : Type*} [SupSet α] (g : ι → α) :
    ⨆ i : ιᵒᵈ, g (ofDual i) = ⨆ i, g i := by
  simp only [iSup.eq_1]
  congr 1
  exact ofDual.surjective.range_comp g

open OrderDual in
private lemma tendsto_subtype_ofDual [Preorder α] {s : Set αᵒᵈ} :
    Tendsto (fun y : s ↦ (⟨ofDual y.1, y.2⟩ : ↥(toDual ⁻¹' s))) atTop atBot :=
  tendsto_atBot.2 fun b ↦
    mem_of_superset (Ici_mem_atTop (⟨toDual b.1, b.2⟩ : ↥s)) fun _ hx ↦ hx

open OrderDual in
private lemma tendsto_subtype_ofDual' [Preorder α] {s : Set αᵒᵈ} :
    Tendsto (fun y : s ↦ (⟨ofDual y.1, y.2⟩ : ↥(toDual ⁻¹' s))) atBot atTop :=
  tendsto_atTop.2 fun b ↦
    mem_of_superset (Iic_mem_atBot (⟨toDual b.1, b.2⟩ : ↥s)) fun _ hx ↦ hx

/-- We say that `α` is a `SupConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → ∞` (formally, at the filter `Filter.atTop`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atTop_isLUB`.

This property holds for linear orders with order topology as well as their products. -/
class SupConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → ∞` -/
  tendsto_coe_atTop_isLUB :
    ∀ (a : α) (s : Set α), IsLUB s a → Tendsto ((↑) : s → α) atTop (𝓝 a)

/-- We say that `α` is an `InfConvergenceClass` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `Set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `Filter.atBot`). We require this for `ι = (s : Set α)`,
`f = (↑)` in the definition, then prove it for any `f` in `tendsto_atBot_isGLB`.

This property holds for linear orders with order topology as well as their products. -/
class InfConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → -∞` -/
  tendsto_coe_atBot_isGLB :
    ∀ (a : α) (s : Set α), IsGLB s a → Tendsto ((↑) : s → α) atBot (𝓝 a)

instance OrderDual.supConvergenceClass [Preorder α] [TopologicalSpace α] [InfConvergenceClass α] :
    SupConvergenceClass αᵒᵈ :=
  ⟨fun a s ha ↦ (continuous_toDual.tendsto _).comp
    ((InfConvergenceClass.tendsto_coe_atBot_isGLB (OrderDual.ofDual a)
      (OrderDual.toDual ⁻¹' s) (isGLB_preimage_toDual.2 ha)).comp tendsto_subtype_ofDual)⟩

instance OrderDual.infConvergenceClass [Preorder α] [TopologicalSpace α] [SupConvergenceClass α] :
    InfConvergenceClass αᵒᵈ :=
  ⟨fun a s ha ↦ (continuous_toDual.tendsto _).comp
    ((SupConvergenceClass.tendsto_coe_atTop_isLUB (OrderDual.ofDual a)
      (OrderDual.toDual ⁻¹' s) (isLUB_preimage_toDual.2 ha)).comp tendsto_subtype_ofDual')⟩

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.supConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : SupConvergenceClass α := by
  refine ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    lift c to s using hcs
    exact (eventually_ge_atTop c).mono fun x hx => bc.trans_le hx
  · exact Eventually.of_forall fun x => (ha.1 x.2).trans_lt hb

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.infConvergenceClass [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] : InfConvergenceClass α := by
  refine ⟨fun a s ha => tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · exact Eventually.of_forall fun x => hb.trans_le (ha.1 x.2)
  · rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩
    lift c to s using hcs
    exact (eventually_le_atBot c).mono fun x hx => lt_of_le_of_lt (show (x : α) ≤ c from hx) bca

section

variable {ι : Type*} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge

theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by
  have h := tendsto_atTop_isLUB (f := f ∘ OrderDual.ofDual) h_anti.dual_left
    (by rwa [OrderDual.ofDual.surjective.range_comp])
  exact h.comp tendsto_toDual_atBot

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by
  have h := tendsto_atTop_isLUB (f := OrderDual.toDual ∘ f ∘ OrderDual.ofDual) h_mono.dual
    (by rw [range_toDual_comp]; exact ha.dual)
  exact (continuous_ofDual.tendsto _).comp (h.comp tendsto_toDual_atBot)

theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  have h := tendsto_atBot_isLUB (f := OrderDual.toDual ∘ f ∘ OrderDual.ofDual) h_anti.dual
    (by rw [range_toDual_comp]; exact ha.dual)
  exact (continuous_ofDual.tendsto _).comp (h.comp tendsto_toDual_atTop)

end IsGLB

section CiSup

section ConditionallyCompletePartialOrder

variable [ConditionallyCompletePartialOrderSup α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
    exact tendsto_atTop_isLUB h_mono <|
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd

theorem tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by
  have h := tendsto_atTop_ciSup (f := f ∘ OrderDual.ofDual) h_anti.dual_left
    (by rwa [OrderDual.ofDual.surjective.range_comp])
  simp only [Function.comp_apply] at h
  rw [iSup_comp_ofDual] at h
  exact h.comp tendsto_toDual_atBot

end ConditionallyCompletePartialOrder

section ConditionallyCompleteLattice

theorem tendsto_finsetSup_ciSup {ι} [ConditionallyCompleteLattice α] [OrderBot α]
    [SupConvergenceClass α] [Nonempty ι] {a : ι → α} (ha : BddAbove (range a)) :
    Tendsto (fun F : Finset ι => F.sup a) atTop (𝓝 (⨆ i, a i)) := by
  simpa [ciSup_eq_ciSup_finset ha] using
    tendsto_atTop_ciSup (Finset.monotone_sup a) ha.range_finsetSup

end ConditionallyCompleteLattice

end CiSup

section CiInf

section ConditionallyCompletePartialOrder

variable [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by
  have h := tendsto_atTop_ciSup (f := OrderDual.toDual ∘ f ∘ OrderDual.ofDual) h_mono.dual
    (by rw [range_toDual_comp]; exact hbdd.dual)
  simp only [Function.comp_apply] at h
  rw [iSup_comp_ofDual (fun i ↦ OrderDual.toDual (f i)), ← toDual_iInf] at h
  exact (continuous_ofDual.tendsto _).comp (h.comp tendsto_toDual_atBot)

theorem tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by
  have h := tendsto_atBot_ciSup (f := OrderDual.toDual ∘ f ∘ OrderDual.ofDual) h_anti.dual
    (by rw [range_toDual_comp]; exact hbdd.dual)
  simp only [Function.comp_apply] at h
  rw [iSup_comp_ofDual (fun i ↦ OrderDual.toDual (f i)), ← toDual_iInf] at h
  exact (continuous_ofDual.tendsto _).comp (h.comp tendsto_toDual_atTop)

end ConditionallyCompletePartialOrder

section ConditionallyCompleteLattice

theorem tendsto_finsetInf_ciInf {ι} [ConditionallyCompleteLattice α] [OrderTop α]
    [InfConvergenceClass α] [Nonempty ι] {a : ι → α} (ha : BddBelow (range a)) :
    Tendsto (fun F : Finset ι => F.inf a) atTop (𝓝 (⨅ i, a i)) := by
  simpa [ciInf_eq_ciInf_finset ha] using
    tendsto_atTop_ciInf (Finset.antitone_inf a) ha.range_finsetInf

end ConditionallyCompleteLattice

end CiInf

section iSup

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)

theorem tendsto_finsetSup_iSup {ι} (a : ι → α) :
    Tendsto (fun F : Finset ι => F.sup a) atTop (𝓝 (⨆ i, a i)) := by
  simpa [Finset.sup_eq_iSup, ← iSup_eq_iSup_finset a] using
    tendsto_atTop_iSup (Finset.monotone_sup a)

theorem tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

end iSup

section iInf

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)

theorem tendsto_finsetInf_iInf {ι} (a : ι → α) :
    Tendsto (fun F : Finset ι => F.inf a) atTop (𝓝 (⨅ i, a i)) := by
  simpa [Finset.inf_eq_iInf, ← iInf_eq_iInf_finset a] using
    tendsto_atTop_ciInf (Finset.antitone_inf a) (OrderBot.bddBelow _)

theorem tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

end iInf

end

instance Prod.supConvergenceClass
    [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [SupConvergenceClass α] [SupConvergenceClass β] : SupConvergenceClass (α × β) := by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isLUB_prod, ← range_domRestrict, ← range_domRestrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atTop (𝓝 a) :=
    tendsto_atTop_isLUB (monotone_fst.domRestrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atTop (𝓝 b) :=
    tendsto_atTop_isLUB (monotone_snd.domRestrict s) h.2
  exact A.prodMk_nhds B

instance Prod.infConvergenceClass
    [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β] [InfConvergenceClass α]
    [InfConvergenceClass β] : InfConvergenceClass (α × β) := by
  constructor
  rintro ⟨a, b⟩ s h
  rw [isGLB_prod, ← range_domRestrict, ← range_domRestrict] at h
  have A : Tendsto (fun x : s => (x : α × β).1) atBot (𝓝 a) :=
    tendsto_atBot_isGLB (monotone_fst.domRestrict s) h.1
  have B : Tendsto (fun x : s => (x : α × β).2) atBot (𝓝 b) :=
    tendsto_atBot_isGLB (monotone_snd.domRestrict s) h.2
  exact A.prodMk_nhds B

instance Pi.supConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, SupConvergenceClass (α i)] : SupConvergenceClass (∀ i, α i) := by
  refine ⟨fun f s h => ?_⟩
  simp only [isLUB_pi, ← range_domRestrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atTop_isLUB ((monotone_eval _).domRestrict _) (h i)

instance Pi.infConvergenceClass
    {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, InfConvergenceClass (α i)] : InfConvergenceClass (∀ i, α i) := by
  refine ⟨fun f s h => ?_⟩
  simp only [isGLB_pi, ← range_domRestrict] at h
  exact tendsto_pi_nhds.2 fun i => tendsto_atBot_isGLB ((monotone_eval _).domRestrict _) (h i)

instance Pi.supConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [SupConvergenceClass α] : SupConvergenceClass (ι → α) :=
  supConvergenceClass

instance Pi.infConvergenceClass' {ι : Type*} [Preorder α] [TopologicalSpace α]
    [InfConvergenceClass α] : InfConvergenceClass (ι → α) :=
  Pi.infConvergenceClass

theorem tendsto_atTop_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ ∃ l, Tendsto f atTop (𝓝 l) := by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
  else Or.inl <| tendsto_atTop_atTop_of_monotone' h_mono H

theorem tendsto_atTop_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atTop atBot ∨ ∃ l, Tendsto f atTop (𝓝 l) := by
  rcases tendsto_atTop_of_monotone (f := OrderDual.toDual ∘ f) h_mono.dual_right with h | ⟨l, hl⟩
  · exact Or.inl (tendsto_ofDual_atTop.comp h)
  · exact Or.inr ⟨OrderDual.ofDual l, (continuous_ofDual.tendsto _).comp hl⟩

theorem tendsto_atBot_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atBot atBot ∨ ∃ l, Tendsto f atBot (𝓝 l) := by
  rcases tendsto_atTop_of_antitone (f := f ∘ OrderDual.ofDual) h_mono.dual_left with h | ⟨l, hl⟩
  · exact Or.inl (h.comp tendsto_toDual_atBot)
  · exact Or.inr ⟨l, hl.comp tendsto_toDual_atBot⟩

theorem tendsto_atBot_of_antitone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Antitone f) :
    Tendsto f atBot atTop ∨ ∃ l, Tendsto f atBot (𝓝 l) := by
  rcases tendsto_atTop_of_monotone (f := f ∘ OrderDual.ofDual) h_mono.dual_left with h | ⟨l, hl⟩
  · exact Or.inl (h.comp tendsto_toDual_atBot)
  · exact Or.inr ⟨l, hl.comp tendsto_toDual_atBot⟩

theorem tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMaxOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Monotone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) := by
  constructor <;> intro h
  · exact h.comp hg
  · rcases tendsto_atTop_of_monotone hf with (h' | ⟨l', hl'⟩)
    · exact (not_tendsto_atTop_of_tendsto_nhds h (h'.comp hg)).elim
    · rwa [tendsto_nhds_unique h (hl'.comp hg)]

theorem tendsto_iff_tendsto_subseq_of_antitone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂]
    [Nonempty ι₁] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [NoMinOrder α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : Antitone f)
    (hg : Tendsto φ atTop atTop) : Tendsto f atTop (𝓝 l) ↔ Tendsto (f ∘ φ) atTop (𝓝 l) :=
  (tendsto_toDual_nhds_iff.symm.trans
    (tendsto_iff_tendsto_subseq_of_monotone (f := OrderDual.toDual ∘ f)
      (l := OrderDual.toDual l) hf.dual_right hg)).trans tendsto_toDual_nhds_iff

/-! The next family of results, such as `isLUB_of_tendsto_atTop` and `iSup_eq_of_tendsto`, are
converses to the standard fact that bounded monotone functions converge. They state, that if a
monotone function `f` tends to `a` along `Filter.atTop`, then that value `a` is a least upper bound
for the range of `f`.

Related theorems above (`IsLUB.isLUB_of_tendsto`, `IsGLB.isGLB_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/

theorem Monotone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    f b ≤ a :=
  haveI : Nonempty β := Nonempty.intro b
  _root_.ge_of_tendsto ha ((eventually_ge_atTop b).mono fun _ hxy => hf hxy)

theorem Monotone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual.ge_of_tendsto ((continuous_toDual.tendsto _).comp (ha.comp tendsto_ofDual_atTop))
    (OrderDual.toDual b)

theorem Antitone.le_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) (b : β) :
    a ≤ f b :=
  hf.dual_right.ge_of_tendsto ((continuous_toDual.tendsto _).comp ha) b

theorem Antitone.ge_of_tendsto [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) (b : β) :
    f b ≤ a :=
  hf.dual_right.le_of_tendsto ((continuous_toDual.tendsto _).comp ha) b

theorem isLUB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsLUB (Set.range f) a := by
  constructor
  · rintro _ ⟨b, rfl⟩
    exact hf.ge_of_tendsto ha b
  · exact fun _ hb => le_of_tendsto' ha fun x => hb (Set.mem_range_self x)

theorem isGLB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Monotone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsGLB (Set.range f) a := by
  have h := isLUB_of_tendsto_atTop (f := OrderDual.toDual ∘ f ∘ OrderDual.ofDual) hf.dual
    ((continuous_toDual.tendsto _).comp (ha.comp tendsto_ofDual_atTop))
  rw [range_toDual_comp] at h
  exact isLUB_preimage_ofDual.1 h

theorem isLUB_of_tendsto_atBot [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsCodirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atBot (𝓝 a)) : IsLUB (Set.range f) a := by
  have h := isLUB_of_tendsto_atTop (f := f ∘ OrderDual.ofDual) hf.dual_left
    (ha.comp tendsto_ofDual_atTop)
  rwa [OrderDual.ofDual.surjective.range_comp] at h

theorem isGLB_of_tendsto_atTop [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]
    [Preorder β] [IsDirectedOrder β] [Nonempty β] {f : β → α} {a : α} (hf : Antitone f)
    (ha : Tendsto f atTop (𝓝 a)) : IsGLB (Set.range f) a := by
  have h := isGLB_of_tendsto_atBot (f := f ∘ OrderDual.ofDual) hf.dual_left
    (ha.comp tendsto_ofDual_atBot)
  rwa [OrderDual.ofDual.surjective.range_comp] at h

theorem iSup_eq_of_tendsto {α β} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Monotone f) :
    Tendsto f atTop (𝓝 a) → iSup f = a :=
  tendsto_nhds_unique (tendsto_atTop_iSup hf)

theorem iInf_eq_of_tendsto {α} [TopologicalSpace α] [CompleteLinearOrder α] [OrderTopology α]
    [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} (hf : Antitone f) :
    Tendsto f atTop (𝓝 a) → iInf f = a :=
  tendsto_nhds_unique (tendsto_atTop_iInf hf)

theorem iSup_eq_iSup_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atTop) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)

theorem iInf_eq_iInf_subseq_of_monotone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Monotone f)
    (hφ : Tendsto φ l atBot) : ⨅ i, f i = ⨅ i, f (φ i) :=
  le_antisymm (iInf_mono' fun i => ⟨φ i, le_rfl⟩)
    (iInf_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)

theorem iInf_eq_iInf_subseq_of_antitone {ι₁ ι₂ α : Type*} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atTop) : ⨅ i, f i = ⨅ i, f (φ i) :=
  le_antisymm (iInf_mono' fun i => ⟨φ i, le_rfl⟩)
    (iInf_mono' fun i =>
      Exists.imp (fun j (hj : i ≤ φ j) => hf hj) (hφ.eventually <| eventually_ge_atTop i).exists)
