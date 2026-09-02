/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Separation.Regular

/-!
# Left and right limits

We define the (strict) left and right limits of a function.

* `leftLim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `rightLim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).

We develop a comprehensive API for monotone functions. Notably,

* `Monotone.continuousAt_iff_leftLim_eq_rightLim` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `Monotone.countable_not_continuousAt` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

We also port the API to antitone functions.

## TODO

Prove corresponding stronger results for `StrictMono` and `StrictAnti` functions.
-/

@[expose] public section


open Set Filter

open scoped Topology

section

variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.leftLim (f : α → β) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.rightLim (f : α → β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ (f ∘ ⇑OrderDual.ofDual) (OrderDual.toDual a)

open Function

section DualBridge

open OrderDual

private theorem nhdsWithin_toDual {X : Type*} [TopologicalSpace X] (s : Set X) (a : X) :
    𝓝[⇑ofDual ⁻¹' s] (toDual a) = Filter.map toDual (𝓝[s] a) := by
  rw [nhdsWithin, nhdsWithin, nhds_toDual, Filter.map_inf toDual.injective, Filter.map_principal,
    Equiv.image_eq_preimage_symm, OrderDual.toDual_symm_eq]

private theorem nhdsLT_toDual {X : Type*} [TopologicalSpace X] [Preorder X] (a : X) :
    𝓝[<] (toDual a) = Filter.map toDual (𝓝[>] a) := by
  rw [Set.Iio_toDual, nhdsWithin_toDual]

private theorem nhdsLE_toDual {X : Type*} [TopologicalSpace X] [Preorder X] (a : X) :
    𝓝[≤] (toDual a) = Filter.map toDual (𝓝[≥] a) := by
  rw [Set.Iic_toDual, nhdsWithin_toDual]

omit [TopologicalSpace β] in
/-- Transport a `Tendsto` statement along `ofDual` on the source of the function. -/
private theorem tendsto_nhdsLT_toDual [TopologicalSpace α] {f : α → β} {a : α} {l : Filter β} :
    Tendsto (f ∘ ⇑ofDual) (𝓝[<] (toDual a)) l ↔ Tendsto f (𝓝[>] a) l := by
  rw [nhdsLT_toDual, Filter.tendsto_map'_iff]
  rfl

/-- Transport a `Tendsto` statement along `toDual` on the target of the function. -/
private theorem tendsto_toDual_comp_map_iff {X Y : Type*} {F : Filter X} {g : X → Y}
    {G : Filter Y} : Tendsto (⇑toDual ∘ g) F (Filter.map toDual G) ↔ Tendsto g F G := by
  rw [Filter.Tendsto, Filter.Tendsto, ← Filter.map_map, Filter.map_le_map_iff toDual.injective]

private theorem tendsto_toDual_comp_nhds_iff {X Y : Type*} [TopologicalSpace Y] {F : Filter X}
    {g : X → Y} {b : Y} : Tendsto (⇑toDual ∘ g) F (𝓝 (toDual b)) ↔ Tendsto g F (𝓝 b) := by
  rw [nhds_toDual, tendsto_toDual_comp_map_iff]

private theorem tendsto_toDual_comp_nhdsGE_iff {X Y : Type*} [TopologicalSpace Y] [Preorder Y]
    {F : Filter X} {g : X → Y} {b : Y} :
    Tendsto (⇑toDual ∘ g) F (𝓝[≥] (toDual b)) ↔ Tendsto g F (𝓝[≤] b) := by
  rw [Set.Ici_toDual, nhdsWithin_toDual, tendsto_toDual_comp_map_iff]

private theorem tendsto_toDual_comp_nhdsLE_iff {X Y : Type*} [TopologicalSpace Y] [Preorder Y]
    {F : Filter X} {g : X → Y} {b : Y} :
    Tendsto (⇑toDual ∘ g) F (𝓝[≤] (toDual b)) ↔ Tendsto g F (𝓝[≥] b) := by
  rw [nhdsLE_toDual, tendsto_toDual_comp_map_iff]

omit [LinearOrder α] [TopologicalSpace β] in
private theorem comp_ofDual_comp_toDual (f : α → β) : (f ∘ ⇑ofDual) ∘ ⇑toDual = f := rfl

private theorem leftLim_comp_ofDual (f : α → β) (a : α) :
    leftLim (f ∘ ⇑ofDual) (toDual a) = rightLim f a := rfl

private theorem leftLim_comp_ofDual' (f : α → β) :
    leftLim (f ∘ ⇑ofDual) ∘ ⇑toDual = rightLim f := rfl

end DualBridge

theorem leftLim_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} [h : (𝓝[<] a).NeBot] (h' : Tendsto f (𝓝[<] a) (𝓝 y)) :
    leftLim f a = y := by
  have h'' : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, neBot_iff.mp h, h'', not_true, or_self_iff, ite_false]
  exact lim_eq h'

theorem rightLim_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} [h : (𝓝[>] a).NeBot] (h' : Tendsto f (𝓝[>] a) (𝓝 y)) :
    Function.rightLim f a = y := by
  have : (𝓝[<] (OrderDual.toDual a)).NeBot := by rw [nhdsLT_toDual]; exact h.map _
  exact leftLim_eq_of_tendsto (α := αᵒᵈ) (f := f ∘ ⇑OrderDual.ofDual)
    (tendsto_nhdsLT_toDual.2 h')

theorem leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[<] a = ⊥) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

theorem rightLim_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[>] a = ⊥) : rightLim f a = f a :=
  leftLim_eq_of_eq_bot (α := αᵒᵈ) _ (by rw [nhdsLT_toDual, h, Filter.map_bot])

theorem leftLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]

theorem rightLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[>] a) (𝓝 y)) : rightLim f a = f a :=
  leftLim_eq_of_not_tendsto (α := αᵒᵈ) _
    (fun ⟨y, hy⟩ ↦ h ⟨y, tendsto_nhdsLT_toDual.1 hy⟩)

theorem leftLim_eq_of_isBot {f : α → β} {a : α} (ha : IsBot a) :
    leftLim f a = f a := by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLim_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]

theorem rightLim_eq_of_isTop {f : α → β} {a : α} (ha : IsTop a) :
    rightLim f a = f a :=
  leftLim_eq_of_isBot (α := αᵒᵈ) (f := f ∘ ⇑OrderDual.ofDual)
    fun b ↦ ha (OrderDual.ofDual b)

theorem ContinuousWithinAt.leftLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} (hf : ContinuousWithinAt f (Iic a) a) : leftLim f a = f a := by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h']
  apply leftLim_eq_of_tendsto
  exact hf.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)

theorem ContinuousWithinAt.rightLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} (hf : ContinuousWithinAt f (Ici a) a) : rightLim f a = f a :=
  ContinuousWithinAt.leftLim_eq (α := αᵒᵈ) (f := f ∘ ⇑OrderDual.ofDual)
    (show Tendsto _ _ _ by
      rw [Set.Iic_toDual, nhdsWithin_toDual, Filter.tendsto_map'_iff]
      exact hf)

theorem tendsto_leftLim_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α]
    {f : α → β} {a : α} (h : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)) :
    Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a)) := by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLim, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h

theorem tendsto_rightLim_of_tendsto [TopologicalSpace α] [OrderTopology α]
    {f : α → β} {a : α} (h : ∃ y, Tendsto f (𝓝[>] a) (𝓝 y)) :
    Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a)) :=
  tendsto_nhdsLT_toDual.1 (tendsto_leftLim_of_tendsto (α := αᵒᵈ) (f := f ∘ ⇑OrderDual.ofDual)
    (h.imp fun _ hy ↦ tendsto_nhdsLT_toDual.2 hy))

theorem mapClusterPt_leftLim [TopologicalSpace α] [OrderTopology α]
    (f : α → β) (a : α) : MapClusterPt (f.leftLim a) (𝓝[≤] a) f := by
  have A : (𝓝 (f a) ⊓ map f (𝓝[≤] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun s hs s' hs' ↦ ?_)
    refine ⟨f a, mem_of_mem_nhds hs, ?_⟩
    simp only [mem_map] at hs'
    apply mem_of_mem_nhdsWithin self_mem_Iic hs'
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp only [MapClusterPt, ClusterPt, h', leftLim_eq_of_eq_bot, A]
  by_cases! H : ¬ ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)
  · simp [MapClusterPt, ClusterPt, H, leftLim_eq_of_not_tendsto, A]
  have : MapClusterPt (f.leftLim a) (𝓝[<] a) f := (tendsto_leftLim_of_tendsto H).mapClusterPt
  exact MapClusterPt.mono this (nhdsWithin_mono _ Iio_subset_Iic_self)

theorem mapClusterPt_rightLim [TopologicalSpace α] [OrderTopology α]
    (f : α → β) (a : α) : MapClusterPt (f.rightLim a) (𝓝[≥] a) f := by
  have h := mapClusterPt_leftLim (α := αᵒᵈ) (f ∘ ⇑OrderDual.ofDual) (OrderDual.toDual a)
  simpa only [MapClusterPt, nhdsLE_toDual, Filter.map_map, comp_ofDual_comp_toDual,
    leftLim_comp_ofDual] using h

theorem continuousWithinAt_leftLim_Iic [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    ContinuousWithinAt f.leftLim (Iic a) a := by
  have : 𝓝[≤] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
    simp
  rw [ContinuousWithinAt, this, tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  obtain ⟨u, au, hu⟩ : ∃ u, u < a ∧ Ioo u a ⊆ {x | f x ∈ s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[<] c) with h'c | h'c
  · simpa [h'c, leftLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[<] c) (𝓝 y)
  · simpa [leftLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsLT_of_mem ⟨hc.1, hc.2.le⟩] with d hd using hu hd

theorem leftLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    f.leftLim.leftLim a = f.leftLim a :=
  (continuousWithinAt_leftLim_Iic h).leftLim_eq

theorem continuousWithinAt_rightLim_Ici [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    ContinuousWithinAt f.rightLim (Ici a) a := by
  have h' := continuousWithinAt_leftLim_Iic (α := αᵒᵈ) (f := f ∘ ⇑OrderDual.ofDual)
    (tendsto_nhdsLT_toDual.2 h)
  simpa only [ContinuousWithinAt, Set.Iic_toDual, nhdsWithin_toDual, Filter.tendsto_map'_iff,
    leftLim_comp_ofDual, leftLim_comp_ofDual'] using h'

theorem rightLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    f.rightLim.rightLim a = f.rightLim a :=
  (continuousWithinAt_rightLim_Ici h).rightLim_eq

theorem leftLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) [h' : (𝓝[<] a).NeBot] :
    f.rightLim.leftLim a = f.leftLim a := by
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  apply leftLim_eq_of_tendsto
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, au, hu⟩ : ∃ u, u < a ∧ Ioo u a ⊆ {x | f x ∈ s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[>] c) with h'c | h'c
  · simpa [h'c, rightLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[>] c) (𝓝 y)
  · simpa [rightLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_rightLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨hc.1.le, hc.2⟩] with d hd using hu hd

theorem rightLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) [h' : (𝓝[>] a).NeBot] :
    f.leftLim.rightLim a = f.rightLim a := by
  obtain ⟨b, hb⟩ : (Ioi a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  apply rightLim_eq_of_tendsto
  apply (closed_nhds_basis (f.rightLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, au, hu⟩ : ∃ u, a < u ∧ Ioo a u ⊆ {x | f x ∈ s} := by
    have := (closed_nhds_basis (f.rightLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsGT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsGT au] with c hc
  rcases eq_or_neBot (𝓝[<] c) with h'c | h'c
  · simpa [h'c, leftLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[<] c) (𝓝 y)
  · simpa [leftLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsLT_of_mem ⟨hc.1, hc.2.le⟩] with d hd using hu hd

theorem tendsto_atTop_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atTop (𝓝 b)) (h' : ∀ᶠ x in atTop, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atTop (𝓝 b) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atTop]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : ∃ a, ∀ (b : α), a ≤ b → MapClusterPt (g b) (𝓝 b) f ∧ f b ∈ s := by
    simpa [eventually_atTop] using h'.and (h s_mem)
  filter_upwards [Ioi_mem_atTop u] with a (ha : u < a)
  apply s_closed.mem_of_mapClusterPt (hu a ha.le).1
  filter_upwards [Ici_mem_nhds ha] with y hy using (hu y hy).2

theorem tendsto_atBot_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoBotOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atBot (𝓝 b)) (h' : ∀ᶠ x in atBot, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atBot (𝓝 b) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atBot]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : ∃ a, ∀ (b : α), b ≤ a → MapClusterPt (g b) (𝓝 b) f ∧ f b ∈ s := by
    simpa [eventually_atBot] using h'.and (h s_mem)
  filter_upwards [Iio_mem_atBot u] with a (ha : a < u)
  apply s_closed.mem_of_mapClusterPt (hu a ha.le).1
  filter_upwards [Iic_mem_nhds ha] with y hy using (hu y hy).2

theorem tendsto_leftLim_atTop_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoTopOrder α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.leftLim atTop (𝓝 b) := by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
  exact MapClusterPt.mono (mapClusterPt_leftLim _ _) nhdsWithin_le_nhds

theorem tendsto_rightLim_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.rightLim atTop (𝓝 b) := by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : f.rightLim ⊤ = f ⊤ := rightLim_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤), ← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
    exact MapClusterPt.mono (mapClusterPt_rightLim _ _) nhdsWithin_le_nhds

theorem tendsto_rightLim_atBot_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoBotOrder α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.rightLim atBot (𝓝 b) := by
  apply tendsto_atBot_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
  exact MapClusterPt.mono (mapClusterPt_rightLim _ _) nhdsWithin_le_nhds

section DualBridge

open OrderDual

/-- The left limit of `toDual ∘ f` is the right limit of `f`, read in the dual order. -/
private theorem leftLim_toDual_comp [LinearOrder β] [OrderTopology β] (f : α → β) (a : α) :
    leftLim (⇑toDual ∘ f) a = toDual (leftLim f a) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] a) with h | h
  · rw [leftLim_eq_of_eq_bot _ h, leftLim_eq_of_eq_bot _ h]
    rfl
  by_cases H : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)
  · obtain ⟨y, hy⟩ := H
    rw [leftLim_eq_of_tendsto hy, leftLim_eq_of_tendsto ((continuous_toDual.tendsto y).comp hy)]
  · rw [leftLim_eq_of_not_tendsto _ H, leftLim_eq_of_not_tendsto]
    · rfl
    · rintro ⟨z, hz⟩
      exact H ⟨ofDual z, (continuous_ofDual.tendsto z).comp hz⟩

private theorem leftLim_toDual_comp' [LinearOrder β] [OrderTopology β] (f : α → β) :
    leftLim (⇑toDual ∘ f) = ⇑toDual ∘ leftLim f :=
  funext fun a ↦ leftLim_toDual_comp f a

private theorem rightLim_toDual_comp [LinearOrder β] [OrderTopology β] (f : α → β) (a : α) :
    rightLim (⇑toDual ∘ f) a = toDual (rightLim f a) :=
  leftLim_toDual_comp (α := αᵒᵈ) (f ∘ ⇑ofDual) (toDual a)

private theorem rightLim_toDual_comp' [LinearOrder β] [OrderTopology β] (f : α → β) :
    rightLim (⇑toDual ∘ f) = ⇑toDual ∘ rightLim f :=
  funext fun a ↦ rightLim_toDual_comp f a

end DualBridge

theorem tendsto_leftLim_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.leftLim atBot (𝓝 b) := by
  cases botOrderOrNoBotOrder α
  · simp only [OrderBot.atBot_eq α] at h ⊢
    have : f.leftLim ⊥ = f ⊥ := leftLim_eq_of_isBot isBot_bot
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊥), ← this]
    apply tendsto_pure_nhds
  · apply tendsto_atBot_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
    exact MapClusterPt.mono (mapClusterPt_leftLim _ _) nhdsWithin_le_nhds

end

open Function

namespace Monotone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Monotone f) {x y : α}
include hf

theorem leftLim_eq_sSup [TopologicalSpace α] [OrderTopology α] [(𝓝[<] x).NeBot] :
    leftLim f x = sSup (f '' Iio x) :=
  leftLim_eq_of_tendsto (hf.tendsto_nhdsLT x)

theorem rightLim_eq_sInf [TopologicalSpace α] [OrderTopology α] [(𝓝[>] x).NeBot] :
    rightLim f x = sInf (f '' Ioi x) :=
  rightLim_eq_of_tendsto (hf.tendsto_nhdsGT x)

theorem leftLim_le (h : x ≤ y) : leftLim f x ≤ f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simpa [leftLim, h'] using hf h
  rw [leftLim_eq_sSup hf]
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact (forall_mem_nonempty_iff_neBot.2 h') _ self_mem_nhdsWithin
  · simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro z hz
    exact hf (hz.le.trans h)

theorem le_leftLim (h : x < y) : f x ≤ leftLim f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with h' | h'
  · rw [leftLim_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLim_eq_sSup hf]
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_ofPred_eq]
  intro z hz
  exact hf hz.le

@[gcongr, mono]
protected theorem leftLim : Monotone (leftLim f) := by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLim_le le_rfl).trans (hf.le_leftLim hxy)

theorem le_rightLim (h : x ≤ y) : f x ≤ rightLim f y := by
  have h' := hf.dual.leftLim_le (show OrderDual.toDual y ≤ OrderDual.toDual x from h)
  simp only [leftLim_toDual_comp, leftLim_comp_ofDual, Function.comp_apply,
    OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual] at h'
  exact h'

theorem rightLim_le (h : x < y) : rightLim f x ≤ f y := by
  have h' := hf.dual.le_leftLim (show OrderDual.toDual y < OrderDual.toDual x from h)
  simp only [leftLim_toDual_comp, leftLim_comp_ofDual, Function.comp_apply,
    OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual] at h'
  exact h'

@[gcongr, mono]
protected theorem rightLim : Monotone (rightLim f) := fun x y h ↦ by
  have := hf.dual.leftLim (show OrderDual.toDual y ≤ OrderDual.toDual x from h)
  simpa only [leftLim_toDual_comp, leftLim_comp_ofDual, Function.comp_apply,
    OrderDual.toDual_le_toDual] using this

theorem leftLim_le_rightLim (h : x ≤ y) : leftLim f x ≤ rightLim f y :=
  (hf.leftLim_le le_rfl).trans (hf.le_rightLim h)

theorem rightLim_le_leftLim (h : x < y) : rightLim f x ≤ leftLim f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with (h' | h')
  · simpa [leftLim, h'] using rightLim_le hf h
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty := nonempty_of_mem (Ioo_mem_nhdsLT h)
  calc
    rightLim f x ≤ f a := hf.rightLim_le xa
    _ ≤ leftLim f y := hf.le_leftLim ay

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) :=
  tendsto_leftLim_of_tendsto ⟨_, hf.tendsto_nhdsLT x⟩

theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≤] leftLim f x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Iio x)] with y hy using hf.le_leftLim hy

theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  tendsto_rightLim_of_tendsto ⟨_, hf.tendsto_nhdsGT x⟩

theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≥] rightLim f x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_rightLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Ioi x)] with y hy using hf.rightLim_le hy

/-- A monotone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x := by
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLim x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLim x
  rwa [h] at this

/-- A monotone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x := by
  rcases eq_or_neBot (𝓝[>] x) with h' | h'
  · simp [rightLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_rightLim x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_rightLim x
  rwa [h] at this

/-- A monotone function is continuous at a point if and only if its left and right limits
coincide. -/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have A : leftLim f x = f x :=
      hf.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousWithinAt
    have B : rightLim f x = f x :=
      hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 h.continuousWithinAt
    exact A.trans B.symm
  · have h' : leftLim f x = f x := by
      apply le_antisymm (leftLim_le hf (le_refl _))
      rw [h]
      exact le_rightLim hf (le_refl _)
    refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
    · exact hf.continuousWithinAt_Iio_iff_leftLim_eq.2 h'
    · rw [h] at h'
      exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.2 h'

end Monotone

namespace Antitone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Antitone f) {x y : α}
include hf

theorem le_leftLim (h : x ≤ y) : f y ≤ leftLim f x := by
  have := hf.dual_right.leftLim_le h
  simpa only [leftLim_toDual_comp, Function.comp_apply, OrderDual.toDual_le_toDual] using this

theorem leftLim_le (h : x < y) : leftLim f y ≤ f x := by
  have := hf.dual_right.le_leftLim h
  simpa only [leftLim_toDual_comp, Function.comp_apply, OrderDual.toDual_le_toDual] using this

@[gcongr, mono]
protected theorem leftLim : Antitone (leftLim f) := by
  have := hf.dual_right.leftLim
  rwa [leftLim_toDual_comp'] at this

theorem rightLim_le (h : x ≤ y) : rightLim f y ≤ f x := by
  have := hf.dual_right.le_rightLim h
  simpa only [rightLim_toDual_comp, Function.comp_apply, OrderDual.toDual_le_toDual] using this

theorem le_rightLim (h : x < y) : f y ≤ rightLim f x := by
  have := hf.dual_right.rightLim_le h
  simpa only [rightLim_toDual_comp, Function.comp_apply, OrderDual.toDual_le_toDual] using this

@[gcongr, mono]
protected theorem rightLim : Antitone (rightLim f) := by
  have := hf.dual_right.rightLim
  rwa [rightLim_toDual_comp'] at this

theorem rightLim_le_leftLim (h : x ≤ y) : rightLim f y ≤ leftLim f x := by
  have := hf.dual_right.leftLim_le_rightLim h
  simpa only [leftLim_toDual_comp, rightLim_toDual_comp, OrderDual.toDual_le_toDual] using this

theorem leftLim_le_rightLim (h : x < y) : leftLim f y ≤ rightLim f x := by
  have := hf.dual_right.rightLim_le_leftLim h
  simpa only [leftLim_toDual_comp, rightLim_toDual_comp, OrderDual.toDual_le_toDual] using this

variable [TopologicalSpace α] [OrderTopology α]

theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) := by
  have := hf.dual_right.tendsto_leftLim x
  rwa [leftLim_toDual_comp, tendsto_toDual_comp_nhds_iff] at this

theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≥] leftLim f x) := by
  have := hf.dual_right.tendsto_leftLim_within x
  rwa [leftLim_toDual_comp, tendsto_toDual_comp_nhdsLE_iff] at this

theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) := by
  have := hf.dual_right.tendsto_rightLim x
  rwa [rightLim_toDual_comp, tendsto_toDual_comp_nhds_iff] at this

theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≤] rightLim f x) := by
  have := hf.dual_right.tendsto_rightLim_within x
  rwa [rightLim_toDual_comp, tendsto_toDual_comp_nhdsGE_iff] at this

/-- An antitone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x := by
  have := hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq (x := x)
  simpa only [ContinuousWithinAt, Function.comp_apply, tendsto_toDual_comp_nhds_iff,
    leftLim_toDual_comp, OrderDual.toDual_inj] using this

/-- An antitone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x := by
  have := hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq (x := x)
  simpa only [ContinuousWithinAt, Function.comp_apply, tendsto_toDual_comp_nhds_iff,
    rightLim_toDual_comp, OrderDual.toDual_inj] using this

/-- An antitone function is continuous at a point if and only if its left and right limits
coincide. -/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x := by
  have := hf.dual_right.continuousAt_iff_leftLim_eq_rightLim (x := x)
  simpa only [ContinuousAt, Function.comp_apply, tendsto_toDual_comp_nhds_iff,
    leftLim_toDual_comp, rightLim_toDual_comp, OrderDual.toDual_inj] using this

end Antitone
