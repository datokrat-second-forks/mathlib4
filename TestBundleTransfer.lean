/-
The three candidate strategies for `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean`,
miniaturized and worked by hand.

The real problem: on master, `TangentSpace I ≡ (tangentBundleCore I M).Fiber` held
definitionally (both were the synonym `fun _ => E`), so the tangent bundle inherited its
`TopologicalSpace`/`FiberBundle`/`VectorBundle` structure by `inferInstanceAs`. With
`TangentSpace` a one-field structure that identification must become an explicit map.

Dictionary between this file and the real one:

    trivCore B F           ↦  tangentBundleCore I M     (one chart instead of an atlas)
    Vec B F b              ↦  TangentSpace I x          (one-field structure fiber)
    v.inner                ↦  tangentSpaceCastModel     (the canonical identification)
    TotalSpace F (Vec B F) ↦  TangentBundle I M
    Strategy1.toCoreHomeomorph ↦ the identification `TM ≃ₜ core.TotalSpace`

Each strategy has to produce the same three things Tangent.lean needs:
a `TopologicalSpace` on the total space, the `FiberBundle` instance, and (in the real
file) `VectorBundle`/`ContMDiffVectorBundle` on top — the linear/smooth layers follow
the same pattern as the topological one shown here.
-/
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.DeriveOneFieldStructure

open Bundle Topology Set

variable (B F : Type*) [TopologicalSpace B] [TopologicalSpace F]

/-- A one-chart `FiberBundleCore`: the trivial bundle, standing in for
`tangentBundleCore I M`. All the interesting content of the real core (the
`fderiv` coordinate changes) is irrelevant to the transfer question. -/
def trivCore : FiberBundleCore Unit B F where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt _ := ()
  mem_baseSet_at _ := mem_univ _
  coordChange _ _ _ := id
  coordChange_self _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuous_snd.continuousOn
  coordChange_comp _ _ _ _ _ _ := rfl

/-! ## Strategy 1: total-space transfer

Keep the core's bundle *as is*; identify our total space with the core's total space
once, and pull everything back through that identification (`Trivialization.compHomeomorph`
exists for exactly this). Cheapest to set up; the cost is a visible `toCoreHomeomorph`
*residue in every chart formula*, i.e. in the statements downstream files rewrite with. -/

namespace Strategy1

structure Vec (B : Type*) (F : Type*) [TopologicalSpace F] (_b : B) : Type _ where
  inner : F
deriving TopologicalSpace

/-- The identification of the two total spaces: `TM ≃ core.TotalSpace` in the real file.
Round trips are `rfl` by structure eta, as for `TangentSpace`. -/
def toCore : TotalSpace F (Vec B F) ≃ (trivCore B F).TotalSpace where
  toFun p := ⟨p.1, p.2.inner⟩
  invFun p := ⟨p.1, ⟨p.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The topology: induced along the identification — this is
`instance : TopologicalSpace TM` in the real file. -/
instance : TopologicalSpace (TotalSpace F (Vec B F)) :=
  .induced (toCore B F) inferInstance

/-- ... which makes the identification a homeomorphism by construction. -/
def toCoreHomeomorph : TotalSpace F (Vec B F) ≃ₜ (trivCore B F).TotalSpace :=
  (toCore B F).toHomeomorphOfIsInducing ⟨rfl⟩

/-- Trivializations: the core's, pulled back through the homeomorphism.
`Trivialization.compHomeomorph` produces a `Trivialization F (Z.proj ∘ toCoreHomeomorph)`;
that projection is *definitionally* `π F (Vec B F)`, so the ascription is accepted. -/
def localTriv (i : Unit) : Trivialization F (π F (Vec B F)) :=
  ((trivCore B F).localTriv i).compHomeomorph (toCoreHomeomorph B F)

instance : FiberBundle F (Vec B F) where
  -- `toCore ∘ (mk b)` is definitionally `(core's mk b) ∘ inner`, a composition of
  -- inducings; cancel the homeomorphism on the left.
  totalSpaceMk_isInducing' b :=
    ((toCoreHomeomorph B F).isInducing.of_comp_iff).1 <|
      (FiberBundle.totalSpaceMk_isInducing F ((trivCore B F).Fiber) b).comp ⟨rfl⟩
  trivializationAtlas' := Set.range (localTriv B F)
  trivializationAt' _ := localTriv B F ()
  mem_baseSet_trivializationAt' _ := mem_univ _
  trivialization_mem_atlas' _ := ⟨(), rfl⟩

/-- THE COST. This is the shape every `TangentBundle.chartAt`-style lemma takes under
Strategy 1: the identification appears on the right-hand side, forever, and `simp` has to
be taught to see through it in every downstream file. -/
example (i : Unit) (p : TotalSpace F (Vec B F)) :
    localTriv B F i p = (trivCore B F).localTriv i (toCoreHomeomorph B F p) := rfl

end Strategy1

/-! ## Strategy 2: rebuild the construction directly on the family

Do what `FiberBundleCore.toTopologicalSpace`/`.localTriv`/`.fiberBundle` do, but landing
on the family `Vec` instead of the synonym `Z.Fiber` — the fiberwise identification
`ψ x := v.inner` is threaded through the *definitions*, not composed on afterwards.
In the real proposal this is a new general construction
(`FiberBundleCore.fiberBundleOn (E' : B → Type*) (ψ : ∀ x, E' x ≃ F)`, of which today's
`Z.Fiber` bundle is the `ψ = refl` special case); for the one-chart core it collapses
to the few lines below. Charts come out *native to the family*: no residue. -/

namespace Strategy2

structure Vec (B : Type*) (F : Type*) [TopologicalSpace F] (_b : B) : Type _ where
  inner : F
deriving TopologicalSpace

/-- The global chart, defined directly on the family total space. For a general core this
is `Z.localTrivAsPartialEquiv i` with `ψ` inserted at the fiber coordinate. -/
def chart : TotalSpace F (Vec B F) ≃ B × F where
  toFun p := (p.1, p.2.inner)
  invFun x := ⟨x.1, ⟨x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For a general core this is `generateFrom ⋃ i, ...` verbatim as in
`FiberBundleCore.toTopologicalSpace`; with one chart it collapses to `induced`. -/
instance : TopologicalSpace (TotalSpace F (Vec B F)) :=
  .induced (chart B F) inferInstance

def chartHomeomorph : TotalSpace F (Vec B F) ≃ₜ B × F :=
  (chart B F).toHomeomorphOfIsInducing ⟨rfl⟩

def localTriv : Trivialization F (π F (Vec B F)) where
  toOpenPartialHomeomorph := (chartHomeomorph B F).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by simp [Homeomorph.toOpenPartialHomeomorph]
  target_eq := by simp [Homeomorph.toOpenPartialHomeomorph]
  proj_toFun _ _ := rfl

instance : FiberBundle F (Vec B F) where
  -- `chart ∘ mk b` is definitionally `(b, ·.inner)`, an embedding composed with an inducing
  totalSpaceMk_isInducing' b :=
    ((chartHomeomorph B F).isInducing.of_comp_iff).1 <|
      ((isEmbedding_prodMkRight b).toIsInducing.comp ⟨rfl⟩)
  trivializationAtlas' := {localTriv B F}
  trivializationAt' _ := localTriv B F
  mem_baseSet_trivializationAt' _ := mem_univ _
  trivialization_mem_atlas' _ := rfl

/-- THE PAYOFF vs Strategy 1: the chart formula is stated on the family itself — the
analogue of `TangentBundle.chartAt` keeps master's shape, with `.inner` at the fiber
coordinate as the only change. -/
example (p : TotalSpace F (Vec B F)) : localTriv B F p = (p.1, p.2.inner) := rfl

end Strategy2

/-! ## Strategy 3: `FiberPrebundle`

Hand Mathlib's prebundle machinery the *pretrivializations* (bare `PartialEquiv`s targeted
at the family — no topology on the total space needed up front!) and let it manufacture
the topology and the bundle. `VectorPrebundle` is the linear sibling used for the real
`VectorBundle` layer. The cost: the topology arrives as `totalSpaceTopology` (a sup of
coinduced topologies), so any lemma identifying it with something concrete (e.g. the
induced-from-core topology, for interop with files reasoning via the core) is a real
proof obligation instead of `rfl`-adjacent. -/

namespace Strategy3

structure Vec (B : Type*) (F : Type*) [TopologicalSpace F] (_b : B) : Type _ where
  inner : F
deriving TopologicalSpace

/-- Pretrivialization: just the partial equivalence plus openness on the *target* side.
Note no `TopologicalSpace (TotalSpace F (Vec B F))` is in scope yet. -/
def pretriv : Pretrivialization F (π F (Vec B F)) where
  toFun p := (p.1, p.2.inner)
  invFun x := ⟨x.1, ⟨x.2⟩⟩
  source := univ
  target := univ ×ˢ univ
  map_source' _ _ := ⟨mem_univ _, mem_univ _⟩
  map_target' _ _ := mem_univ _
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl
  open_target := isOpen_univ.prod isOpen_univ
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := rfl
  proj_toFun _ _ := rfl

def prebundle : FiberPrebundle F (Vec B F) where
  pretrivializationAtlas := {pretriv B F}
  pretrivializationAt _ := pretriv B F
  mem_base_pretrivializationAt _ := mem_univ _
  pretrivialization_mem_atlas _ := rfl
  continuous_trivChange e he e' he' := by
    rw [mem_singleton_iff] at he he'
    subst he he'
    exact continuousOn_id.congr fun x hx => (pretriv B F).toPartialEquiv.right_inv hx.1
  totalSpaceMk_isInducing b := (isEmbedding_prodMkRight b).toIsInducing.comp ⟨rfl⟩

instance : TopologicalSpace (TotalSpace F (Vec B F)) :=
  (prebundle B F).totalSpaceTopology

instance : FiberBundle F (Vec B F) := (prebundle B F).toFiberBundle

end Strategy3

/-
Summary of the trade, in terms of what Tangent.lean's ~50 broken declarations become:

* Strategy 1 — three instances are ~15 lines; but every statement that identified a
  TM-object with a core-object (`TangentBundle.chartAt`, `trivializationAt_*`, the
  `mfld_simps` normal forms) picks up a `toCoreHomeomorph` composition on its RHS,
  and all downstream rewriting must normalize through it.

* Strategy 2 — needs the general `FiberBundleCore.fiberBundleOn ψ` API first
  (the real analogue of the `chart`/`localTriv` defined by hand above, plus its
  `VectorBundleCore`/smooth versions); in exchange the trivializations are native to
  `TangentSpace` and the repaired statements keep master's shape with `.inner` at the
  fiber coordinate — the residue lives in *definitions*, not in the rewrite set.

* Strategy 3 — least hand-built topology (the prebundle machinery does it), the linear
  layer comes from `VectorPrebundle` similarly; but the resulting topology is only
  *provably*, not definitionally, the core one, and the smooth layer
  (`ContMDiffVectorBundle`, line 326 of Tangent.lean) still needs its own transfer.
-/
