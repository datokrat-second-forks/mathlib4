/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Exact.Sequence
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
meta import Lean.PostprocessTraces

/-!
# The index of a linear map

In this file we define the index of a linear map and provide some basic API.

## Main definitions / results:

* `LinearMap.index`: the index of a linear map, with sign convention `index = dim ker - dim coker`.
* `LinearMap.index_comp`: the index is additive under composition.

-/

noncomputable section

namespace LinearMap

open Function Module

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

section Ring

variable {R : Type*} [Ring R] [Module R M] [Module R N] (f : M →ₗ[R] N)

/-- The index of a linear map with sign convention `index = dim ker - dim coker`.

In the case that either the kernel or cokernel has infinite rank, the value is junk. -/
public def index : ℤ := finrank R f.ker - finrank R (N ⧸ f.range)

variable {f}

public lemma index_eq_finrank_sub :
    f.index = finrank R f.ker - finrank R (N ⧸ f.range) := by
  rfl

@[nontriviality] public lemma index_of_subsingleton [Subsingleton R] :
    f.index = 0 := by
  simp [index_eq_finrank_sub]

@[simp] public lemma index_zero :
    (0 : M →ₗ[R] N).index = finrank R M - finrank R N := by
  rw [index_eq_finrank_sub, ker_zero, range_zero]
  simpa using (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

public lemma index_of_injective [Nontrivial R] (hf : Injective f) :
    f.index = - finrank R (N ⧸ f.range) := by
  simpa [index_eq_finrank_sub] using ker_eq_bot.2 hf ▸ finrank_bot _ _

variable [StrongRankCondition R]

public lemma index_of_surjective (hf : Surjective f) :
    f.index = finrank R f.ker := by
  rw [index_eq_finrank_sub, range_eq_top.mpr hf]
  simp [finrank_eq_zero_of_subsingleton]

/-
tl;dr: Making `ker` implicit-reducible helps.

---

`index_id` needs `backward.isDefEq.instanceTypes "none"` (kept together with
`respectTransparency.types false`) for its closing `simp [finrank_eq_zero_of_subsingleton]`.
The mode used by the actual build is `"markOrSynth"` (set globally in `lakefile.lean`); the
load-bearing rejection is in that mode's fallback synthesis leg.

Trigger chain. After `nontriviality R` (whose `Subsingleton R` branch is discharged by the
`@[nontriviality]` lemma `index_of_subsingleton`) and `rw [index_eq_finrank_sub, range_id]`,
the goal is `(finrank R ↥(ker id) : ℤ) - finrank R (M ⧸ ⊤) = 0`. Inside the final `simp`,
the `@[simp]` lemma `ker_id : ker (id : M →ₗ[R] M) = ⊥` — which holds by `rfl` — rewrites the
*carrier* `↥(ker id)` to `↥⊥`, but simp's congruence for `Module.finrank` reuses the original
instance arguments, still spelled `id.ker.addCommMonoid`, `id.ker.module` (i.e. at the old
carrier `↥id.ker`). Simp may reuse them because `↥id.ker` and `↥⊥` are defeq at default
transparency (`ker_id` is `rfl`; see `demoDefeqDefaultButNotReducible`). The resulting subterm
is `@finrank R ↥⊥ _ id.ker.addCommMonoid id.ker.module`.

The rejected assignment. `finrank_eq_zero_of_subsingleton` carries `[Module.Free R M]`. To
discharge `Module.Free R ↥⊥` — whose `AddCommMonoid`/`Module` arguments are the inherited
`id.ker.*` — instance synthesis tries `Free.of_subsingleton`, reproducing the module structure
in instance-typed metavariables. The load-bearing rejection (see `demoFreeSynthFails`) is
  ❌ (?m.75 : AddCommMonoid ↥⊥) := (id.ker.addCommMonoid : AddCommMonoid ↥id.ker).

Which `markOrSynth` leg fails, and why. This is leg (c), the fallback-synthesis leg. The
direct check first compares `AddCommMonoid ↥⊥ =?= AddCommMonoid ↥id.ker` at `.instances`,
where neither `LinearMap.ker` nor `LinearMap.id` unfolds — both are ordinary
(non-reducible, non-instance) defs, and `ker_id` is only a `rfl`-lemma, not a reduction
available at `.instances` — so it fails. The fallback then *synthesizes* `AddCommMonoid ↥⊥`,
which succeeds, yielding `⊥.addCommMonoid`; but the candidate `id.ker.addCommMonoid` is not
definitionally equal to `⊥.addCommMonoid` at `.instances` (the same `↥id.ker` vs `↥⊥`
boundary), so the assignment is rejected. The trace shows exactly this: the ❌ checkTypes node
followed by a ✅ `AddCommMonoid ↥⊥` synthesis whose `result` is `⊥.addCommMonoid`.

Consequences. `Module.Free R ↥⊥` cannot be synthesized, so `finrank_eq_zero_of_subsingleton`
never fires on `finrank R ↥⊥`. It *does* fire on `finrank R (M ⧸ ⊤)`, whose
`Submodule.Quotient.module ⊤` instance is spelled consistently at `⊤` — there `range_id` was
applied by `rw`, which transports the instances. Diffing `trace.Meta.Tactic.simp.rewrite`
confirms `finrank_eq_zero_of_subsingleton` fires twice under `"none"` and only once under
`"markOrSynth"`. The leftover `finrank R ↥⊥` is not rewritten to `0`, and `simp` closes with
`⊢ finrank R ↥⊥ = 0` unsolved.

Harmless-but-strict, not a defeq abuse. `↥id.ker` and `↥⊥` are genuinely defeq at default
transparency (`ker_id` is `rfl`), so under `"none"` — which, with
`respectTransparency.types false`, checks the mvar types at default via `withInferTypeConfig` —
the assignment is accepted. Only the `.instances` restriction refuses to delta-unfold
`LinearMap.ker`/`LinearMap.id`. This is a milder flavour than the propositional-synonym sites
in `Mathlib/RingTheory/Kaehler/JacobiZariski.lean` and
`Mathlib/CategoryTheory/Filtered/CostructuredArrow.lean`, where the two spellings are not defeq
at any transparency; the common shape is "simp rewrites a carrier but keeps instances at the
old spelling".

Prop-exemption. The rejected metavariable `?m.75 : AddCommMonoid ↥⊥` is data-valued, so the
parked Prop-exemption does not apply — even though the blocked hypothesis `Module.Free R ↥⊥`
is itself a `Prop`.

Possible fixes (proof-local preferred).
* Move `ker_id` into the `rw`: `rw [index_eq_finrank_sub, range_id, ker_id]` transports the
  instances to `↥⊥` consistently, and then `simp [finrank_eq_zero_of_subsingleton]` closes the
  goal under `"markOrSynth"` with neither backward option (verified).
* Making `LinearMap.ker`/`LinearMap.id` reducible at `.instances` would also fix it, but that
  is a definition change and is not preferred. (Adding `finrank_bot` to the `simp` set does
  *not* help: its LHS `finrank R (⊥ : Submodule R M)` hits the same instance mismatch and never
  fires.)
-/

section InstanceTypesDemos
open Lean.PostprocessTraces

private meta partial def maxDepth (depth : Nat) : TracePostprocessor := fun trees =>
  let rec truncateTree (t : TraceTree) (depth : Nat) : TraceTree :=
    match t with
    | .leaf msg => TraceTree.leaf msg
    | .node data msg children wrap =>
      match depth with
      | 0 => .node data m!"{msg} (truncated)" #[] wrap
      | depth' + 1 => .node data msg (children.map (truncateTree · depth')) wrap
  return trees.map (truncateTree · depth)

private meta partial def elideBelow (p : TracePattern) : TracePostprocessor :=
  fun trees => trees.mapM go
where
  go (t : TraceTree) : Lean.CoreM TraceTree := do
    match t with
    | .leaf msg => return .leaf msg
    | .node data msg children wrap =>
      if ← p t then
        return .node data m!"{msg} (truncated)" #[] wrap
      else
        return .node data msg (← children.mapM go) wrap

/- The load-bearing failure, in the actual build mode `"markOrSynth"`: synthesising
`Module.Free R ↥⊥` (needed by `finrank_eq_zero_of_subsingleton`) fails because
`Free.of_subsingleton` cannot assign the inherited `id.ker.addCommMonoid` to its instance-typed
`AddCommMonoid ↥⊥` mvar. Leg (c): the fallback synthesis of `AddCommMonoid ↥⊥` succeeds
(`result ⊥.addCommMonoid`), but the candidate is not defeq to it at `.instances`. The
simp then leaves `finrank R ↥⊥ = 0`, which the demo discharges with `sorry`. -/
set_option linter.style.longLine false in
/--
trace: [Meta.synthInstance] ❌️ Free R ↥⊥
  [Meta.synthInstance.apply] ❌️ apply Free.of_subsingleton to Free R ↥⊥
    [Meta.synthInstance.tryResolve] ❌️ Free R ↥⊥ ≟ Free ?m.72 ?m.73
      [Meta.isDefEq] ❌️ [instances] Free R ↥⊥ =?= Free ?m.72 ?m.73
        [Meta.isDefEq] ✅️ [instances] R =?= ?m.72
          [Meta.isDefEq] R [nonassignable] =?= ?m.72 [assignable]
          [Meta.isDefEq.assign.checkTypes] ✅️ (?m.72 : Type ?u.51) := (R : Type u_3)
            [Meta.isDefEq] ✅️ [default] Type ?u.51 =?= Type u_3
        [Meta.isDefEq] ✅️ [instances] ↥⊥ =?= ?m.73
          [Meta.isDefEq] ↥⊥ [nonassignable] =?= ?m.73 [assignable]
          [Meta.isDefEq.assign.checkTypes] ✅️ (?m.73 : Type ?u.52) := (↥⊥ : Type u_1)
            [Meta.isDefEq] ✅️ [default] Type ?u.52 =?= Type u_1
        [Meta.isDefEq.transparency] raising transparency instances → implicit
        [Meta.isDefEq] ✅️ [implicit] inst✝².toSemiring =?= ?m.74
          [Meta.isDefEq] inst✝².toSemiring [nonassignable] =?= ?m.74 [assignable]
          [Meta.isDefEq.assign.checkTypes] ✅️ (?m.74 : Semiring R) := (inst✝².toSemiring : Semiring R)
            [Meta.isDefEq] ✅️ [instances] Semiring R =?= Semiring R
              [Meta.isDefEq] ✅️ [instances] R =?= R (truncated)
        [Meta.isDefEq.transparency] raising transparency instances → implicit
        [Meta.isDefEq] ❌️ [implicit] id.ker.addCommMonoid =?= ?m.75
          [Meta.isDefEq] id.ker.addCommMonoid [nonassignable] =?= ?m.75 [assignable]
          [Meta.isDefEq.assign.checkTypes] ❌️ (?m.75 : AddCommMonoid
                ↥⊥) := (id.ker.addCommMonoid : AddCommMonoid ↥id.ker)
            [Meta.isDefEq] ❌️ [instances] AddCommMonoid ↥⊥ =?= AddCommMonoid ↥id.ker
              [Meta.isDefEq] ❌️ [instances] ↥⊥ =?= ↥id.ker (truncated)
              [Meta.isDefEq.onFailure] ❌️ AddCommMonoid ↥⊥ =?= AddCommMonoid ↥id.ker (truncated)
              [Meta.isDefEq.onFailure] ❌️ AddCommMonoid ↥⊥ =?= AddCommMonoid ↥id.ker (truncated)
            [Meta.synthInstance] ✅️ AddCommMonoid ↥⊥ (truncated)
            [Meta.isDefEq] ❌️ [implicit] id.ker.addCommMonoid =?= ⊥.addCommMonoid
              [Meta.isDefEq] ❌️ [implicit] id.ker =?= ⊥ (truncated)
              [Meta.isDefEq] ❌️ [implicit] AddSubmonoidClass.toAddCommMonoid
                    id.ker =?= AddSubmonoidClass.toAddCommMonoid ⊥ (truncated)
          [Meta.isDefEq.assign.checkTypes] ❌️ (?m.75 : AddCommMonoid
                ↥⊥) := ({ toAddMonoid := AddSubmonoidClass.toAddMonoid id.ker, add_comm := ⋯ } : AddCommMonoid ↥id.ker)
            [Meta.isDefEq] ❌️ [instances] AddCommMonoid ↥⊥ =?= AddCommMonoid ↥id.ker
              [Meta.isDefEq] ❌️ [instances] ↥⊥ =?= ↥id.ker (truncated)
              [Meta.isDefEq.onFailure] ❌️ AddCommMonoid ↥⊥ =?= AddCommMonoid ↥id.ker (truncated)
              [Meta.isDefEq.onFailure] ❌️ AddCommMonoid ↥⊥ =?= AddCommMonoid ↥id.ker (truncated)
            [Meta.synthInstance] ✅️ AddCommMonoid ↥⊥ (truncated)
            [Meta.isDefEq] ❌️ [implicit] { toAddMonoid := AddSubmonoidClass.toAddMonoid id.ker,
                  add_comm := ⋯ } =?= ⊥.addCommMonoid
              [Meta.isDefEq] ❌️ [implicit] { toAddMonoid := AddSubmonoidClass.toAddMonoid id.ker,
                    add_comm := ⋯ } =?= AddSubmonoidClass.toAddCommMonoid ⊥ (truncated)
        [Meta.isDefEq.onFailure] ❌️ Free R ↥⊥ =?= Free ?m.72 ?m.73
        [Meta.isDefEq.onFailure] ❌️ Free R ↥⊥ =?= Free ?m.72 ?m.73
---
warning: declaration uses `sorry`
-/
#guard_msgs in
set_option trace.Meta.synthInstance true in
set_option trace.Meta.isDefEq.assign.checkTypes true in
set_option trace.Meta.isDefEq true in
set_option trace.Meta.isDefEq.printTransparency true in
set_option backward.isDefEq.instanceTypes "markOrSynth" in
set_option backward.isDefEq.respectTransparency.types false in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.synthInstance.apply x)
    <&&> (containsString "Free.of_subsingleton" x) <&&> failed x)
  >=> maxDepth 7
  >=> elideBelow (fun x => (ofClass `Meta.synthInstance x) <&&> (containsString "AddCommMonoid" x))
in
theorem demoFreeSynthFails : (id : M →ₗ[R] M).index = 0 := by
  nontriviality R
  rw [index_eq_finrank_sub, range_id]
  simp [finrank_eq_zero_of_subsingleton]
  sorry

set_option allowUnsafeReducibility true

/-
Making `ker` implicit-reducible helps.
-/
attribute [local implicit_reducible] ker in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.synthInstance.apply x)
    <&&> (containsString "Free.of_subsingleton" x) <&&> failed x)
  >=> maxDepth 7
  >=> elideBelow (fun x => (ofClass `Meta.synthInstance x) <&&> (containsString "AddCommMonoid" x))
in
theorem demoFreeSynthSucceeds : (id : M →ₗ[R] M).index = 0 := by
  nontriviality R
  rw [index_eq_finrank_sub, range_id]
  simp [finrank_eq_zero_of_subsingleton]

-- fix: make `ker` implicit-reducible
attribute [local implicit_reducible] ker in
set_option backward.isDefEq.instanceTypes "markOrSynth" in
@[simp] public lemma index_id :
    (id : M →ₗ[R] M).index = 0 := by
  nontriviality R
  rw [index_eq_finrank_sub, range_id]
  simp [finrank_eq_zero_of_subsingleton]

end InstanceTypesDemos

@[simp] public lemma _root_.LinearEquiv.index_eq_zero {e : M ≃ₗ[R] N} :
    e.toLinearMap.index = 0 := by
  nontriviality R
  have := index_of_injective e.injective
  have := index_of_surjective e.surjective
  lia

end Ring

section DivisionRing

variable {k : Type*} [DivisionRing k] [Module k M] [Module k N] {f : M →ₗ[k] N}

@[simp] public lemma index_neg :
    (-f).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_neg, range_neg]

public lemma index_eq_of_finiteDimensional [FiniteDimensional k M] [FiniteDimensional k N] :
    f.index = finrank k M - finrank k N := by
  -- `0 → f.ker → M → N → f.coker → 0`
  rw [index_eq_finrank_sub]
  have h₁ := f.range.finrank_quotient_add_finrank
  have h₂ := f.quotKerEquivRange.finrank_eq
  have h₃ := f.ker.finrank_quotient_add_finrank
  lia

set_option backward.isDefEq.respectTransparency.types false in
open Submodule in
@[simp] public lemma index_comp {P : Type*} [AddCommGroup P] [Module k P] (g : N →ₗ[k] P)
    [FiniteDimensional k f.ker] [FiniteDimensional k g.ker]
    [FiniteDimensional k (N ⧸ f.range)] [FiniteDimensional k (P ⧸ g.range)] :
    (g ∘ₗ f).index = g.index + f.index := by
  -- `0 → f.ker → (g ∘ₗ f).ker → g.ker → f.coker → (g ∘ₗ f).coker → g.coker → 0`
  have aux : f.range ≤ comap g (g ∘ₗ f).range := by rw [← map_le_iff_le_comap, range_comp]
  let f₀ : f.ker →ₗ[k] (g ∘ₗ f).ker := inclusion <| ker_le_ker_comp f g
  let f₁ : (g ∘ₗ f).ker →ₗ[k] g.ker := f.restrict <| by simp
  let f₂ : g.ker →ₗ[k] N ⧸ f.range := f.range.mkQ ∘ₗ g.ker.subtype
  let f₃ : (N ⧸ f.range) →ₗ[k] P ⧸ (g ∘ₗ f).range := f.range.mapQ (g ∘ₗ f).range g aux
  let f₄ : (P ⧸ (g ∘ₗ f).range) →ₗ[k] P ⧸ g.range := factor <| range_comp_le_range f g
  have h₀ : Injective f₀ := inclusion_injective _
  have h₁ : Exact f₀ f₁ := by rw [exact_iff]; simp [f₀, f₁, ker_restrict, range_inclusion]
  have h₂ : Exact f₁ f₂ := by rw [exact_iff]; simp [f₁, f₂, ker_comp, map_comap_eq]
  have h₃ : Exact f₂ f₃ := by rw [exact_iff]; simp [f₂, f₃, range_comp, ker_mapQ, comap_map_eq]
  have h₄ : Exact f₃ f₄ := by rw [exact_iff]; simp [f₃, f₄, factor, ker_mapQ, range_mapQ]
  have h₅ : Surjective f₄ := factor_surjective _
  have : FiniteDimensional k (g ∘ₗ f).ker := by rw [ker_comp]; infer_instance
  have : FiniteDimensional k (P ⧸ (g ∘ₗ f).range) := by rw [range_comp]; infer_instance
  grind [index, sum_neg_one_pow_finrank_eq_zero_of_exact_six f₀ f₁ f₂ f₃ f₄ h₀ h₁ h₂ h₃ h₄ h₅]

end DivisionRing

section Field

variable {k : Type*} [Field k] [Module k M] [Module k N] {f : M →ₗ[k] N}

public lemma index_smul (t : k) (ht : t ≠ 0) :
    (t • f).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_smul _ _ ht, range_smul _ _ ht]

end Field

end LinearMap
