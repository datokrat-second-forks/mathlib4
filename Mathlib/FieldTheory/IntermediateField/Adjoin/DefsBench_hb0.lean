/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `K[x]` might not include `x⁻¹`.

## Notation

- `F⟮α⟯`: adjoin a single element `α` to `F` (in scope `IntermediateField`).
-/

@[expose] public section

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
@[stacks 09FZ "first part", implicit_reducible]
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.range (algebraMap F E) ∪ S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

@[simp]
theorem adjoin_toSubfield :
    (adjoin F S).toSubfield = Subfield.closure (Set.range (algebraMap F E) ∪ S) := rfl

variable {F S} in
theorem mem_adjoin_iff_div {x : E} : x ∈ adjoin F S ↔
    ∃ r ∈ Algebra.adjoin F S, ∃ s ∈ Algebra.adjoin F S, x = r / s := by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring, eq_comm]

end AdjoinDef

section Lattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

@[simp]
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ⊆ T :=
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.range (algebraMap F E) ∪ S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) := fun _ _ =>
  adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
@[implicit_reducible]
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) where
  choice s hs := (adjoin F s).copy s <| le_antisymm (gc.le_u_l s) hs
  gc := IntermediateField.gc
  le_l_u S := (IntermediateField.gc (S : Set E) (adjoin F S)).1 <| le_rfl
  choice_eq _ _ := copy_eq _ _ _

instance : CompleteLattice (IntermediateField F E) where
  __ := GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot :=
    { toSubalgebra := ⊥
      inv_mem' := by rintro x ⟨r, rfl⟩; exact ⟨r⁻¹, map_inv₀ _ _⟩ }
  bot_le x := (bot_le : ⊥ ≤ x.toSubalgebra)

set_option synthInstance.maxHeartbeats 0 in
set_option trace.profiler true in
instance (K₁ K₂ : IntermediateField F E) : Algebra ↥(K₁ ⊓ K₂) K₁ :=
  inferInstanceAs <| Algebra ↑(K₁.toSubalgebra ⊓ K₂.toSubalgebra) K₁.toSubalgebra

#exit
