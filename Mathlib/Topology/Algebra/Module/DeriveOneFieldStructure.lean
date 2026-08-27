/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public meta import Mathlib.Algebra.Module.DeriveOneFieldStructure
public meta import Mathlib.Topology.DeriveOneFieldStructure

/-!
# Deriving topological algebra structures for one-field structures

Deriving handlers for `IsTopologicalAddGroup`, `ContinuousSMul` and `ContinuousConstSMul` on
structures with a single field. See `Mathlib/Tactic/DeriveOneFieldStructure.lean` for the general
set-up.

All three handlers assume that the topology on the structure is the one derived by the
`TopologicalSpace` handler, that is, the topology induced by the projection. `IsTopologicalAddGroup`
additionally assumes that `AddCommGroup` was derived, and the two scalar action handlers assume
that `Module` was derived: a one-field structure has no `SMul` instance of its own, and deriving
one separately would be a diamond with the one coming from `Module`. Since a deriving handler never
sees the arguments of the class it is invoked for, the derived scalar instances quantify over the
scalar ring: write `deriving ContinuousSMul`, not `deriving ContinuousSMul R`.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerDerivingHandler ``IsTopologicalAddGroup <|
      mkOneFieldStructureHandler ``IsTopologicalAddGroup fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ [TopologicalSpace $α] [AddCommGroup $α] [IsTopologicalAddGroup $α],
                  IsTopologicalAddGroup $S),
            ← `(fun [TopologicalSpace $α] [AddCommGroup $α] [IsTopologicalAddGroup $α] =>
                  Topology.IsInducing.isTopologicalAddGroup
                    (show $S →+ $α from ⟨⟨$(info.projStx), rfl⟩, fun _ _ => rfl⟩) ⟨rfl⟩))
  registerDerivingHandler ``ContinuousSMul <|
      mkOneFieldStructureHandler ``ContinuousSMul fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ {R : Type _} [Semiring R] [TopologicalSpace R] [TopologicalSpace $α]
                  [AddCommGroup $α] [Module R $α] [ContinuousSMul R $α], ContinuousSMul R $S),
            ← `(fun {R : Type _} [Semiring R] [TopologicalSpace R] [TopologicalSpace $α]
                  [AddCommGroup $α] [Module R $α] [ContinuousSMul R $α] =>
                  Topology.IsInducing.continuousSMul (g := $(info.projStx)) (f := id) ⟨rfl⟩
                    continuous_id fun {_ _} => rfl))
  registerDerivingHandler ``ContinuousConstSMul <|
      mkOneFieldStructureHandler ``ContinuousConstSMul fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ {R : Type _} [Semiring R] [TopologicalSpace $α] [AddCommGroup $α] [Module R $α]
                  [ContinuousConstSMul R $α], ContinuousConstSMul R $S),
            ← `(fun {R : Type _} [Semiring R] [TopologicalSpace $α] [AddCommGroup $α] [Module R $α]
                  [ContinuousConstSMul R $α] =>
                  Topology.IsInducing.continuousConstSMul (g := $(info.projStx)) ⟨rfl⟩ id
                    fun {_ _} => rfl))

end Mathlib.Deriving.OneFieldStructure
