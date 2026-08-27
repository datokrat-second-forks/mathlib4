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
`TopologicalSpace` handler, that is, the topology induced by the projection.
`IsTopologicalAddGroup` additionally assumes that `AddCommGroup` was derived, and the two scalar
action handlers take the scalar ring as an argument (`deriving instance ContinuousSMul 𝕜 for S`)
and assume that `Module` was derived for the same ring: a one-field structure has no `SMul`
instance of its own, and deriving one separately would be a diamond with the one coming from
`Module`. The corresponding instances on the field type are synthesized from the structure's
parameters at deriving time.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerOneFieldStructureHandler ``IsTopologicalAddGroup fun info args => do
    ensureNoArgs ``IsTopologicalAddGroup args
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(IsTopologicalAddGroup $S),
            ← `(Topology.IsInducing.isTopologicalAddGroup
                  (show $S →+ $α from ⟨⟨$(info.projStx), rfl⟩, fun _ _ => rfl⟩) ⟨rfl⟩))
  registerOneFieldStructureHandler ``ContinuousSMul fun info args => do
    let #[R] := args
      | throwError "deriving `ContinuousSMul` for a one-field structure needs the scalar ring as \
          an argument, as in `deriving instance ContinuousSMul 𝕜 for MyStructure`"
    return (← `(ContinuousSMul $R $(info.typeStx)),
            ← `(Topology.IsInducing.continuousSMul (g := $(info.projStx)) (f := id) ⟨rfl⟩
                  continuous_id fun {_ _} => rfl))
  registerOneFieldStructureHandler ``ContinuousConstSMul fun info args => do
    let #[R] := args
      | throwError "deriving `ContinuousConstSMul` for a one-field structure needs the scalar \
          ring as an argument, as in `deriving instance ContinuousConstSMul 𝕜 for MyStructure`"
    return (← `(ContinuousConstSMul $R $(info.typeStx)),
            ← `(Topology.IsInducing.continuousConstSMul (g := $(info.projStx)) ⟨rfl⟩ id
                  fun {_ _} => rfl))

end Mathlib.Deriving.OneFieldStructure
