/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff
public meta import Mathlib.Tactic.DeriveOneFieldStructure

/-!
# Deriving topologies for one-field structures

Deriving handlers for `TopologicalSpace` and for a few properties of topological spaces, for
structures with a single field. See `Mathlib/Tactic/DeriveOneFieldStructure.lean` for the general
set-up.

The topology derived for a one-field structure is the one induced by its projection, so that the
projection is a homeomorphism onto the type of the field. The other handlers in this file assume
that the topology on the structure is that one, and fail otherwise. `TopologicalSpace` and
`T2Space` synthesize the corresponding instance on the field type from the structure's parameters;
`PathConnectedSpace` instead takes it as a hypothesis of the derived instance, since path
connectedness of the field type is usually not synthesizable from the parameters (for
`TangentSpace` it holds over `ℝ` but not over a general field).
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerOneFieldStructureHandler ``TopologicalSpace fun info args => do
    ensureNoArgs ``TopologicalSpace args
    return (← `(TopologicalSpace $(info.typeStx)),
            ← `(TopologicalSpace.induced $(info.projStx) inferInstance))
  registerOneFieldStructureHandler ``T2Space fun info args => do
    ensureNoArgs ``T2Space args
    return (← `(T2Space $(info.typeStx)),
            ← `((Equiv.toHomeomorphOfIsInducing $(info.equivStx) ⟨rfl⟩).symm.t2Space))
  registerOneFieldStructureHandler ``PathConnectedSpace fun info args => do
    ensureNoArgs ``PathConnectedSpace args
    let α := info.fieldTypeStx
    return (← `(∀ [PathConnectedSpace $α], PathConnectedSpace $(info.typeStx)),
            ← `(fun [PathConnectedSpace $α] =>
                  (Equiv.toHomeomorphOfIsInducing $(info.equivStx) ⟨rfl⟩).symm.pathConnectedSpace))

end Mathlib.Deriving.OneFieldStructure
