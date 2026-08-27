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
projection is a homeomorphism onto the type of the field. All the other handlers in this file
assume that the topology on the structure is that one, and fail otherwise.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerDerivingHandler ``TopologicalSpace <|
      mkOneFieldStructureHandler ``TopologicalSpace fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ [TopologicalSpace $α], TopologicalSpace $S),
            ← `(fun [TopologicalSpace $α] => TopologicalSpace.induced $(info.projStx) ‹_›))
  registerDerivingHandler ``T2Space <| mkOneFieldStructureHandler ``T2Space fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ [TopologicalSpace $α] [T2Space $α], T2Space $S),
            ← `(fun [TopologicalSpace $α] [T2Space $α] =>
                  (Equiv.toHomeomorphOfIsInducing $(info.equivStx) ⟨rfl⟩).symm.t2Space))
  registerDerivingHandler ``PathConnectedSpace <|
      mkOneFieldStructureHandler ``PathConnectedSpace fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ [TopologicalSpace $α] [PathConnectedSpace $α], PathConnectedSpace $S),
            ← `(fun [TopologicalSpace $α] [PathConnectedSpace $α] =>
                  (Equiv.toHomeomorphOfIsInducing $(info.equivStx) ⟨rfl⟩).symm.pathConnectedSpace))

end Mathlib.Deriving.OneFieldStructure
