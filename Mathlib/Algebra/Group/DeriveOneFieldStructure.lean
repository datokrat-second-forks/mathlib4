/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public meta import Mathlib.Tactic.DeriveOneFieldStructure

/-!
# Deriving group structures for one-field structures

Deriving handlers transferring `AddCommGroup` and `CommGroup` along the canonical equivalence
between a one-field structure and the type of its field. See
`Mathlib/Tactic/DeriveOneFieldStructure.lean` for the general set-up.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerDerivingHandler ``AddCommGroup <| mkOneFieldStructureHandler ``AddCommGroup fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ [AddCommGroup $α], AddCommGroup $S),
            ← `(fun [AddCommGroup $α] => Equiv.addCommGroup $(info.equivStx)))
  registerDerivingHandler ``CommGroup <| mkOneFieldStructureHandler ``CommGroup fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ [CommGroup $α], CommGroup $S),
            ← `(fun [CommGroup $α] => Equiv.commGroup $(info.equivStx)))

end Mathlib.Deriving.OneFieldStructure
