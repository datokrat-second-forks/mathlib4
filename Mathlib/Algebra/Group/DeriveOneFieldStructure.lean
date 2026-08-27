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
between a one-field structure and the type of its field. The corresponding instance on the field
type is synthesized from the structure's parameters at deriving time. See
`Mathlib/Tactic/DeriveOneFieldStructure.lean` for the general set-up.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerOneFieldStructureHandler ``AddCommGroup fun info args => do
    ensureNoArgs ``AddCommGroup args
    return (← `(AddCommGroup $(info.typeStx)), ← `(Equiv.addCommGroup $(info.equivStx)))
  registerOneFieldStructureHandler ``CommGroup fun info args => do
    ensureNoArgs ``CommGroup args
    return (← `(CommGroup $(info.typeStx)), ← `(Equiv.commGroup $(info.equivStx)))

end Mathlib.Deriving.OneFieldStructure
