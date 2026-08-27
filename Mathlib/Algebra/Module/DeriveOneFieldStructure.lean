/-
Copyright (c) 2026 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public meta import Mathlib.Algebra.Group.DeriveOneFieldStructure

/-!
# Deriving module structures for one-field structures

A deriving handler transferring `Module` along the canonical equivalence between a one-field
structure and the type of its field. See `Mathlib/Tactic/DeriveOneFieldStructure.lean` for the
general set-up.

The scalar ring is given as an argument, as in `deriving instance Module 𝕜 for TangentSpace`;
it may refer to the structure's parameters by name, and `Module 𝕜 (fieldType)` is synthesized
from the structure's parameters at deriving time. The handler also needs the additive structure
of the one-field structure, so `AddCommGroup` has to be derived first.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerOneFieldStructureHandler ``_root_.Module fun info args => do
    let #[R] := args
      | throwError "deriving `Module` for a one-field structure needs the scalar ring as an \
          argument, as in `deriving instance Module 𝕜 for MyStructure`"
    return (← `(Module $R $(info.typeStx)),
            ← `((show $(info.typeStx) ≃+ $(info.fieldTypeStx) from
                  ⟨$(info.equivStx), fun _ _ => rfl⟩).module $R))

end Mathlib.Deriving.OneFieldStructure
