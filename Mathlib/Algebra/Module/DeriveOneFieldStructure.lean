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

Since a deriving handler never sees the arguments of the class it is invoked for, the derived
instance quantifies over the scalar ring: write `deriving Module`, not `deriving Module R`.
The handler needs the additive structure of the one-field structure, so `AddCommGroup` has to be
derived first.
-/

public meta section

namespace Mathlib.Deriving.OneFieldStructure

open Lean Elab Term

initialize
  registerDerivingHandler ``_root_.Module <|
      mkOneFieldStructureHandler ``_root_.Module fun info => do
    let α := info.fieldTypeStx
    let S := info.typeStx
    return (← `(∀ {R : Type _} [Semiring R] [AddCommGroup $α] [Module R $α], Module R $S),
            ← `(fun {R : Type _} [Semiring R] [AddCommGroup $α] [Module R $α] =>
                  (show $S ≃+ $α from ⟨$(info.equivStx), fun _ _ => rfl⟩).module R))

end Mathlib.Deriving.OneFieldStructure
