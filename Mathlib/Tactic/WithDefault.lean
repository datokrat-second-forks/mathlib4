/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# Default transparency in tactics

`with_default tacs` runs `tacs` at default transparency, even inside a tactic that
restricts transparency.
-/

public meta section

namespace Mathlib.Tactic

/-- Run a tactic sequence at default transparency. -/
elab "with_default " t:Lean.Parser.Tactic.tacticSeq : tactic =>
  Lean.Meta.withDefault (Lean.Elab.Tactic.evalTactic t)

end Mathlib.Tactic
