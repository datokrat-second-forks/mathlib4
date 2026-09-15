import Mathlib.Tactic.Semireducible

open Lean Meta Elab Tactic

-- Assert the transparency boundary without relying on elaboration heuristics.
elab "check_semireducible" : tactic => do
  let target ← getMainTarget
  let some (_, lhs, rhs) := target.eq? | throwError "expected an equality"
  if ← withReducibleAndInstances <| isDefEq lhs rhs then
    throwError "term reduced at instance transparency"
  if ← withImplicit <| isDefEq lhs rhs then
    throwError "term reduced at implicit transparency"
  unless ← withDefault <| isDefEq lhs rhs do
    throwError "term did not reduce at default transparency"
  withDefault <| closeMainGoal `check_semireducible (← mkEqRefl lhs)

@[instance_reducible] def hiddenIdentity {α : Sort u} (x : α) : α := semireducible% x

example {α : Sort u} (x : α) : hiddenIdentity x = x := by
  check_semireducible

-- The unfolding theorem is usable by simp, but not by dsimp, in either recognition mode.
example {α : Sort u} (x : α) : hiddenIdentity x = x := by
  fail_if_success solve | dsimp [hiddenIdentity]
  simp [hiddenIdentity]

set_option backward.dsimp.useDefEqAttr false in
example {α : Sort u} (x : α) : hiddenIdentity x = x := by
  fail_if_success solve | dsimp [hiddenIdentity]
  simp [hiddenIdentity]

-- Capture dependent parameters and local lets.
@[instance_reducible] def hiddenDependent {α : Type u} (β : α → Type v) (a : α) (x : β a) : β a :=
  let y := x
  semireducible% y

example {α : Type u} (β : α → Type v) (a : α) (x : β a) : hiddenDependent β a x = x := by
  check_semireducible

-- Elaborate the body against its expected type, including instance synthesis.
@[instance_reducible] def hiddenZero (α : Type u) [Zero α] : α := semireducible% 0

example (α : Type u) [Zero α] : hiddenZero α = 0 := by
  check_semireducible

-- Wrappers preserve compilation for computable terms.
def hiddenSucc : Nat → Nat := semireducible% fun n ↦ n + 1

/-- info: 4 -/
#guard_msgs in
#eval hiddenSucc 3

-- Noncomputable bodies are allowed in noncomputable definitions.
noncomputable def hiddenChoice {α : Sort u} (h : Nonempty α) : α :=
  semireducible% Classical.choice h

example {α : Sort u} (h : Nonempty α) : hiddenChoice h = Classical.choice h := rfl

-- The generated declaration must also work in meta definitions.
meta def hiddenMeta : Nat := semireducible% 7

/-- info: 7 -/
#guard_msgs in
#eval hiddenMeta
