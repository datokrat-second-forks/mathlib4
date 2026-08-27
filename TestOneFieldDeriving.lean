/-
A hand-written mock-up of what a *generic* one-field-structure deriving handler would emit,
one case per section. Nothing here is meta code: every instance below is the term the engine
would generate, so this file is the specification of the engine, written out by hand.

The engine's knowledge is a small table indexed by the *type former* at the head of each
field's type (not by the class being derived!):

    carrier S            ↦ transport by `proj`/`mk` (direction chosen by variance)
    any type without S   ↦ copied verbatim
    T₁ → T₂              ↦ recurse; the left side flips variance
    Set T                ↦ preimage along the transport of `T` (Set is `T → Prop`)
    Filter T             ↦ `Filter.map` along the transport of `T`
    parent structure     ↦ NOT transported: `inferInstanceAs` on `S` (diamond discipline)
    Prop field           ↦ the E-side axiom, conjugated by `congrArg`/eta and the
                           *naturality lemmas* of the formers appearing in it

Each rule is a "relator": it says how to build the transport map for `F T` out of the
transport map for `T`, plus which lemmas discharge the proof obligations it creates.
A dozen such entries cover almost every class in Mathlib; that is the economy compared
to one hand-written transfer per class (`Equiv.mul`, `Equiv.monoid`, ... today).
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.Filter.Map
import Mathlib.Algebra.Group.Defs

universe u

structure Wrap (α : Type u) : Type u where
  inner : α

namespace Wrap

variable {α : Type*}

/-- The canonical equivalence. Because `Wrap` is a one-field structure, *both* round trips
are definitional (structure eta): this is what makes the Prop-field discharge below so much
easier than transport along an arbitrary `Equiv`. -/
def equiv (α : Type u) : Wrap α ≃ α :=
  ⟨inner, mk, fun _ => rfl, fun _ => rfl⟩

example (x : Wrap α) : mk x.inner = x := rfl   -- eta, judgmentally

/-! ### Case 1: data fields built from `→` and the carrier

`mul : S → S → S`. Argument positions (left of an arrow: contravariant) transport by
`proj = inner`, the result position (covariant) by `mk`. -/

instance [Mul α] : Mul (Wrap α) where
  mul x y := mk (x.inner * y.inner)

/-- A constant of the carrier: result position only, so just `mk`. -/
instance [One α] : One (Wrap α) where
  one := mk 1

/-- Multi-parameter class: the goal `SMul R (Wrap α)` dictates *which* occurrences are the
carrier being transported (only `α`'s); `R`-positions are copied verbatim. -/
instance {R : Type*} [SMul R α] : SMul R (Wrap α) where
  smul r x := mk (r • x.inner)

/-! ### Case 2: Prop fields, first order

The S-side axiom *is* the E-side axiom under `congrArg mk`, judgmentally, thanks to eta.
This is the entire discharge tactic for fields whose statement only involves `→`, `=`,
and the carrier. Note `one_mul`: the right-hand side is `a`, not `mk a.inner` — eta makes
`congrArg mk` typecheck anyway. -/

instance [Semigroup α] : Semigroup (Wrap α) :=
  { (inferInstance : Mul (Wrap α)) with          -- Case 3 below
    mul_assoc := fun a b c => congrArg mk (mul_assoc a.inner b.inner c.inner) }

instance [MulOneClass α] : MulOneClass (Wrap α) :=
  { (inferInstance : One (Wrap α)), (inferInstance : Mul (Wrap α)) with
    one_mul := fun a => congrArg mk (one_mul a.inner)
    mul_one := fun a => congrArg mk (mul_one a.inner) }

/-! ### Case 3: parent projections → `inferInstanceAs`, never re-transported

`Monoid extends Semigroup, MulOneClass`. The engine must NOT conjugate the whole `Monoid α`
wholesale — that would bake in a *fresh* `Mul (Wrap α)` not definitionally shared with the
one derived above. Instead, parents are filled by synthesis on `Wrap α`, reusing the
already-derived instances (this also forces the derivation order, like `AddCommGroup`
before `Module` for `TangentSpace`). Only the fields that are *new* in `Monoid`
(`npow` and its axioms) get transported.

(Engine detail: `(inferInstance : C (Wrap α))`, not `inferInstanceAs` — inside the record
update `{ _ with }` there is no expected type, and the current `inferInstanceAs` insists
on one for its instance-translation step.) -/

instance [Monoid α] : Monoid (Wrap α) :=
  { (inferInstance : Semigroup (Wrap α)), (inferInstance : MulOneClass (Wrap α)) with
    npow := fun n x => mk (x.inner ^ n)         -- ℕ has no carrier: copied verbatim
    npow_zero := fun x => congrArg mk (pow_zero x.inner)
    npow_succ := fun n x => congrArg mk (pow_succ x.inner n) }

-- the diamond discipline, checked judgmentally: the `Mul` inside `Monoid` IS the `Mul` instance
example [Monoid α] (x y : Wrap α) : x * y = mk (x.inner * y.inner) := rfl
example [Monoid α] (x : Wrap α) : (x * 1).inner = x.inner * 1 := rfl

/-! ### Case 4: `Set`-valued fields — the type-former table in action

`TopologicalSpace` has `IsOpen : Set S → Prop`. The table entry for `Set` says: transport
`Set S → Set E` by preimage along the transport of the element type run *backwards*
(`Set T = T → Prop`, so this is just the arrow rule again): `s ↦ mk ⁻¹' s`.

The Prop fields now show the general shape of discharge obligations:
* `isOpen_univ`, `isOpen_inter`: the naturality equations (`mk ⁻¹' univ = univ`,
  `mk ⁻¹' (s ∩ t) = mk ⁻¹' s ∩ mk ⁻¹' t`) hold *judgmentally*, so the E-axiom is accepted
  as-is.
* `isOpen_sUnion`: the naturality equation `mk ⁻¹' ⋃₀ S = ⋃ t ∈ S, mk ⁻¹' t` is only
  propositional — the engine must rewrite with the registered naturality lemma
  (`Set.preimage_sUnion`) before applying the E-axiom. This is exactly where the
  per-former lemma database earns its keep. -/

instance genericTopology [TopologicalSpace α] : TopologicalSpace (Wrap α) where
  IsOpen s := IsOpen (mk ⁻¹' s)
  isOpen_univ := isOpen_univ
  isOpen_inter _ _ hs ht := hs.inter ht
  isOpen_sUnion S hS := by
    show IsOpen (mk ⁻¹' ⋃₀ S)
    rw [Set.preimage_sUnion]
    exact isOpen_biUnion hS

/- The curated comparison: our *actual* handler emits `TopologicalSpace.induced inner ‹_›`
instead, a nicer normal form. Generic transport and the curated choice agree — but only
propositionally, which is why per-class overrides should shadow the generic engine. -/
open scoped Topology in
example [TopologicalSpace α] (s : Set (Wrap α)) :
    IsOpen[genericTopology] s ↔ IsOpen[TopologicalSpace.induced inner ‹_›] s := by
  constructor
  · exact fun h => ⟨mk ⁻¹' s, h, rfl⟩            -- `inner ⁻¹' (mk ⁻¹' s) = s` is eta, `rfl`
  · rintro ⟨u, hu, rfl⟩; exact hu                -- `mk ⁻¹' (inner ⁻¹' u) = u` likewise

/-! ### Case 5: `Filter`-valued fields, and naturality-lemma discharge

A mock class packing the remaining rules into one place: a field with no carrier
(copied), a `Filter`-valued field (covariant former: `Filter.map`), and a Prop field
whose discharge needs the former's naturality lemmas (`map_pure`, `map_mono`) rather
than bare `congrArg`. Compare `Bornology` (`cobounded : Filter α`) for the real thing. -/

class Gadget (X : Type u) where
  weight : ℕ                            -- no carrier: copied verbatim
  base : X                              -- constant: `mk`
  near : X → Filter X                   -- arrow into a covariant former
  pure_le_near : ∀ x, pure x ≤ near x   -- Prop over the former

instance [Gadget α] : Gadget (Wrap α) where
  weight := Gadget.weight α
  base := mk Gadget.base
  near x := (Gadget.near x.inner).map mk
  pure_le_near x :=
    -- `pure x = pure (mk x.inner) = map mk (pure x.inner)` — the middle step is eta,
    -- the right one is the naturality lemma `Filter.map_pure`.
    (Filter.map_pure mk x.inner).symm.trans_le (Filter.map_mono (Gadget.pure_le_near x.inner))

/-! ### Case 6: where the structural recursion genuinely stops

`DecidableEq S` has type `(a b : S) → Decidable (a = b)`: the carrier occurs inside the
*index of a dependent type* (`Decidable` at the proposition `a = b`). No variance rule
applies — transporting needs a propositional bridge (`decidable_of_iff`), i.e. genuine
per-former intelligence about `Decidable`, or a handler. This is the honest coverage
boundary of the generic engine: fail loudly here and ask for a per-class handler. -/

instance [DecidableEq α] : DecidableEq (Wrap α) := fun a b =>
  decidable_of_iff (a.inner = b.inner) ⟨fun h => congrArg mk h, fun h => congrArg inner h⟩

end Wrap
