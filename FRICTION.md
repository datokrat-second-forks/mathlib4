# Friction from turning `OrderDual` into a one-field structure

`OrderDual α` used to be a reducible type synonym (`def OrderDual (α : Type*) := α`), so
`αᵒᵈ` and `α` were definitionally the same type and `toDual`/`ofDual` were the identity.
It is now

```lean
structure OrderDual (α : Type*) where
  toDual' ::
  ofDual' : α
```

so `toDual`/`ofDual` really move data. Everything below is friction that this change causes
downstream, with the shape of the repair. Most of it is *not* a defect of the new definition:
it is places where the old proof silently exploited the synonym being an identity. But some of
it is elaborator friction that could be removed.

## 1. Unification cannot invert the wrapper: `toDual ?x =?= y`

This is the single most common failure, and the one worth fixing in the elaborator. When the
expected type mentions a value of `α` and the term produces a value of `αᵒᵈ` (or vice versa),
unification has to solve `toDual ?x =?= y` / `ofDual ?x =?= y`. It cannot, because it will not
apply the inverse function, so the implicit argument is left as a stuck metavariable and the
error surfaces as a type mismatch with `?m` still in it.

Every one of the following needed a hint that a human would call redundant:

```lean
-- Mathlib/Algebra/Order/Group/Synonym.lean
lemma ofDual_eq_one {a : αᵒᵈ} : ofDual a = 1 ↔ a = 1 := ofDual_inj (b := 1)
--                                                                ^^^^^^^^
-- `(1 : α)` has to be recognised as `ofDual 1`; unification will not do it.

-- Mathlib/Order/Lattice.lean
theorem Antitone.map_sup_le (h : Antitone f) (x y : α) : f (x ⊔ y) ≤ f x ⊓ f y :=
  (h.dual_right.le_map_sup (f := ⇑OrderDual.toDual ∘ f) x y :)
--                          ^^^^^^^^^^^^^^^^^^^^^^^^^^
-- without the hint: `Monotone.le_map_sup ?m.21 x y has type ?m.20 x ⊔ ?m.20 y ≤ ...`

-- Mathlib/Order/Max.lean
theorem isBot_ofDual_iff {a : αᵒᵈ} : IsBot (ofDual a) ↔ IsTop a :=
  (OrderDual.forall (p := (· ≤ a))).symm
--                  ^^^^^^^^^^^^^^
-- the higher-order pattern `?p (toDual b)` against `b ≤ ofDual a` is not solved.

-- Mathlib/Order/BoundedOrder/Basic.lean
lemma ofDual_eq_top {a : αᵒᵈ} : ofDual a = ⊤ ↔ a = ⊥ := ofDual_inj (b := ⊥)
```

**Wish:** teach the elaborator to solve `toDual ?x =?= y` by `?x := ofDual y` (and dually) for
an `Equiv`-like pair marked as such. That would remove most of the annotations above.

Until then, **the pattern is: pass the dualised arguments explicitly.** Do not try to make the
term elaborate by rearranging it; name the function or the value that the unifier cannot guess.

## 2. Binders over `αᵒᵈ` are no longer binders over `α`

`∀ x : αᵒᵈ, p x` and `∃ x : αᵒᵈ, p x` used to be *the same proposition* as their `α` versions.
Now they are not, and a proof of one is not a proof of the other — even though the bodies are
still defeq once a wrapper is applied. The repair is to insert `OrderDual.forall` /
`OrderDual.exists` explicitly:

```lean
-- Mathlib/Order/Lattice.lean
theorem exists_le_and_iff_exists (hP : Antitone P) : (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  (OrderDual.exists (p := fun x ↦ OrderDual.toDual x₀ ≤ x ∧ (P ∘ ⇑OrderDual.ofDual) x)).symm.trans
    ((exists_ge_and_iff_exists (x₀ := OrderDual.toDual x₀) hP.dual_left).trans OrderDual.exists)
-- was: `exists_ge_and_iff_exists <| hP.dual_left`
```

Note this also hits **hypotheses of structure instances**: `le_sup_inf := inf_sup_le` in
`DistribLattice.ofInfSupLe` failed because the field wants `∀ x y z : αᵒᵈ, …` and the
hypothesis is `∀ a b c : α, …`; the bodies are defeq, the telescopes are not.

```lean
abbrev DistribLattice.ofInfSupLe [Lattice α]
    (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) : DistribLattice α where
  le_sup_inf a b c := (@OrderDual.instDistribLattice αᵒᵈ { (inferInstance : Lattice αᵒᵈ) with
      le_sup_inf := fun x y z ↦
        inf_sup_le (OrderDual.ofDual x) (OrderDual.ofDual y) (OrderDual.ofDual z) }).le_sup_inf
    (OrderDual.toDual (OrderDual.toDual a)) (OrderDual.toDual (OrderDual.toDual b))
    (OrderDual.toDual (OrderDual.toDual c))
```

## 3. `dual_dual` identities do not typecheck any more

`SemilatticeSup.dual_dual : OrderDual.instSemilatticeSup αᵒᵈ = H` compared an instance on
`αᵒᵈᵒᵈ` with one on `α`. Those are now different types, so the statement itself is ill-typed
(and `@[to_dual]` warns that it did not change the type). The content that survives is the
equality of the *data fields* under a double wrapper:

```lean
theorem SemilatticeSup.dual_dual (α : Type*) [H : SemilatticeSup α] :
    (OrderDual.instSemilatticeSup αᵒᵈ).sup = fun a b ↦
      OrderDual.toDual (OrderDual.toDual
        (H.sup (OrderDual.ofDual (OrderDual.ofDual a)) (OrderDual.ofDual (OrderDual.ofDual b)))) :=
  rfl
```

The same happened to the four `dual_dual` lemmas in `Mathlib/Order/OrderDual.lean` (restated as
`le` / `compare` field equalities).

## 4. Instance fields must unwrap and rewrap by hand

Every field that used to be inherited by definitional identity now needs `.ofDual'` on the
inputs and `toDual'` on `Type`-valued outputs; `Prop`-valued fields only unwrap. Equalities in
the dual type are produced with `congrArg toDual'`.

```lean
instance OrderDual.instSemilatticeSup (α) [h : SemilatticeInf α] : SemilatticeSup αᵒᵈ where
  sup a b := OrderDual.toDual' (h.inf a.ofDual' b.ofDual')
  le_sup_left a b := h.inf_le_left a.ofDual' b.ofDual'
  le_sup_right a b := h.inf_le_right a.ofDual' b.ofDual'
  sup_le _ _ _ hac hbc := h.le_inf _ _ _ hac hbc

instance [PartialOrder α] : PartialOrder αᵒᵈ where
  le_antisymm a b hab hba := congrArg toDual' (@le_antisymm α _ a.ofDual' b.ofDual' hba hab)
```

For bundled algebraic classes the same job is done wholesale by the `Function.Injective.*`
transport lemmas, which is much shorter than a field-by-field rewrite:

```lean
@[to_additive] instance [Monoid α] : Monoid αᵒᵈ :=
  ofDual.injective.monoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
```

(the cost is one extra import, e.g. `Mathlib.Algebra.Group.InjSurj` in
`Mathlib/Algebra/Order/Group/Synonym.lean`; measured as exactly one new module, no new
transitive dependencies).

## 5. Things that no longer reduce, and were relied on

* **`DecidableEq αᵒᵈ` no longer computes to `α`'s.** `decide (a = b)` and
  `decide (a.ofDual' = b.ofDual')` are no longer the same term, because `Eq αᵒᵈ ⟨a⟩ ⟨b⟩` is not
  `Eq α a b`. Proofs closing such goals by `rfl` need `OrderDual.toDual'.injEq` in the
  `simp only` set (e.g. `compare_eq_compareOfLessAndEq`). This is inherent to the change and
  harmless for diamonds, but it is a real behaviour change.
* **Iteration through the dual** does not reduce either: `(toDual ∘ f ∘ ofDual)^[n] (toDual x)`
  is no longer syntactically `toDual (f^[n] x)`. `Mathlib/Order/Iterate.lean` needed a private
  conjugation lemma proved by induction, and it must be applied *before* `Function.comp_def`
  gets a chance to unfold the composition — `simpa only [...]` had to become
  `have H := …; simp only [iterate_conj_toDual] at H; exact H`.
* **`with_reducible rfl` fails for parent projections.** This is *not* a regression: a control
  experiment with a plain old-style `def Syn (α) := α` fails identically.

## 6. Name resolution

Inside `namespace GaloisCoinsertion`, a bare `ofDual` resolves to the declaration being defined
(`GaloisCoinsertion.ofDual`), not to `OrderDual.ofDual`. With the old synonym this was invisible
because the term elaborated anyway. Qualify as `OrderDual.ofDual` in such namespaces.

## 7. Option lines that became unnecessary

The rewrite let us delete backward-compatibility options that existed only to paper over the
synonym: six `set_option backward.inferInstanceAs.wrap.instances false` in
`Mathlib/Algebra/Order/Group/Synonym.lean` and four
`set_option backward.isDefEq.respectTransparency false in` in `Mathlib/Order/Monotone/Basic.lean`.

## 8. Type synonyms whose *duality* was the identity: `WithBot` / `WithTop`

`Mathlib/Order/WithBot.lean` defined `WithTop`'s order as `WithBot`'s order at `αᵒᵈ`:

```lean
instance WithTop.instLE : LE (WithTop α) where le a b := WithBot.LE (α := αᵒᵈ) b a
```

`b : WithTop α` was accepted as a `WithBot αᵒᵈ` for two independent reasons: `WithTop α` and
`WithBot α` are both `def … := Option α` (still true), and `αᵒᵈ` *was* `α` (no longer true). The
file even carries a TODO asking whether that def-eq should be kept. It can be kept — the fix is a
`map` bridge across the wrapper only:

```lean
instance (priority := 10) WithTop.instLE : LE (WithTop α) where
  le a b := WithBot.LE (α := αᵒᵈ) (b.map OrderDual.toDual') (a.map OrderDual.toDual')
```

Measured cost for the whole 1000-line file: the two order instances above, the two dual
equivalences (`WithBot.toDual`/`ofDual` stop being `Equiv.refl` and become genuine
`Option.map`-based bijections), the four `map_*` lemmas next to them, and real proofs for
`WithTop.le_def'` / `lt_def'`, which could no longer be `WithBot.le_def` / `WithBot.lt_def`:

```lean
lemma WithTop.le_def' {x y : WithTop α} : x ≤ y ↔ y = ⊤ ∨ ∃ b a : α, a ≤ b ∧ y = b ∧ x = a := by
  cases x <;> cases y <;> simp <;> first
    | exact WithBot.LE.bot_le _
    | exact fun h ↦ nomatch h
    | exact ⟨fun h ↦ by cases h; assumption, fun h ↦ WithBot.LE.coe_le_coe h⟩
```

Everything else in the file — including every `@[to_dual]`-generated `WithTop` lemma — stayed
green. Two lessons:

* **A `rfl` that crosses a wrapper needs a `cases` first.** `Option.map g (Option.map f a)` does
  not reduce for a variable `a`, so the four `map_*` lemmas went from `rfl` to `by cases a <;> rfl`.
* **Keep the statement on the side where the data already lives.** The obvious repair for
  `map f (WithBot.toDual a) = a.map (toDual ∘ f)` is to conjugate both wrappers,
  `= WithBot.toDual (a.map (ofDual ∘ f ∘ toDual))`. But since `WithBot`/`WithTop` are still the
  same `Option`, the shorter `= a.map (f ∘ ⇑toDual)` typechecks and is still `rfl`-after-`cases`.
  Prefer it.
