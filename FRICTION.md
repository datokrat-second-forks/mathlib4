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

## 9. Higher-order unification in *bridge* lemmas

Bridge lemmas that quantify over a relation, such as

```lean
theorem bounded_dual_iff :
    Bounded (fun a b : αᵒᵈ ↦ r (OrderDual.ofDual a) (OrderDual.ofDual b))
      (⇑OrderDual.ofDual ⁻¹' s) ↔ Bounded r s
```

are useless without help at the use site: unifying
`fun a b ↦ ?r (ofDual a) (ofDual b) =?= fun x y ↦ x ≤ y` is a higher-order problem
Lean does not solve, so `?r` stays open and the error surfaces as an
*application type mismatch* several `.trans` steps later. Every one of the
fourteen use sites in `Mathlib/Order/Bounded.lean` needs the relation pinned:

```lean
(bounded_dual_iff (r := (· ≥ ·))).symm.trans
  ((bounded_le_inter_le (α := αᵒᵈ) (s := ⇑OrderDual.ofDual ⁻¹' s) (OrderDual.toDual a)).trans
    (bounded_dual_iff (r := (· ≥ ·))))
```

This is §1 again, one level up: the wrapper now sits *under a binder inside the
argument*, so not even the "pass the dualised argument" trick applies — only a
named argument does.

## 10. Conjugation by hand where the dual used to be the identity

Wherever an `Equiv`/hom/embedding was `Equiv.refl`, `f.toEquiv` or
`f.toEmbedding` because `αᵒᵈ` *was* `α`, it now has to be spelled as a real
conjugation:

```lean
-- Order/Hom/Basic.lean
def dualDual : α ≃o αᵒᵈᵒᵈ := { toEquiv := toDual.trans toDual, map_rel_iff' := Iff.rfl }
def OrderIso.dual (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨OrderDual.ofDual.trans (f.toEquiv.trans OrderDual.toDual), f.le_iff_le⟩
```

For *bundled algebraic* homs the conjugation needs a bundled wrapper, which has
to be introduced privately in the file that needs it:

```lean
-- Algebra/Order/Hom/Monoid.lean
private def toDualAddHom {γ : Type*} [AddZeroClass γ] : γ →+ γᵒᵈ where
  toFun := OrderDual.toDual'; map_zero' := rfl; map_add' _ _ := rfl

theorem antitone_iff_map_nonpos : Antitone (f : α → β) ↔ ∀ a, 0 ≤ a → f a ≤ 0 :=
  monotone_toDual_comp_iff.symm.trans <|
    monotone_iff_map_nonneg (F := α →+ βᵒᵈ) (toDualAddHom.comp (f : α →+ β))
```

Note that the conjugated statement then also differs *in its binders* (§2), so
these proofs usually end in an `OrderDual.forall` / `OrderDual.exists` step too.

Unwrapping-only structure fields are cheap by comparison — `Function.Injective.*`
transport does the whole job, e.g. in `Algebra/Field/Basic.lean`:

```lean
instance : Field Kᵒᵈ := OrderDual.ofDual.injective.field _ rfl rfl (fun _ _ ↦ rfl) …
```

## 11. Quotients: the setoid must be pinned

`Quotient.map'` picks its setoids by instance search, and with `αᵒᵈ` no longer
syntactically `α` the two candidates are genuinely different instances. Leaving
them implicit makes every subsequent field (`left_inv`, `map_rel_iff'`) fail with
opaque mismatches; the fix is to name both:

```lean
-- Order/Antisymmetrization.lean
Quotient.map' (s₁ := AntisymmRel.setoid α (· ≤ ·)) (s₂ := AntisymmRel.setoid αᵒᵈ (· ≤ ·))
  OrderDual.toDual' (fun _ _ h => ⟨h.2, h.1⟩) (OrderDual.ofDual a)
```

Related: term-mode `Quotient.inductionOn'` proofs of the remaining fields had to
become tactic blocks (`cases a with | _ q => induction q using Quotient.inductionOn'`),
because the term-mode versions get re-elaborated at `implicit` transparency and
no longer see through the wrapper.

## 12. When the dual operation has a *different name*, `toDual_inj` stops working

The standard repair for a dualised equation is
`(OrderDual.toDual_inj (b := rhs)).1 (lemma (α := αᵒᵈ) …)`. It only works while
both sides are spelled with the same operations. In a Heyting/Boolean algebra
the dual of `⇨` is `\` and the dual of `ᶜ` is `hnot`, and the dualised statement
therefore mentions `hnot` where the target says `ᶜ` — no injectivity step can
bridge that. Four lemmas in `Order/BooleanAlgebra/Basic.lean` had to be reproved
directly:

```lean
theorem compl_himp : (x ⇨ y)ᶜ = x \ y := by
  rw [himp_eq, sdiff_eq, compl_sup, compl_compl, inf_comm]
theorem codisjoint_himp_self_left : Codisjoint (x ⇨ y) x :=
  codisjoint_iff.2 <| by rw [himp_eq, sup_assoc, compl_sup_eq_top, sup_top_eq]
```

Same conclusion in `Order/Interval/Set/LinearOrder.lean`, for a different reason:
`Ioc_subset_Ioc_iff` used `convert! @Ico_subset_Ico_iff αᵒᵈ …`, which relied on
`Set αᵒᵈ` being `Set α`. With real wrappers `convert` would have to cross a
`ofDual ⁻¹' _` on every subterm, so the four-line direct proof wins.

Rule of thumb from waves 5–8: dualise when the dual statement is the *same
formula* over `αᵒᵈ` (then §1's named arguments suffice); write the proof directly
as soon as the dual notation differs.

## 13. Instances that used to be `‹Fintype α›`

`Fintype αᵒᵈ`, `Finite αᵒᵈ`, `Small.{v} αᵒᵈ` were all *the same instance*, written as
`‹Fintype α›` or `h`. Each now needs an actual transport:

```lean
-- Data/Fintype/Defs.lean; `Fintype.ofEquiv` lives in a later file, so this is by hand
instance OrderDual.fintype (α : Type*) [Fintype α] : Fintype αᵒᵈ where
  elems := ⟨(Finset.univ : Finset α).1.map OrderDual.toDual',
    Multiset.Nodup.map OrderDual.toDual.injective (Finset.univ : Finset α).2⟩
  complete a := Multiset.mem_map.2 ⟨a.ofDual', Finset.mem_univ_val _, rfl⟩

instance OrderDual.finite (α : Type*) [Finite α] : Finite αᵒᵈ := Finite.of_equiv α OrderDual.toDual
instance small_orderDual [Small.{v} α] : Small.{v} αᵒᵈ :=
  small_of_surjective OrderDual.toDual.surjective
```

Note the import ordering trap: the natural transport (`Fintype.ofEquiv`) is defined *downstream*
of the file that needs it, so the instance has to be built at the `Multiset` level instead.

## 14. Duals of *algebraic* synonyms: `Multiplicative αᵒᵈ`

The sharpest edge in wave 9. `LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ)` used to take
its fields straight from the `⊤`/`+` lemmas of `α`, with the instance argument left to `(_)`:

```lean
  zero_mul := @top_add _ (_)                      -- before
  zero_mul a := congrArg OrderDual.toDual' (top_add (OrderDual.ofDual' a.toAdd))   -- after
```

Two things to know here. First, `Multiplicative` is still a plain `def` synonym while `OrderDual`
is a structure, so the two must be peeled in order: `a.toAdd` to leave `Multiplicative`, then
`.ofDual'` to leave the dual.

Second, and worse, *hypotheses* need transport too, and `Ne` does not transport definitionally:
`ha : (0 : Multiplicative αᵒᵈ) < a` gives `ha.ne' : a ≠ 0`, an inequality between elements of
`αᵒᵈ`, while the lemma wants `a.ofDual' ≠ ⊤` in `α`. `Eq` at the two types is not defeq (different
types), so the transport has to be written out:

```lean
  mul_lt_mul_of_pos_left := @fun _ ha _ _ hbc ↦
    add_right_strictMono_of_ne_top (fun h ↦ ha.ne' (congrArg OrderDual.toDual' h)) hbc
```

The `congrArg OrderDual.toDual'` here is doing the work `rfl` used to do silently.

## 15. `WithBot` lemmas proved as `WithTop … (α := αᵒᵈ)`

With `WithBot α` and `WithTop αᵒᵈ` no longer the same type, the cheapest repair is almost never
the `WithBot.toDual` equiv — it is to mirror the two-line `WithTop` proof against the `WithBot`
lemmas, which exist because `@[to_dual]` already generated them:

```lean
theorem mul_ne_bot (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a * b ≠ ⊥ := by simp [mul_eq_bot_iff, *]
theorem bot_lt_mul [LT α] (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b := by
  rw [WithBot.bot_lt_iff_ne_bot] at *; exact mul_ne_bot ha hb
```

The same holds for pointwise duals of a `Pi` family — `@le_cons _ (fun i ↦ (α i)ᵒᵈ) …` for
`Fin.cons_le` — where re-running the original four-line proof is shorter than transporting a
family of wrappers.

## 16. Conversions that were identities can become *traversals*

The wrapper itself is free. Compiling a map over a one-field structure's constructor shows
the constructor erased to the identity:

```
def toWrapTree._lam_0 (x_1 : @& tobj) : tobj := inc x_1; ret x_1   -- this is `Wrap.mk`
def toWrapTree (x_1 : tobj) : tobj := ... Tree.map._redArg x_2 x_1
```

But the `Tree.map` around it survives, and that is an O(n) rebuild of every node to apply
the identity. So the cost of the conversion is not the wrapper — it is whatever structure
has to be walked to push the wrapper inside.

This is the one place where the conversion is not merely a proof-engineering cost. It bites
wherever a *container* of `α` was silently reused as a container of `αᵒᵈ`:

```lean
-- Data/Ordmap/Invariants.lean, before: `Ordnode αᵒᵈ` and `Ordnode α` were the same type
theorem dual_insert (x : α) : ∀ t : Ordnode α,
    dual (Ordnode.insert x t) = @Ordnode.insert αᵒᵈ _ _ x (dual t)
```

`Ordnode.dual` mirrors the tree in place and stays in `Ordnode α`; only the *statement*
crossed to `αᵒᵈ`, for free. Restating it with an element map (`(dual t).map toDual'`) keeps
the statement recognizable but buys a second traversal at every use, in a data structure whose
whole point is the constant factors. The alternative is to dualise the *instances* rather than
the type (`@Ordnode.insert α ⟨fun a b ↦ b ≤ a⟩ _ x (dual t)`), or to generalize `Bounded`/
`Valid'` over the order relation instead of over the type — both keep the runtime cost at zero
and pay in statement noise instead.

Worth checking, whenever a dual lemma mentions a container: is `αᵒᵈ` there because the *order*
is reversed, or because the type synonym happened to be free? Only the first kind should
survive as a type-level dual.

## 17. `(α := αᵒᵈ)` as a *proof* is not a proof any more

The single most common idiom in the order library was to prove the dual statement by
re-instantiating the primal one at `αᵒᵈ`:

```lean
lemma mul_mem_lowerBounds_mul (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    a * b ∈ lowerBounds (s * t) := mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb
```

With `Mᵒᵈ` a structure this stops elaborating: `upperBounds (s : Set Mᵒᵈ)` and
`lowerBounds (s : Set M)` are sets of *different types*. There are three repairs, in order of
preference:

1. **Mirror the proof.** Very often the primal proof is literally self-dual once the statement
   is dualized, because the underlying lemma (`mul_le_mul'`, `image2_subset_iff`) is symmetric:
   ```lean
   lemma mul_mem_lowerBounds_mul … := forall_mem_image2.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)
   ```
   The cost is a duplicated proof, not a harder one.
2. **Go through a bridge lemma** (§18) when the statement genuinely is the primal one
   transported, e.g. `bddAbove_inv`.
3. **Let `@[to_dual]` generate it** where the declaration is tagged — this is the only repair
   that does not duplicate text, and it is why the attribute is worth keeping healthy.

`Mathlib/Algebra/Order/Group/Pointwise/Bounds.lean` alone had 13 such sites
(`mul_mem_lowerBounds_mul`, `subset_lowerBounds_mul`, `BddBelow.range_mul`, `bddAbove_inv`,
`bddBelow_inv`, `isLUB_inv`, `isLUB_inv'`, `isGLB_inv`, `isGLB_inv'`, `BddBelow.range_inv`,
`BddAbove.range_inv`, `IsGLB.mul`, `IsGLB.div`).

## 18. The dual-preimage bridge family

Repairs kept needing "the same bound, one side wrapped", so `Mathlib/Order/Bounds/Basic.lean`
now carries a small family, all stated with `ofDual ⁻¹'` / `toDual ⁻¹'` and all `@[simp]`:

```lean
lemma bddAbove_preimage_ofDual  {s : Set α}            : BddAbove (ofDual ⁻¹' s) ↔ BddBelow s
lemma isLUB_preimage_ofDual     {s : Set α} {a : α}    : IsLUB (ofDual ⁻¹' s) (toDual a) ↔ IsGLB s a
lemma upperBounds_preimage_ofDual {s : Set α}          : upperBounds (ofDual ⁻¹' s) = ofDual ⁻¹' lowerBounds s
```
(plus the `toDual` variants and the `@[to_dual]`-generated `bddBelow_`/`isGLB_`/`lowerBounds_`
partners). Before the conversion all six were `Iff.rfl`/`rfl`; they are the *price of the
wrapper*, paid once, so that downstream sites stay one-liners:

```lean
theorem bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s :=
  ((OrderIso.inv G).bddAbove_preimage (s := ofDual ⁻¹' s)).trans bddAbove_preimage_ofDual
```

The pattern is worth naming: an `e : α ≃o αᵒᵈ` produces a statement about `Set αᵒᵈ`; the
bridge converts it back. `(inv G) ⁻¹' (ofDual ⁻¹' s)` is still *definitionally* `s⁻¹`, so only
the outer bound predicate needs a lemma.

## 19. An `OrderIso α βᵒᵈ` needs its image transported by hand

`OrderIso.smulRightDual β ha : β ≃o βᵒᵈ` (multiplication by a negative scalar). The generic
`e.upperBounds_image` now speaks about `e '' s : Set βᵒᵈ`, and nothing connects that to the
pointwise `a • s : Set β` any more. The image has to be identified explicitly:

```lean
lemma image_smulRightDual (ha : a < 0) (t : Set β) :
    OrderIso.smulRightDual β ha '' t = ⇑OrderDual.ofDual ⁻¹' (a • t) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, congrArg OrderDual.toDual hxy⟩
```

and then each bound lemma is "state it in `Set βᵒᵈ`, then apply `toDual ⁻¹'`":

```lean
@[simp] lemma lowerBounds_smul_of_neg (ha : a < 0) : lowerBounds (a • s) = a • upperBounds s := by
  have h : ⇑ofDual ⁻¹' lowerBounds (a • s) = ⇑ofDual ⁻¹' (a • upperBounds s) := by
    rw [← upperBounds_preimage_ofDual]
    simp only [← image_smulRightDual ha]
    exact (OrderIso.smulRightDual β ha).upperBounds_image
  exact congrArg (⇑toDual ⁻¹' ·) h
```

Note the shape: `congrArg (toDual ⁻¹' ·)` is the *un*-wrapping step, and it works only because
`toDual ⁻¹' (ofDual ⁻¹' X)` is still definitionally `X`. Writing it as a term
(`congrArg _ <| by …`) fails — the expected type does not reach the `by` block and the rewrite
has nothing to fire on; the equation has to be stated in a `have` first.

## 20. `And.left`'s implicit binder is called `a`, and so is `upperBounds`'

Named-argument pinning (§8) collides with anonymous constructor projections:

```lean
h.1 (a := toDual y) hy
-- Application type mismatch: the argument `toDual ?m` … expected `Prop`
--   in the application `@And.left (toDual ?m)`
```

`h.1` is `@And.left {a b : Prop}`, so `(a := …)` binds *there*, not on the membership proof.
The fix is to force the strict-implicit by giving its argument an explicit type instead:

```lean
h.1 (show toDual y ∈ ofDual ⁻¹' s from hy)
```

`(a := …)` stays fine on a plain hypothesis (`hb (a := toDual y) hy`), which is why the idiom
works in some proofs of the same file and not others.
