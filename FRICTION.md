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

## 21. Duality that depended on a *choice* is simply lost

`Set.ordConnectedSection s` is the range of `ordConnectedProj s`, which picks one point of each
order connected component with `Nonempty.some` — i.e. with `Classical.choice`. Before the
conversion `αᵒᵈ` *was* `α`, so the choice made for the dual set was literally the same choice,
and

```lean
theorem dual_ordConnectedSection (s : Set α) :
    ordConnectedSection (ofDual ⁻¹' s) = ofDual ⁻¹' ordConnectedSection s
```

held (by `tauto` after unfolding). With `αᵒᵈ` a structure, `(ofDual ⁻¹' s).Nonempty` is a
*different proposition over a different type*, so `Classical.choice` answers it independently:
the dual section need not be the image of the primal one. The statement is no longer true, and
no proof effort can recover it.

This is the one category of casualty that is not a repair problem but a genuine loss: a lemma
whose content was "the dual construction is the same construction", where "same" meant
definitional identity of the types. The repair is to delete the lemma and mirror its single
consumer — here `compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE` in
`Mathlib/Topology/Order/T5.lean`, which was one `simpa … using!` line and is now the ~25-line
mirror image of the `nhdsGE` proof, carrying a note saying why it cannot be derived by duality.

Worth checking for the same shape elsewhere: any `dual_foo` lemma about a construction that
makes an arbitrary choice (`Nonempty.some`, `Classical.choose`, `Exists.choose`, a chosen
basis, a chosen section) is suspect. Constructions defined by a *property* (`ordConnectedComponent`,
`upperBounds`, `lfp`) dualize fine; constructions defined by a *choice* do not.

## §22 — `(α := αᵒᵈ)` at scale: convert to `@[to_dual]`, but check the fence first

`Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean` had 22 hand-written duals of the
form `ciInf_le := le_ciSup (α := αᵒᵈ) H c`, plus 8 more spelled `gc.dual.l_csSup` /
`e.dual.map_csSup`.  Every one of them broke for the §17 reason.  The file *already* used
`@[to_dual]` for some of its pairs, so the systemic repair is to delete the hand-written dual
and tag the primal:

```lean
-- before
theorem ciInf_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : iInf f ≤ f c :=
  le_ciSup (α := αᵒᵈ) H c
-- after: on the primal, and the dual is deleted
@[to_dual ciInf_le /-- … -/]
theorem le_ciSup {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H (mem_range_self _)
```

**But the fence is real.**  14 of the 22 converted on the first try; 8 did not, and the reason
is informative: `to_dual` translates a proof by replacing each constant with its registered
dual partner, and these proofs used supporting lemmas that had *no registered partner* —
`ciSup_le_iff`/`le_ciInf_iff`, `le_ciSup₂`/`ciInf₂_le`, `ciSup_subtype_fun`/`ciInf_subtype_fun`,
`cbiSup_of_not_bddAbove`/`cbiInf_of_not_bddBelow`, `IsLUB.ciSup_set_eq`/`IsGLB.ciInf_set_eq`.
Each of those pairs already existed as two hand-written declarations; they were simply never
introduced to each other.  So the fix is *registration*, not regeneration:

```lean
attribute [to_dual existing] ciSup_le_iff   -- placed after `le_ciInf_iff` is declared
```

`to_dual existing` adds no declaration and changes no statement — it only records the pairing,
so it is the zero-risk half of this conversion.  Note it must come **after** the dual is
declared (`@[to_dual existing]` on the primal fails with "the translated declaration doesn't
exist" when the partner is further down the file).

**What to verify before deleting a hand-written dual.**  A generated dual is not textually the
old one; `to_dual` flips `≤` in place and keeps the binder names, so e.g. `ciSup_mono`'s
`(B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) : iSup f ≤ iSup g` generates
`(B : BddBelow (range g)) (H : ∀ x, g x ≤ f x) : iInf g ≤ iInf f`, whereas the hand-written
`ciInf_mono` said `(B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : iInf f ≤ iInf g`.  These are
the *same* lemma — unification against a goal `iInf a ≤ iInf b` binds the two spellings
identically — but that has to be checked, not assumed, and it is the one place where a silent
downstream break could hide.  `#check @<dual>` for every generated name and compare positionally.

Attributes travel separately and must be carried over by hand:

```lean
@[gcongr low, to_dual (attr := gcongr low) /-- … -/]   -- both the primal and the dual need it
@[to_dual (attr := norm_cast)]                          -- was @[norm_cast] on both members
```

Verify them behaviourally, not by eye: `gcongr` must still fire the dual, `push_cast` must still
use the generated `WithBot.coe_iSup`.

## §23 — `rintro ⟨x⟩` gives the *constructor* spelling, which simp lemmas do not match

Destructuring an `αᵒᵈ` with `rintro ⟨x⟩` is the cheapest way to get at the underlying element,
but it puts `{ ofDual' := x }` into the goal — the raw structure literal.  `OrderDual.ofDual_toDual`
is stated about the `Equiv` coercion `⇑ofDual (⇑toDual a)`, so it does **not** fire on
`⇑ofDual { ofDual' := x }`, and `dsimp only` leaves the whole detour in place.  Everything
downstream then fails to match too: in `CategoryTheory/Abelian/Subobject.lean` the goal after
`dsimp only [..., Subobject.lift_mk, ...]` was still

```
⊢ Subobject.lift (fun _ f _ => Subobject.mk (cokernel.π f).op) ⋯
      (Subobject.lift (fun _ f _ => Subobject.mk (kernel.ι f.unop)) ⋯
        (OrderDual.ofDual { ofDual' := Subobject.mk f })) = OrderDual.ofDual { ofDual' := Subobject.mk f }
```

with `Subobject.lift_mk` never firing, and the *later* tactics failing on the unreduced
`(MonoOver.mk (kernel.ι (MonoOver.mk f).arrow.unop)).arrow` spelling rather than at the dsimp.

Use the surjectivity of the equiv instead, which introduces the element already wrapped in the
coercion the simp set knows about:

```lean
-- before (worked when `αᵒᵈ` was `α`)
refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))

-- after
refine OrderHom.ext _ _
  (funext (OrderDual.toDual.surjective.forall.2 (Subobject.ind _ ?_)))
...
dsimp only [..., OrderDual.ofDual_toDual]   -- now fires
refine OrderDual.toDual_inj.mpr ?_          -- strip the wrapper off the *goal*
```

`Function.Surjective.forall.2` turns `∀ x : αᵒᵈ, p x` into `∀ a : α, p (toDual a)`, so the
induction principle for `α` applies directly and every `ofDual (toDual _)` cancels by simp.

## §24 — Instances that *deliberately* exploited `Finset αᵒᵈ = Finset α`

`Order/Interval/Finset/Defs.lean` defined the dual `LocallyFiniteOrder` by handing back the
primal interval **unmapped**, and said so in a docstring:

> Note we define `Icc (toDual a) (toDual b)` as `Icc α _ _ b a` (which has type `Finset α` not
> `Finset αᵒᵈ`!) instead of `(Icc b a).map toDual.toEmbedding` as this means the following is
> defeq: `lemma this : (Icc (toDual (toDual a)) (toDual (toDual b)) :) = (Icc a b :) := rfl`

That is exactly the identification the one-field structure removes, so the fence has to come
down: the instance must map.

```lean
-- before
finsetIcc a b := @Icc α _ _ (ofDual b) (ofDual a)
finset_mem_Icc _ _ _ := (mem_Icc (α := α)).trans and_comm

-- after
finsetIcc a b := (@Icc α _ _ (ofDual b) (ofDual a)).map toDual.toEmbedding
finset_mem_Icc _ _ _ := mem_map_equiv.trans <| (mem_Icc (α := α)).trans and_comm
```

What is gained: the twelve `Icc_orderDual_def` / `Icc_toDual` / `Icc_ofDual` bridge lemmas that
used to be proved by `map_refl.symm` are now `rfl` in the `toDual` direction — the map *is* the
definition.  What is lost: the `ofDual` direction (`Icc (ofDual a) (ofDual b) = (Icc b a).map
ofDual.toEmbedding`) is no longer `rfl`, because `map g (map f s)` does not reduce; it needs

```lean
  ext x; rw [mem_map_equiv, mem_Icc, mem_Icc, and_comm]; exact Iff.rfl
```

and the docstring's `rfl` promise is now false and has been rewritten to say so.  Same story for
`LocallyFiniteOrderBot` / `Iic` / `Iio`.

## §25 — Antitone Galois connections encoded as `GaloisConnection (toDual ∘ l) (u ∘ ofDual)`

`fixingSubmonoid_fixedPoints_gc`, `fixingSubgroup_fixedPoints_gc` and `dualAnnihilator_gc` are
stated with the dual baked into the maps, and every consequence was then read off directly:

```lean
theorem fixingSubmonoid_union : fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixingSubmonoid_fixedPoints_gc M α).l_sup
```

`l_sup` now proves an equation in `(Submonoid M)ᵒᵈ`, not in `Submonoid M`.  Three grades of repair,
in increasing order of pain:

1. **Binary operations are defeq**: `⊔` on `αᵒᵈ` unfolds to `⊓`, so only the wrapper is in the way:
   `OrderDual.toDual_inj.mp (gc).l_sup`.  Same for `l_bot`, `u_top`, `u_inf`.
2. **Indexed operations are not**: `⨆ i, toDual (f i)` and `toDual (⨅ i, f i)` are *equal* but not
   defeq (`toDual_iSup` needs a `Set.ext`), so `l_iSup` needs the rewrite put in by hand:
   ```lean
   rw [← OrderDual.toDual_inj, toDual_iInf]
   exact (fixingSubmonoid_fixedPoints_gc M α).l_iSup
   ```
   Left as-is, `u_iInf` does not merely fail — it spends 200000 heartbeats in `isDefEq` first.
3. **`u_iInf` cannot even be `rw`n into place**: the `⨅` that `u_iInf` produces and the `⨅` you
   write in a `have` differ in instance path, so `simp only [key]` / `rw [key]` silently fail to
   match.  Move the mismatch onto a defeq check instead of a syntactic one:
   ```lean
   have key : OrderDual.ofDual (⨅ i, OrderDual.toDual (P i)) = ⨆ i, P i := by
     rw [← toDual_iSup, OrderDual.ofDual_toDual]
   have h := (gc M α).u_iInf (f := fun i => OrderDual.toDual (P i))
   simp only [Function.comp_apply, OrderDual.ofDual_toDual] at h
   exact (congrArg (fun Q : Submonoid M => fixedPoints Q α) key.symm).trans h
   ```
   `Eq.trans` unifies up to defeq, so the instance-path difference stops mattering.

Also beware: `toDual_iSup` is a `simp` lemma, so a `simpa` after `rw [← toDual_iSup]` cheerfully
rewrites your work back.

## 26. `inferInstanceAs (C ιᵒᵈᵒᵈ)` — the double dual is a different type, and the kernel says so

`Mathlib/Order/SuccPred/LinearLocallyFinite.lean` built three declarations out of the idiom

```lean
instance isSuccArchimedean_of_isPredArchimedean [IsPredArchimedean ι] : IsSuccArchimedean ι :=
  inferInstanceAs (IsSuccArchimedean ιᵒᵈᵒᵈ)
```

which worked only because `ιᵒᵈᵒᵈ` *was* `ι`.  With a one-field structure it is a nested structure,
and — worth noting — the elaborator lets these through: the errors arrive from the **kernel**,

```
error: (kernel) declaration type mismatch, '…isSuccArchimedean_of_isPredArchimedean._proof_1'
has type   … IsSuccArchimedean ιᵒᵈᵒᵈ
but it is expected to have type   … IsSuccArchimedean ι
```

so the failure is reported against an auto-generated `_proof_1`/`_aux_1` name and the source
position is the whole declaration.  Do not go looking for a bad instance; look for `ᵒᵈᵒᵈ`.

There is no cheap repair — the statement really has to be proved.  Three shapes worked:

* mirror the primal proof (`isPredArchimedean_of_isSuccArchimedean` → its succ/pred mirror);
* route through a *different* existing construction rather than through the double dual:
  ```lean
  instance [LocallyFiniteOrder ι] [PredOrder ι] : IsPredArchimedean ι :=
    letI := succOrder ι                              -- not `succOrder ιᵒᵈ`
    LinearOrder.isPredArchimedean_of_isSuccArchimedean
  ```
* build the structure by hand, conjugating each field through `toDual`/`ofDual`:
  ```lean
  noncomputable def predOrder [LocallyFiniteOrder ι] : PredOrder ι where
    pred i := OrderDual.ofDual (succFn (OrderDual.toDual i))
    pred_le i := le_succFn (ι := ιᵒᵈ) (OrderDual.toDual i)
    min_of_le_pred {_} h := isMax_toDual_iff.1 (isMax_of_succFn_le (ι := ιᵒᵈ) _ h)
    le_pred_of_lt {_ _} h := succFn_le_of_lt (ι := ιᵒᵈ) _ _ h
  ```
  Each field typechecks because `x ≤ y` in `ιᵒᵈ` *unfolds* to `ofDual y ≤ ofDual x`; only the
  `IsMin`/`IsMax` conclusions need an explicit `isMax_toDual_iff`.

## 27. Order isos that land in the dual (`α ≃o αᵒᵈ`) stop being usable as `α ≃o α`

`OrderIso.inv G : G ≃o Gᵒᵈ` (and `OrderIso.smulRightDual`, `OrderIso.divLeft`, …) used to give
statements about `G` for free, because the codomain `Gᵒᵈ` was `G`.  A whole block of
`Mathlib/Order/Filter/AtTopBot/Group.lean` was built that way:

```lean
theorem map_inv_atBot : map (Inv.inv : G → G) atBot = atTop := (OrderIso.inv G).map_atBot
```

`(OrderIso.inv G).map_atBot : map ⇑(OrderIso.inv G) atBot = (atBot : Filter Gᵒᵈ)` — the two sides
now live in `Filter Gᵒᵈ` and `Filter G`.  Every consequence (`map_inv_atTop`, `comap_inv_atBot`,
`comap_inv_atTop`, `tendsto_inv_atTop_atBot`, `tendsto_inv_atTop_iff`, …) fails the same way.

Two repairs, both used:

1. **Re-found the block on a tendsto pair.**  Prove the two `Tendsto` facts directly from the
   order-reversing lemmas of the theory itself, then get the filter equalities from involutivity:
   ```lean
   theorem tendsto_inv_atTop_atBot : Tendsto (Inv.inv : G → G) atTop atBot :=
     tendsto_atBot.2 fun b => (eventually_ge_atTop b⁻¹).mono fun _ hx => inv_le'.2 hx

   theorem map_inv_atBot : map (Inv.inv : G → G) atBot = atTop :=
     le_antisymm tendsto_inv_atBot_atTop <|
       calc (atTop : Filter G) = map ((Inv.inv : G → G) ∘ Inv.inv) atTop := by
             rw [inv_involutive.comp_self, map_id]
         _ = map Inv.inv (map Inv.inv atTop) := map_map.symm
         _ ≤ map Inv.inv atBot := map_mono tendsto_inv_atTop_atBot
   ```
   `comap` then comes from `comap_map inv_injective`, and the `tendsto_inv_atTop_iff` family from
   `tendsto_comap_iff`.
2. **Keep the dual iso, cross back over with the preimage bridges.**  When the dual iso is the
   actual content (`OrderIso.smulRightDual`, i.e. `x ↦ a • x` for `a < 0`), pair
   `image_smulRightDual` with the `isLUB_preimage_ofDual` / `isGLB_preimage_ofDual` bridges:
   ```lean
   -- sInf (a • s) = a • sSup s, for a < 0
   refine (?_ : IsGLB (a • s) (a • sSup s)).csInf_eq hs.smul_set
   rw [← isLUB_preimage_ofDual, ← image_smulRightDual ha']
   exact (OrderIso.smulRightDual ℝ ha').isLUB_image'.2 (isLUB_csSup hs h)
   ```
   This is much shorter than mirroring `Real.sSup_smul_of_nonneg`, and it keeps the antitone iso
   where it belongs.

Related, and cheap: in a `CategoryTheory.Equivalence` built from `dual`, the *counit* component is
`(dual ⋙ dual).obj X ≅ X`, so `OrderIso.dualDual X` is now the wrong direction there and must be
`(OrderIso.dualDual X).symm` (`Order/Category/DistLat.lean`, `LinOrd.lean`; `Lat.lean` and
`Preord.lean` already carried the fix).

## 28. Definitions that were *two* definitions related by "unseal and it's `rfl`"

`Mathlib/SetTheory/Ordinal/FixedPointApproximants.lean` defined `lfpApprox` and `gfpApprox` as two
separate well-founded recursions and then proved every `gfpApprox` lemma from its `lfpApprox`
sibling by definitional equality, under an explicit comment:

```lean
-- By unsealing these recursive definitions we can relate them by definitional equality
unseal gfpApprox lfpApprox
theorem gfpApprox_le {a : Ordinal} : gfpApprox f x a ≤ x := le_lfpApprox (α := αᵒᵈ)
```

That worked because `αᵒᵈ` *was* `α`, so `lfpApprox (OrderHom.dual f) x a` and
`gfpApprox f x a` were literally the same term after unfolding. With `OrderDual` a structure the
two are terms of different types, and the identity has to become a theorem:

```lean
private theorem lfpApprox_dual (a : Ordinal.{u}) :
    lfpApprox (OrderHom.dual f) (OrderDual.toDual x) a = OrderDual.toDual (gfpApprox f x a) := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    rw [lfpApprox, gfpApprox]
    simp only [toDual_inf, toDual_iInf]
    congr 1
    exact iSup_congr fun b => iSup_congr fun hb => by rw [ih b hb]; rfl
```

and each of the 18 downstream lemmas becomes "take the `lfpApprox` lemma at `OrderHom.dual f` with
`x := toDual x`, `rw [lfpApprox_dual]`, strip `toDual` with `OrderDual.toDual_inj`":

```lean
theorem gfpApprox_add_one (hx : f x ≤ x) (a : Ordinal) :
    gfpApprox f x (a + 1) = f (gfpApprox f x a) := by
  have h := lfpApprox_add_one (OrderHom.dual f) (x := OrderDual.toDual x) hx a
  rw [lfpApprox_dual, lfpApprox_dual, dual_apply_toDual, OrderDual.toDual_inj] at h
  exact h
```

Three sub-frictions worth noting.

* `rw` does not fire on a `Set` membership whose unfolding is the equation you want to rewrite in:
  `gfpApprox f x c ∈ fixedPoints f` needs an explicit
  `show f (gfpApprox f x c) = gfpApprox f x c` first.
* A hypothesis obtained by instantiating a lemma at `OrderDual.toDual x` can come back displayed as
  the constructor `{ ofDual' := x }`, and then `rw [lfpApprox_dual] at h` finds no occurrence of the
  pattern `lfpApprox _ (OrderDual.toDual ?x) ?a`. Rewriting the *goal* backwards
  (`rw [← OrderDual.toDual_inj, ← dual_apply_toDual, ← lfpApprox_dual]; exact h`) and letting
  `exact` do the defeq check works where rewriting the hypothesis does not. Same phenomenon as §23.
* `lfp`/`gfp` themselves are still related by `rfl`
  (`(OrderHom.dual f).lfp = OrderDual.toDual f.gfp`), but unification cannot *invert* that, so
  `OrderDual.toDual_inj.1` on a goal whose RHS is `(OrderHom.dual f).lfp` fails. Introduce the
  identity as a named `have hlfp : … := rfl` and `rw [hlfp]` instead of relying on it silently.

## 29. Instances that were literally `‹_›` (`instance : C Xᵒᵈ := ‹C X›`)

Every structure carried "without change" onto the dual was spelled by *handing back the same
instance*:

```lean
instance : Bornology αᵒᵈ := ‹Bornology α›
instance OrderDual.instTopologicalSpace : TopologicalSpace Xᵒᵈ := ‹_›
instance OrderDual.instDiscreteTopology [DiscreteTopology X] : DiscreteTopology Xᵒᵈ := ‹_›
```

Each of these now has to *transport* the structure along `toDual`, and the choice of transport is
a real decision, because it fixes which downstream lemmas stay `rfl`:

```lean
-- Mathlib/Topology/Bornology/Basic.lean
instance instBornology : Bornology αᵒᵈ where
  cobounded := (Bornology.cobounded α).map toDual
  le_cofinite := (map_mono (Bornology.le_cofinite α)).trans toDual.injective.tendsto_cofinite

-- Mathlib/Topology/Constructions.lean
instance OrderDual.instTopologicalSpace : TopologicalSpace Xᵒᵈ := .coinduced toDual ‹_›
```

`coinduced toDual` was chosen over the propositionally equal `induced ofDual` because it makes
`IsOpen (toDual ⁻¹' s) ↔ IsOpen s` (and hence the `IsClosed` version) hold by `Iff.rfl`; the
`induced` form hides an existential and none of the block's lemmas would be definitional.  The
cost of the transport is that everything downstream of the instance turns from `‹_›`/`.id` into a
proof: `continuous_toDual := continuous_coinduced_rng`, `isOpenMap_ofDual` needs
`Equiv.image_eq_preimage_symm`, and `nhds_toDual : 𝓝 (toDual x) = map toDual (𝓝 x)` — free when
`Xᵒᵈ` was `X` — is now a two-step `le_antisymm` between the continuity of `toDual` and of
`ofDual`.  The same happens for `𝓝[>] (toDual x)`, which is no longer *syntactically* `𝓝[<] x`:

```lean
instance OrderDual.instNeBotNhdsWithinIoi [h : (𝓝[<] x).NeBot] : (𝓝[>] toDual x).NeBot := by
  have : 𝓝[>] toDual x = map toDual (𝓝[<] x) := by
    rw [nhdsWithin, nhdsWithin, nhds_toDual, Filter.map_inf toDual.injective,
      Filter.map_principal, Equiv.image_eq_preimage_symm, OrderDual.toDual_symm_eq, Set.Ioi_toDual]
  rw [this]; exact h.map _
```

Note the signature drift this forces: `nhds_ofDual` used to be stated for `x : X` (because
`Xᵒᵈ = X`); it now has to take `x : Xᵒᵈ`.

## 30. A file whose second half is its first half at `αᵒᵈ`

`Mathlib/Order/LiminfLimsup.lean` derived every `liminf`/`bliminf`/`limsInf` statement from its
`limsup` sibling by instantiating the lattice at `αᵒᵈ` — 31 sites, e.g.
`bliminf_eq_liminf := blimsup_eq_limsup (α := αᵒᵈ)`.  None of these typecheck any more: the
function `u : β → α` is not a function into `αᵒᵈ`.

The cheap repair is *four definitional bridges*, one per operator, stated once at the top of the
file — they are all `rfl`, because `sInf` on the dual is `sSup` on the nose:

```lean
private lemma limsup_toDual_comp :
    limsup (fun b ↦ OrderDual.toDual (u b)) f = OrderDual.toDual (liminf u f) := rfl
private lemma liminf_toDual_comp :
    liminf (fun b ↦ OrderDual.toDual (u b)) f = OrderDual.toDual (limsup u f) := rfl
-- and the two `blimsup`/`bliminf` versions
```

with the standard consumer being

```lean
theorem liminf_eq_iSup_iInf {f : Filter β} {u : β → α} : liminf u f = ⨆ s ∈ f, ⨅ a ∈ s, u a := by
  rw [← OrderDual.toDual_inj, ← limsup_toDual_comp]
  simp only [toDual_iSup, toDual_iInf]
  exact limsup_eq_iInf_iSup
```

Two things the bridges do **not** cover:

* **Boundedness side conditions.**  `IsBoundedUnder (· ≥ ·) f u` and
  `IsBoundedUnder (· ≤ ·) f (toDual ∘ u)` quantify over `α` and `αᵒᵈ` respectively, so they are
  *not* defeq — the `∃ b` ranges over a different type.  Two more private bridges are needed, and
  every `by isBoundedDefault` autoParam then has to be passed explicitly:
  ```lean
  private lemma isBoundedUnder_le_toDual :
      IsBoundedUnder (· ≤ ·) f (fun b ↦ OrderDual.toDual (u b)) ↔ IsBoundedUnder (· ≥ ·) f u :=
    ⟨fun ⟨b, hb⟩ ↦ ⟨OrderDual.ofDual b, hb⟩, fun ⟨b, hb⟩ ↦ ⟨OrderDual.toDual b, hb⟩⟩
  ```
* **Quantifiers in the statement.**  `∀ y > x, …` at `αᵒᵈ` is a `∀` over `αᵒᵈ`, so the transported
  statement needs an explicit shuttle, not `rfl`:
  ```lean
  (limsup_le_iff (β := βᵒᵈ) … ).trans
    ⟨fun h y hy ↦ h (OrderDual.toDual y) hy, fun h y hy ↦ h (OrderDual.ofDual y) hy⟩
  ```

Where the primal proof was three lines, mirroring it (`sInf_le` → `le_sSup`, `csInf_lt` →
`lt_csSup`, `iInf_split` → `iSup_split`, `left_eq_inf` → `left_eq_sup`) is shorter and more robust
than transporting; where it was fifteen (`HasBasis.liminf_eq_ite`), transporting through the
bridges plus `apply_ite OrderDual.toDual` wins.

## 31. Data structures indexed by the order: `LTSeries αᵒᵈ` is not `LTSeries α`

`Mathlib/Order/KrullDimension.lean` is the sharpest case so far of §30 raised to *data*.  The whole
`coheight` half of the file was written as "`height` at `αᵒᵈ`", and it worked because the
reversal of a series, `RelSeries.reverse`, produced a term that was *literally* a `LTSeries αᵒᵈ`:

```lean
lemma length_le_coheight {x : α} {p : LTSeries α} (hhead : x ≤ p.head) : p.length ≤ coheight x :=
  length_le_height (α := αᵒᵈ) (p := p.reverse) (by simpa)
```

Now `LTSeries α = RelSeries ((· < ·) : Rel α α)` and `LTSeries αᵒᵈ = RelSeries ((· < ·) : Rel αᵒᵈ αᵒᵈ)`
are series over *different types*, and `p.reverse : RelSeries (SetRel.inv (· < ·))` is a third thing
again.  Every one of the ~30 `coheight` lemmas broke at once.

The repair is a transport written out by hand, kept private to the file:

```lean
private def LTSeries.dual (p : LTSeries α) : LTSeries αᵒᵈ where
  length := p.length
  toFun i := OrderDual.toDual (p i.rev)
  step _ := p.strictMono (Fin.rev_lt_rev.2 Fin.castSucc_lt_succ)

private def LTSeries.dualEquiv : LTSeries α ≃ LTSeries αᵒᵈ where
  toFun := LTSeries.dual
  invFun := LTSeries.ofDual
  left_inv p := RelSeries.ext rfl (funext fun i ↦ congrArg p (Fin.rev_rev i))
  right_inv q := RelSeries.ext rfl (funext fun i ↦ congrArg q (Fin.rev_rev i))
```

plus the four `simp` lemmas `dual_length`, `dual_apply`, `dual_head`, `dual_last` (and their
`ofDual` mirrors) that say reversal swaps head and last.  With those, the site above becomes

```lean
  length_le_height (α := αᵒᵈ) (p := LTSeries.dual p) (by simpa using hhead)
```

Three lessons:

* **`coheight` had to be redefined**, not just reproved: `coheight a := height (OrderDual.toDual a)`.
  It was previously `height (α := αᵒᵈ) a`, which no longer typechecks.  Once it is *definitionally*
  `height (toDual a)`, the four bridge lemmas `height_toDual`, `coheight_ofDual` are `rfl`, and only
  the two that cross the double dual (`height_ofDual`, `coheight_toDual`) need the reindexing
  argument `height_toDual_toDual`, proved by `Equiv.iSup_congr (dualEquiv.trans dualEquiv)`.
* **Dot notation does not survive.**  `p.dual` fails: `LTSeries` is an `abbrev` for `RelSeries`, so
  the resolver looks for `RelSeries.dual`.  All uses have to be spelled `LTSeries.dual p`.
* **Higher-order unification needs help.**  Bridging a bounded quantifier with `Iff.trans` puts the
  shuttle's predicate in a non-pattern position, so it must be supplied:
  `(coe_lt_height_iff (α := αᵒᵈ) (x := toDual x) hfin).trans (exists_lt_toDual_iff (p := fun y ↦ height y = n))`.

## 32. `α ≃o αᵒᵈ` used to be an automorphism (`OrderIso.compl`)

`Mathlib/Combinatorics/SetFamily/AhlswedeZhang.lean`:

```lean
@[simp] lemma compl_truncatedSup (s : Finset α) (a : α) :
    (truncatedSup s a)ᶜ = truncatedInf sᶜˢ aᶜ := map_truncatedSup (OrderIso.compl α) _ _
```

`map_truncatedSup (e : α ≃o β)` transports `truncatedSup` along `e`.  Instantiated at
`e := OrderIso.compl α : α ≃o αᵒᵈ` it produces a statement about `truncatedSup` **in `αᵒᵈ`**, which
used to *be* `truncatedInf` in `α` — same type, and `sup'` at `αᵒᵈ` is `inf'` by unfolding the
`OrderDual` instance.  It is now a genuinely different statement about a different type, and no
amount of `simp` closes the gap (`Finset αᵒᵈ` vs `Finset α`, `lowerClosure` vs `upperClosure`,
`sup'` vs `inf'`).

Cheaper than building a `truncatedSup`-on-the-dual bridge: prove the complement lemma directly,
by the induction that the defeq was hiding, and derive its partner by complementing both sides.

```lean
  have key : ∀ (t : Finset α) (H : t.Nonempty), (t.sup' H id)ᶜ = t.inf' H compl := by
    intro t H
    induction H using Finset.Nonempty.cons_induction with
    | singleton b => simp
    | cons b t hb ht ih =>
      rw [Finset.sup'_cons (H := ht), Finset.inf'_cons (H := ht), compl_sup, ih]; rfl
  …
@[simp] lemma compl_truncatedInf (s : Finset α) (a : α) :
    (truncatedInf s a)ᶜ = truncatedSup sᶜˢ aᶜ := by
  rw [← compl_inj_iff, compl_compl, compl_truncatedSup, compls_compls, compl_compl]
```

One tactic note that recurs whenever a `Finset` is rewritten under `sup'`/`inf'`: the nonemptiness
proof is a dependent argument, so `rw [hfilter]` fails with "motive is not type correct".
`Finset.inf'_congr _ hfilter (fun _ _ ↦ rfl)` rewrites the index set and carries the proof along.

## 33. Instances that were `‹C α›` and carry a *field* that must agree with another instance

§29 collected the instances that were literally `instance : C Xᵒᵈ := ‹C X›`.  `UniformSpace` is the
same shape but with a twist: a `UniformSpace` carries its own `toTopologicalSpace` field, and `Xᵒᵈ`
already has a topology instance from `Mathlib/Topology/Constructions.lean`.  Transporting the
uniformity naively,

```lean
instance OrderDual.instUniformSpace [UniformSpace α] : UniformSpace αᵒᵈ :=
  UniformSpace.comap OrderDual.ofDual ‹_›     -- topology := induced ofDual
```

would put a *second*, only propositionally equal, topology on `αᵒᵈ` (`induced ofDual` versus the
`coinduced toDual` instance) — a genuine diamond, and the kind that only bites three files later.
Mathlib's tool for exactly this is `replaceTopology`, which keeps the ambient instance as the
structure field:

```lean
instance OrderDual.instUniformSpace [UniformSpace α] : UniformSpace (αᵒᵈ) :=
  (UniformSpace.comap OrderDual.ofDual ‹_›).replaceTopology <| by
    refine TopologicalSpace.ext_iff.2 fun s ↦ ⟨fun hs ↦ ⟨_, hs, rfl⟩, ?_⟩
    rintro ⟨u, hu, rfl⟩
    exact hu
```

The two preimage round-trips in that proof (`ofDual ⁻¹' (toDual ⁻¹' s) = s`) are `rfl` by structure
eta, so the whole obligation is four lines.  **Rule of thumb for the rest of the campaign:** when a
class carries another class as a field, transport it with the `replace…` combinator, never with a
bare `comap`/`induced`.

## 34. A type synonym whose entire API rested on a chain of identifications

`AddValuation R Γ₀` is *defined* as `Valuation R (Multiplicative Γ₀ᵒᵈ)`, and the whole 300-line API
was written as if `Multiplicative Γ₀ᵒᵈ` were `Γ₀`:

```lean
instance : FunLike (AddValuation R Γ₀) R Γ₀ :=
  inferInstanceAs <| FunLike (Valuation R <| Multiplicative Γ₀ᵒᵈ) R <| Multiplicative Γ₀ᵒᵈ

@[simp] theorem map_zero : v 0 = (⊤ : Γ₀) := Valuation.map_zero v
```

42 errors, but only *one* real decision: how the coercion reads values back.  Composing it with the
two inverse wrappers keeps everything else definitional —

```lean
instance : FunLike (AddValuation R Γ₀) R Γ₀ where
  coe v r := OrderDual.ofDual (Multiplicative.toAdd
    (DFunLike.coe (F := Valuation R (Multiplicative Γ₀ᵒᵈ)) v r))
  coe_injective _ _ h := …
```

because `Multiplicative` and `OrderDual` are both one-field structures, so
`toValuation v r ≡ Multiplicative.ofAdd (OrderDual.toDual (v r))` by eta, in both directions.  That
is what makes `⊤ ↔ 0`, `+ ↔ *`, `min ↔ max` and the reversed `≤` all pass through untouched: every
*inequality* lemma (`map_le_add`, `map_lt_sum'`, `map_sub`) went through unchanged.

What does **not** pass through is an `Eq`: `a = b` in `Multiplicative Γ₀ᵒᵈ` and its image in `Γ₀`
are equations *at different types*, so they need a transport.  Two private one-liners cover all of
them:

```lean
private lemma val_congr {Γ : Type*} {a b : Multiplicative Γᵒᵈ} (h : a = b) :
    OrderDual.ofDual (Multiplicative.toAdd a) = OrderDual.ofDual (Multiplicative.toAdd b) :=
  congrArg _ h
private lemma addVal_congr {Γ : Type*} {a b : Γ} (h : a = b) :
    Multiplicative.ofAdd (OrderDual.toDual a) = Multiplicative.ofAdd (OrderDual.toDual b) :=
  congrArg (fun x ↦ Multiplicative.ofAdd (OrderDual.toDual x)) h
```

`map_zero := val_congr (Valuation.map_zero v)`, `ext := Valuation.ext fun r ↦ addVal_congr (h r)`,
and so on down the file.  Note the second one's proof: `congrArg _ h` guesses the *wrong* function
(`⇑Multiplicative.ofAdd` alone) — the composite has to be spelled out.

One module-system trap: a `private` lemma may not appear in the body of a **public `def`**
(`AddValuation.map`), only inside proofs.  Either inline the `congrArg` there or turn on
`backward.privateInPublic`.

## 35. Parallel synonyms: `Colex` was `Lex` read at `ιᵒᵈ`

`Mathlib/Data/DFinsupp/Lex.lean` derives the entire colexicographic order from the lexicographic
one by dualising the *index*: `instance Colex.total_le := Lex.total_le (ι := ιᵒᵈ)`, twelve times.
That worked because `Π₀ i : ιᵒᵈ, α i` was `Π₀ i : ι, α i`; now the index type genuinely differs and
no equiv rescues an *instance* cheaply.

Each one has to be proved again, which is short because the underlying `Pi.Colex` API already
exists in parallel — with one real piece of work, the case split, which for `Lex` looks at the
*smallest* index where two functions differ and for `Colex` at the *largest*:

| `Lex`                        | `Colex`                        |
|------------------------------|--------------------------------|
| `(f.neLocus g).min`          | `(f.neLocus g).max`            |
| `Finset.min_eq_top`          | `Finset.max_eq_bot`            |
| `Finset.notMem_of_lt_min`    | `Finset.notMem_of_max_lt`      |
| `Finset.min'` / `min'_le`    | `Finset.max'` / `le_max'`      |

The one gap this exposed upstream: `Pi.Lex` has an `IsOrderedCancelMonoid` instance and `Pi.Colex`
did not (it never needed one — `Colex` was `Lex` at `ιᵒᵈ`).  Its mirror is now next to it in
`Mathlib/Algebra/Order/Group/PiLex.lean`.

## 36. `toDual` does not commute with a big operator definitionally

`Finset.sum`, `List.sum`, `Multiset.sum`, `Finset.sup`/`inf` are folds, so
`toDual (∑ i ∈ s, f i)` and `∑ i ∈ s, toDual (f i)` are *not* defeq — the fold would have to
commute with the map, which is exactly the content of an induction.  Wherever a lemma used to be
"the same statement at `βᵒᵈ`", the transport now needs one bridge per operator:

```lean
private lemma sum_smul_toDual (t : Finset ι) (u : ι → α) (v : ι → β) :
    ∑ i ∈ t, u i • toDual (v i) = toDual (∑ i ∈ t, u i • v i) := by
  classical
  induction t using Finset.cons_induction with
  | empty => rfl
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih]; rfl
```

with which `AntivaryOn.card_smul_sum_le_sum_smul_sum` is again a one-liner:

```lean
  have h := hfg.dual_right.sum_smul_sum_le_card_smul_sum
  simpa only [Function.comp_def, sum_toDual, sum_smul_toDual, smul_toDual, nsmul_toDual,
    OrderDual.toDual_le_toDual] using h
```

Pointwise operations are the opposite: `a • toDual b = toDual (a • b)` and
`toDual a + toDual b = toDual (a + b)` are `rfl`, so they only ever need to be *named* to be used
as rewrite rules (`toDual_add`, `toDual_smul` at root already exist; `smul_toDual`/`nsmul_toDual`
were local one-liners).  For `Finset.sup`/`inf` the named lemmas exist too — `Finset.toDual_inf`,
`Finset.toDual_sup'` — but their statements use `⇑toDual ∘ f`, so a lambda-shaped restatement is
worth a line when you want to `rw` with them:

```lean
private lemma toDual_support_inf (s : Finset A) (degt : A → T) :
    OrderDual.toDual (s.inf degt) = s.sup fun a ↦ OrderDual.toDual (degt a) :=
  Finset.toDual_inf s degt
```

## 37. A class whose *topology* is a parameter cannot be transported by `‹_›`

`UniformSpace` carries its topology in a field (§33); `WeakPseudoEMetricSpace`/`WeakEMetricSpace`
are the other shape — the topology is a *parameter*, and the class states `topology_le` and
`topology_eq_on_restrict` relative to it.  Either way `instance : C Xᵒᵈ := ‹C X›` is now
ill-typed, and the repair is the combinator Mathlib already has for pulling a structure back
along a map:

```lean
instance OrderDual.instWeakPseudoEMetricSpace [TopologicalSpace X] [WeakPseudoEMetricSpace X] :
    WeakPseudoEMetricSpace Xᵒᵈ :=
  WeakPseudoEMetricSpace.IsInducing (f := ofDual)
    ⟨by
      refine TopologicalSpace.ext_iff.2 fun s ↦ ⟨fun hs ↦ ⟨_, hs, rfl⟩, ?_⟩
      rintro ⟨u, hu, rfl⟩
      exact hu⟩ ‹_›
instance [PseudoEMetricSpace X] : PseudoEMetricSpace Xᵒᵈ :=
  (PseudoEMetricSpace.induced ofDual ‹_›).replaceUniformity (by rfl)
```

The `⟨by …⟩` is `IsInducing (ofDual : Xᵒᵈ → X)`, i.e. the proof that the campaign's
`OrderDual.instTopologicalSpace := .coinduced toDual` agrees with `.induced ofDual`.  It has to be
written out *inline*: an `instance` is a public `def`, so a `private theorem` may not appear in its
body (§34), and every topology-flavoured `Xᵒᵈ` instance needs this same three-line proof again.

**Open design question.** Defining `OrderDual.instTopologicalSpace := .induced ofDual ‹_›` instead
would make `IsInducing ofDual` literally `⟨rfl⟩`, would let `OrderDual.instUniformSpace` drop its
`replaceTopology`, and matches Mathlib's convention for type synonyms (`ULift.down`,
`Subtype.val`).  The cost is that `OrderDual.isOpen_preimage_toDual` stops being `Iff.rfl` and that
every module downstream of `Mathlib/Topology/Constructions.lean` rebuilds; that file is also where
any shared `isInducing_ofDual` lemma would have to live, at the same rebuild cost.

## 38. `simpa … using h` finishes at reducible transparency

`OrderDual` props are defeq at *default* transparency (`toDual x ≤ toDual y` ≡ `y ≤ x`), and
`exact` accepts them.  `simpa … using h` does not: its final step is a reducible-transparency
match, so a term that `exact` would take is rejected with "After simplification, term … has type".
Split it:

```lean
  have hx := Set.ext_iff.1 h (OrderDual.toDual x)
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_Iio] at hx
  simp only [Set.mem_iUnion, Set.mem_Ici, Set.mem_Ioi]
  exact hx
```

The simp lemmas have to be applied to the hypothesis and the goal *separately*, because they are
different lemmas (`Iic`/`Iio` on `αᵒᵈ` against `Ici`/`Ioi` on `α`).  Note also that a `toDual`
which the unifier produced comes back as the constructor `{ ofDual' := f i }`, so simp lemmas
stated with `⇑toDual` do not fire on it.

## 39. Antitone Galois connections into `(Set X)ᵒᵈ`

`zeroLocus`/`vanishingIdeal` (and `orthogonalBilin`, `annihilator`/`torsionBySet`, …) are stated as
a `GaloisConnection` whose right-hand order is `(Set X)ᵒᵈ`.  The two maps now have to say so:

```lean
theorem gc_ideal :
    @GaloisConnection (Ideal A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun I => OrderDual.toDual (zeroLocus 𝒜 I)) fun t =>
      (vanishingIdeal (OrderDual.ofDual t)).toIdeal :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal (OrderDual.ofDual t) I
```

and then each consumer picks up one of three fixes: feed a `toDual` where a set was passed
(`(gc_set _) s (OrderDual.toDual t)`), strip a `toDual` from a conclusion
(`OrderDual.toDual_inj.1 (gc_ideal 𝒜).l_sup`), or — for the `iSup`/`iInf` forms, which are big
operators (§36) — insert the bridge:

```lean
  OrderDual.toDual_inj.1 <| (gc_ideal 𝒜).l_iSup.trans (toDual_iInf _).symm
```

`l_bot`, `l_sup`, `u_inf` need no bridge: `⊥`, `⊔`, `⊓` on `αᵒᵈ` are `toDual ⊤`, `toDual ∘ ⊓`,
`toDual ∘ ⊔` definitionally.  Named arguments are worth checking — `GaloisConnection.u_inf` binds
`b₁`/`b₂`, not `a`/`b`.

## 40. `(α := αᵒᵈ)` is only a transport when the *statement* stays at one type

The wave-23 sweep separated two kinds of `(α := αᵒᵈ)` one-liners.  Where the statement is about
elements and props only, the transport survives with a bridge for the data
(`iSup_eq_of_forall_le_of_tendsto (α := αᵒᵈ) hle (tendsto_toDual_iff.2 hlim)`).  Where the
statement mentions a *set*, a *function space* or an *order-indexed structure* at `α`, the dual
statement is about `Set αᵒᵈ`/`β → αᵒᵈ`/`LTSeries αᵒᵈ` (§31) and there is nothing to transport —
the proof has to be mirrored:

```lean
theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) := fun x hx y hy a b ha hb hab =>
  calc
    r = a • r + b • r := (Convex.combo_self hab _).symm
    _ ≤ a • x + b • y :=
      add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
```

Mirroring is mechanical but not free: `MonotoneOn.convex_ge` swaps `max_rec'`/`Convex.combo_le_max`
for `min_rec'`/`Convex.min_le_combo`, `nhds_atBot` re-runs `nhds_atTop`'s `simp only` with `atBot`,
and `DFinsupp.Colex.wellFoundedLT` re-runs `Lex.wellFounded'` at `r := (· > ·)` (which needs
`Std.Trichotomous (· > ·)`, one line: `⟨fun a b h₁ h₂ ↦ Std.Trichotomous.trichotomous a b h₂ h₁⟩`).

## 41. A class carrying *two* structures, with no `induced` combinator in scope

`PseudoMetricSpace` bundles a uniformity **and** a bornology, and `PseudoMetricSpace.induced` lives
in `Pseudo/Constructions.lean`, i.e. downstream of the file where the `αᵒᵈ` instance has to be
declared.  So the instance is written out, with both carried fields pinned to the `OrderDual`
instances that already exist (`OrderDual.instUniformSpace`, `OrderDual.instBornology`) and their
two coherence fields proved by hand:

```lean
instance : PseudoMetricSpace αᵒᵈ where
  dist x y := dist (ofDual x) (ofDual y)
  dist_self _ := dist_self _
  dist_comm _ _ := dist_comm _ _
  dist_triangle _ _ _ := dist_triangle _ _ _
  edist x y := edist (ofDual x) (ofDual y)
  edist_dist _ _ := edist_dist _ _
  toUniformSpace := inferInstance
  uniformity_dist := (Metric.uniformity_basis_dist.comap _).eq_biInf
  toBornology := inferInstance
  cobounded_sets := Set.ext fun s ↦ by
    show (OrderDual.toDual ⁻¹' s) ∈ Bornology.cobounded α ↔ _
    rw [← Filter.mem_sets, PseudoMetricSpace.cobounded_sets (α := α)]
    exact ⟨fun ⟨C, hC⟩ ↦ ⟨C, fun x hx y hy ↦ hC (OrderDual.ofDual x) hx (OrderDual.ofDual y) hy⟩,
      fun ⟨C, hC⟩ ↦ ⟨C, fun x hx y hy ↦ hC (OrderDual.toDual x) hx (OrderDual.toDual y) hy⟩⟩
```

The `show` is the whole trick for the bornology: `cobounded αᵒᵈ` is `(cobounded α).map toDual`, so
`s ∈ cobounded αᵒᵈ` is *definitionally* `toDual ⁻¹' s ∈ cobounded α`, and after that the two
`∃ C` statements only differ by where `ofDual` sits.

## 42. `OrderTopology αᵒᵈ`

The old proof was `rcases …; simp_rw [Preorder.topology, or_comm]; rfl`: with `αᵒᵈ = α` the two
generated topologies were literally the same term up to `or_comm`.  Now the instance is
`.coinduced toDual`, and the bridge is `induced_generateFrom_eq` plus the interval table
(`Set.Iic_toDual : Iic (toDual a) = ofDual ⁻¹' Ici a`, and `Ioi`/`Iio`/`Ici` likewise):

```lean
instance [t : OrderTopology α] : OrderTopology αᵒᵈ := by
  have hind : (OrderDual.instTopologicalSpace : TopologicalSpace αᵒᵈ) =
      TopologicalSpace.induced OrderDual.ofDual ts := by
    refine TopologicalSpace.ext_iff.2 fun s ↦
      ⟨fun hs ↦ ⟨OrderDual.toDual ⁻¹' s, hs, rfl⟩, ?_⟩
    rintro ⟨u, hu, rfl⟩
    exact hu
  constructor
  rw [hind, t.topology_eq_generate_intervals]
  simp only [Preorder.topology]
  rw [induced_generateFrom_eq]
  congr 1
  ext s
  …
```

Two things to know when writing this: the instance argument has to be named (`ts` from the file's
`variable` line) — an `inferInstance` in the `have` will not match the goal — and the witness in
`⟨toDual ⁻¹' s, hs, rfl⟩` has to be given explicitly, or the elaborator cannot see which set to
take the preimage of.

## 43. An existential over `αᵒᵈ` is not an existential over `α`

`∃ z : αᵒᵈ, p z` and `∃ z : α, q z` are never defeq — the binder types differ — even when `p` and
`q` agree pointwise under `toDual`.  So `countable_image_gt_image_Ioi (α := αᵒᵈ) f` no longer
typechecks, and the transport goes through the subset relation instead of an equality of sets:

```lean
theorem countable_image_gt_image_Ioi_within … := by
  refine (countable_image_lt_image_Ioi_within (α := αᵒᵈ) t fun x ↦ OrderDual.toDual (f x)).mono ?_
  rintro x ⟨hx, z, hz, hz'⟩
  exact ⟨hx, OrderDual.toDual z, hz, hz'⟩
```

`Set.Countable.mono` wants the subset proof in tactic position: as a term argument the target set
is still a metavariable when the `⟨…⟩` is elaborated, and the anonymous constructor fails.

## 44. `𝓝[<]` / `𝓝[≤]` dualization needs a `nhdsWithin` transport lemma

Every `s ∈ 𝓝[<] a ↔ …` result in `Topology/Order/LeftRightNhds.lean` used to be
`… (α := αᵒᵈ)` plus a `simpa`, because `𝓝[<] a` and `𝓝[>] (toDual a)` were the same filter on
the same type.  They are now different filters on different types, and the `simp` set contains
nothing that relates them: the interval simp lemmas rewrite `Ioi (toDual b)` to
`ofDual ⁻¹' Iio b`, and there the rewriting stops.

Two private lemmas restore all of it at once:

```lean
private theorem nhdsWithin_toDual (x : X) (t : Set X) :
    𝓝[ofDual ⁻¹' t] (toDual x) = map toDual (𝓝[t] x) := by
  rw [nhdsWithin, nhdsWithin, nhds_toDual, Filter.map_inf OrderDual.toDual.injective,
    Filter.map_principal, Equiv.image_eq_preimage_symm, OrderDual.toDual_symm_eq]

@[simp]
private theorem mem_nhdsWithin_toDual {x : X} {s t : Set X} :
    ofDual ⁻¹' s ∈ 𝓝[ofDual ⁻¹' t] (toDual x) ↔ s ∈ 𝓝[t] x := by
  rw [nhdsWithin_toDual, Filter.mem_map]; rfl
```

With `mem_nhdsWithin_toDual` in the simp set, `simpa using! TFAE_mem_nhdsGT h.dual (ofDual ⁻¹' s)`
works again unchanged — the existential and interval parts of those statements were already
handled by the interval `to_dual` simp lemmas.  The `= ⊥` variants need the filter form plus
`Filter.map_eq_bot_iff`.

The same three-line `rw` chain now appears in `Topology/Constructions.lean` (twice),
`Topology/Order/Basic.lean` and here; it is the strongest argument so far for promoting this
vocabulary to `Topology/Constructions.lean` next to `nhds_toDual`.

## 45. Big operators do not commute with `toDual` — the `Finset.sum` case

Known for `iSup`/`iInf` (§ earlier); `Finset.sum` is the same story and has no library lemma.
`Analysis/Convex/Jensen.lean` derives every concave statement from the convex one at
`toDual ∘ f`, which produces `∑ i ∈ t, w i • toDual (f (p i))` where the goal wants
`toDual (∑ i ∈ t, w i • f (p i))`.  Note the direction: the library simp lemma
`OrderDual.toDual_smul` pushes `toDual` *inward*, which is exactly the wrong way, so the
collecting lemmas must be given explicitly:

```lean
private lemma smul_toDual (c : 𝕜) (b : β) : c • toDual b = toDual (c • b) := rfl
private lemma sum_toDual (t : Finset ι) (g : ι → β) :
    ∑ i ∈ t, toDual (g i) = toDual (∑ i ∈ t, g i) := by
  induction t using Finset.cons_induction with
  | empty => rfl
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih]; rfl
```

and then every site is `simpa only [Function.comp_apply, smul_toDual, sum_toDual,
OrderDual.toDual_le_toDual, OrderDual.toDual_lt_toDual, OrderDual.toDual_inj] using hf.dual.foo …`.
`Finset.sup'`/`inf'` and `BddAbove`/`BddBelow` already have their bridges in the library
(`Finset.toDual_inf'`, `bddAbove_preimage_ofDual`).

Wave 33 hit the same wall in `Topology/Semicontinuity/Basic.lean` (`UpperSemicontinuousWithinAt.sum`)
and there the induction is avoidable: the `AddEquiv` is free, so `map_sum` does the whole job.

```lean
private lemma toDual_finset_sum {ι' : Type*} (a : Finset ι') (f : ι' → γ) :
    OrderDual.toDual (∑ i ∈ a, f i) = ∑ i ∈ a, OrderDual.toDual (f i) :=
  map_sum ({ toEquiv := OrderDual.toDual, map_add' := fun _ _ ↦ rfl } : γ ≃+ γᵒᵈ) f a
```

Which underlines what is actually missing: not the algebra — `map_add'` is `rfl` — only the
indexed transport lemma. Same shape as §61's missing `atTop`/`atBot` bridges.

Also: a transport written as `Foo (β := βᵒᵈ) hf` makes the *unifier* produce the function
`fun x ↦ { ofDual' := f x }`, on which no `toDual` simp lemma fires.  Rewriting the site to use
the explicit `hf.dual` (`ConcaveOn.dual : ConcaveOn 𝕜 s f → ConvexOn 𝕜 s (toDual ∘ f)`) gives
`⇑toDual ∘ f` instead, and the simp set applies.

## 46. A class whose field mentions the type's own order: `IsLower`/`IsUpper`

`IsUpper α` is `t = upper α`, so `IsUpper αᵒᵈ` is a statement about `coinduced toDual t`, and
`topology_eq_lowerTopology (α := α)` no longer proves it.  What carries the whole file is three
private lemmas:

```lean
private lemma coinduced_toDual_eq (t : TopologicalSpace α) :
    TopologicalSpace.coinduced toDual t = TopologicalSpace.induced ofDual t
private lemma induced_ofDual_injective {t₁ t₂ : TopologicalSpace α}
    (h : TopologicalSpace.induced ofDual t₁ = TopologicalSpace.induced ofDual t₂) : t₁ = t₂
private lemma induced_ofDual_lower [Preorder α] :
    TopologicalSpace.induced ofDual (lower α) = upper αᵒᵈ
```

the last by `rw [lower, upper, induced_generateFrom_eq]` and a two-way `rintro` on the generating
family, where both directions are `rfl` (`ofDual ⁻¹' (Ici a)ᶜ` *is* `(Iic (toDual a))ᶜ`).
`induced_ofDual_injective` is what makes the `IsUpper αᵒᵈ ↔ IsLower α` direction work, which no
instance can give you.

For the twenty-odd *statements* in the `IsUpper` namespace the honest fix is to mirror the
`IsLower` proof rather than transport it: they are two to five lines each and dualize
mechanically (`Ici`↔`Iic`, `sup'`↔`inf'`, `⊥`↔`⊤`, `Ioi_inter_Ioi` for `Iio_inter_Iio`).
Transport is only worth it for the two long ones, and there it goes through
`ofDual ⁻¹' U` plus `Set.preimage_eq_preimage OrderDual.ofDual.surjective`.

## 47. `atTop`/`atBot` on a dual, and on a *subtype* of a dual

`atTop : Filter αᵒᵈ` is no longer `atBot : Filter α`; the transports need
`Tendsto toDual atBot atTop` and friends, which are one-liners but have to exist:

```lean
private lemma tendsto_toDual_atBot [Preorder ι] : Tendsto (toDual : ι → ιᵒᵈ) atBot atTop :=
  tendsto_atTop.2 fun b ↦ mem_of_superset (Iic_mem_atBot (ofDual b)) fun _ hx ↦ hx
```

The subtype version is what `SupConvergenceClass`/`InfConvergenceClass` need, because their field
quantifies over `s → α` for `s : Set α`:

```lean
private lemma tendsto_subtype_ofDual [Preorder α] {s : Set αᵒᵈ} :
    Tendsto (fun y : s ↦ (⟨ofDual y.1, y.2⟩ : ↥(toDual ⁻¹' s))) atTop atBot :=
  tendsto_atBot.2 fun b ↦ mem_of_superset (Ici_mem_atTop (⟨toDual b.1, b.2⟩ : ↥s)) fun _ hx ↦ hx
```

Both the membership proof and the order comparison go through unchanged (`fun _ hx ↦ hx`) because
subtype `≤` unfolds to the carrier's `≤`, which unfolds through `toDual`; only the *types* differ.

One `rw` trap: `iSup_comp_ofDual : ⨆ i : ιᵒᵈ, g (ofDual i) = ⨆ i, g i` fires for `g := f` but not
for `g := fun i ↦ toDual (f i)` — `?g (ofDual i)` is not a Miller pattern, so `rw` needs the
function supplied explicitly, `rw [iSup_comp_ofDual (fun i ↦ OrderDual.toDual (f i))]`.

## 48. A whole file of `(α := αᵒᵈ)` one-liners: mirror, do not transport

`Topology/Order/IsLUB.lean` is the extreme case — 28 of its declarations were literally
`IsLUB.foo (α := αᵒᵈ) ha hs`. Two dozen separate transports would each have needed the
`𝓝[≥]`/`𝓝[≤]` bridge, `isLUB_preimage_ofDual`, and an image/preimage rewrite. Mirroring the
primal proof was shorter *in every single case but two*:

```lean
-- before
theorem IsGLB.frequently_mem (ha : IsGLB s a) (hs : s.Nonempty) : ∃ᶠ x in 𝓝[≥] a, x ∈ s :=
  IsLUB.frequently_mem (α := αᵒᵈ) ha hs
-- after: the LUB proof with Ioc↦Ico, Iio↦Ioi, `<` flipped
theorem IsGLB.frequently_mem (ha : IsGLB s a) (hs : s.Nonempty) : ∃ᶠ x in 𝓝[≥] a, x ∈ s := by
  rcases hs with ⟨a', ha'⟩
  intro h
  rcases (ha.1 ha').eq_or_lt with (rfl | haa')
  · exact h.self_of_nhdsWithin le_rfl ha'
  · rcases (mem_nhdsGE_iff_exists_Ico_subset' haa').1 h with ⟨b, hab, hb⟩
    rcases ha.exists_between hab with ⟨b', hb's, hb'⟩
    exact hb hb' hb's
```

The reason mirroring is cheap is that *every* ingredient of the primal proof already has its dual
under the same name, generated by `@[to_dual]`: `lowerBounds_closure`, `lowerBounds_mono_set`,
`isGLB_congr`, `isGLB_ciInf_set`, `BddBelow.closure`, `ciInf_of_not_bddBelow`,
`IsGLB.inter_Iic_of_mem`, `isGLB_Ioo`, `isOpen_gt'`, `le_csSup_of_le`. The transport, by contrast,
has to *cross* the type boundary, and the boundary is exactly where `αᵒᵈ ≠ α` bites. Rule of thumb
that held for all 28: mirror whenever the primal proof is under ten lines; transport only when the
dual appears inside a binder you cannot mirror away.

The two survivors are informative. One is a genuine `∀`-binder mismatch (§49); the other,
`IsGLB.exists_seq_strictAnti_tendsto_of_notMem`, was mirrored too, because the transport would have
needed `IsCountablyGenerated (𝓝 (toDual x))` — an instance nobody has, since `𝓝 (toDual x)` is
`map toDual (𝓝 x)` and the instance search does not see through that.

## 49. `∀ b : αᵒᵈ` is not `∀ b : α`, even when the body is defeq

The one place transport still won in `IsLUB.lean`:

```lean
theorem eventually_const_le_iff_forall_lt_eventually_const_lt {f : γ → α} {a : α} :
    (∀ᶠ x in l, a ≤ f x) ↔ ∀ b, b < a → ∀ᶠ x in l, b < f x := by
  have h := eventually_le_const_iff_forall_gt_eventually_lt_const (α := αᵒᵈ)
    (l := l) (f := fun x ↦ toDual (f x)) (a := toDual a)
  exact h.trans ⟨fun H b hb ↦ H (toDual b) hb, fun H b hb ↦ H (ofDual b) hb⟩
```

The LHS transports by `rfl` (`toDual (f x) ≤ toDual a` *is* `a ≤ f x`), and so does the body of the
RHS; what does not transport is the quantifier `∀ b : αᵒᵈ` against `∀ b : α`. The repair is three
tokens of `Equiv`-plumbing done by hand — `H (toDual b) hb` and `H (ofDual b) hb` — and it is the
same repair every time a dualized statement quantifies over the carrier. Under the old
type-synonym this whole `Iff` was `Iff.rfl`.

## 50. Two kinds of debris left by the annotate campaign

Both showed up in this file and both must go when a real proof lands:

* `set_option backward.isDefEq.respectTransparency false in` in front of `isGLB_of_mem_nhds`,
  `IsGLB.exists_seq_strictAnti_tendsto_of_notMem`, `IsGLB.exists_seq_antitone_tendsto` — the option
  was hiding the fact that the transport never really typechecked, only unified at low transparency.
* `simpa using!` — `exists_seq_strictAnti_tendsto'`, `Dense.exists_seq_strictAnti_tendsto_of_lt`,
  `DenseRange.exists_seq_strictAnti_tendsto_of_lt`. `using!` is a request to close the goal by
  brute force; with the synonym gone there is nothing left for it to close.

Unrelated to `OrderDual` but worth one line, since it cost a compile: a statement written with the
projection, `IsClosed (lowerClosure s).1`, does not accept `▸` with a lemma about the coercion
`↑(lowerClosure s)` — the goal displays `.carrier` and the rewrite finds neither side. `show
IsClosed (lowerClosure s : Set α)` first.

## 51. Order embeddings and Galois connections *into* a dual

Three shapes recur once the frontier reaches order-theoretic API rather than topology:

```lean
-- ValuationSubring: an OrderEmbedding whose codomain is a dual
toFun A := OrderDual.toDual A.nonunits
inj' _ _ h := nonunits_injective (OrderDual.toDual_inj.1 h)

-- Nullstellensatz: a GaloisConnection with a dual on the right
GaloisConnection (fun I ↦ OrderDual.toDual (zeroLocus K I)) (fun V ↦ vanishingIdeal k (ofDual V))

-- Lie/Submodule, Spectrum/Prime/Noetherian: well-foundedness across the dual
(wellFoundedLT_dual_iff _).1 <| RelHomClass.isWellFounded (e.dual.ltEmbedding)
```

None of these are hard, but all three used to be invisible: the `toDual`/`ofDual` were `id`, so
`toFun A := A.nonunits` and `fun V ↦ vanishingIdeal k V` typechecked directly. The cost is one
`toDual`/`ofDual` per field and one `toDual_inj.1` per injectivity obligation — mechanical, but it
touches the *definition*, not a proof, so it is API-visible churn.

## 52. The codomain-dual toolkit: five one-liners buy back twenty transports

§48 says mirror rather than transport. That verdict is about the *domain* dual. When only the
codomain is dualized — the `AntitoneOn f s → MonotoneOn (⇑toDual ∘ f) s` idiom, spelled
`Af.dual_right` — transport wins, because the obstruction is always one of the same five, and each
is a one-liner (`Topology/Order/Monotone.lean`, twenty sites):

```lean
private lemma image_toDual_comp {f : α → β} {s : Set α} :
    (⇑toDual ∘ f) '' s = ⇑ofDual ⁻¹' (f '' s) := by
  rw [Set.image_comp, Equiv.image_eq_preimage_symm, OrderDual.toDual_symm_eq]

private lemma sSup_image_toDual [InfSet β] {f : α → β} {s : Set α} :
    sSup ((⇑toDual ∘ f) '' s) = toDual (sInf (f '' s)) := by
  rw [image_toDual_comp, toDual_sInf]

private lemma tendsto_toDual_comp_nhds_iff [TopologicalSpace β] {l : Filter α} {f : α → β} {b : β} :
    Tendsto (⇑toDual ∘ f) l (𝓝 (toDual b)) ↔ Tendsto f l (𝓝 b) :=
  ⟨fun h ↦ (continuous_ofDual.tendsto _).comp h, fun h ↦ (continuous_toDual.tendsto _).comp h⟩

private lemma continuousWithinAt_toDual_comp_iff [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {s : Set α} {x : α} :
    ContinuousWithinAt (⇑toDual ∘ f) s x ↔ ContinuousWithinAt f s x :=
  tendsto_toDual_comp_nhds_iff
```

(plus `sInf_image_toDual` and `continuousAt_toDual_comp_iff`.) With those, a transport is two lines:

```lean
lemma AntitoneOn.tendsto_nhdsLT (Af : AntitoneOn f (Iio x)) (h_bdd : BddBelow (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x))) := by
  have h := MonotoneOn.tendsto_nhdsLT Af.dual_right
    (by rw [image_toDual_comp]; exact bddAbove_preimage_ofDual.2 h_bdd)
  rwa [sSup_image_toDual, tendsto_toDual_comp_nhds_iff] at h
```

Why this direction is the cheap one: `toDual_sSup : toDual (sSup s) = sInf (⇑ofDual ⁻¹' s)` is still
`rfl`, and the preimage/image dictionary (`image_toDual_comp`, `bddAbove_preimage_ofDual`,
`upperBounds_preimage_ofDual`) is already in the library. The domain dual has no such dictionary —
it needs a `nhdsWithin` transport per site (§44), which is why mirroring wins there.

Two spelling traps in the toolkit. `AntitoneOn.dual_right` produces `⇑toDual ∘ f` with an honest
`Function.comp`, so every bridge must be stated with `⇑toDual ∘ f`, not `fun y ↦ toDual (f y)` —
`rw` will not cross that gap. And `Set.Countable.preimage toDual.injective` lands on
`toDual (f x) = toDual b`, which is *not* defeq to `f x = b` for a structure; a
`simpa only [Set.preimage_ofPred_eq, Function.comp_apply, OrderDual.toDual_inj]` is required where
the synonym needed nothing.

## 53. `show P (toDual ∘ f) from h` — the retyping idiom is gone

Six sites in `Topology/Order/Monotone.lean` read

```lean
theorem AntitoneOn.map_sSup_of_continuousWithinAt (Cf : ContinuousWithinAt f s (sSup s)) … :
    f (sSup s) = sInf (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sSup s) from Cf) Af fbot
```

`show … from Cf` was pure notation: under the type synonym the two statements were the same term.
Now it is a real coercion. Either §52's `continuousWithinAt_toDual_comp_iff.2 Cf`, or — better here,
because the file already proves the conditionally-complete versions — drop the transport and mirror
through them:

```lean
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h, fbot]
  · exact Af.map_csSup_of_continuousWithinAt Cf h
```

The whole `map_csSup`/`map_csInf` block, in turn, mirrors onto the four `IsLUB`/`IsGLB`-of-tendsto
lemmas repaired in §48's file — `IsGLB.isLUB_of_tendsto` for the antitone-at-an-infimum case, and so
on. One file's honest proofs are the next file's transport-free ingredients; this is the pattern the
whole campaign keeps rewarding.

## 54. `to_dual` does not flip `lt`/`gt` in names — only the intervals

A trap that costs a compile and reads as a mysterious `hm : m < f x` vs. expected `f x < m`.
`Topology/Order/Basic.lean` has both

```lean
@[to_dual] theorem countable_image_lt_image_Ioi_within (t : Set β) (f : β → α) :
    Set.Countable {x ∈ t | ∃ z, f x < z ∧ ∀ y ∈ t, x < y → z ≤ f y}
@[to_dual] theorem countable_image_gt_image_Ioi_within (t : Set β) (f : β → α) :
    Set.Countable {x ∈ t | ∃ z, z < f x ∧ ∀ y ∈ t, x < y → f y ≤ z}
```

The generated duals are `countable_image_lt_image_Iio_within` and
`countable_image_gt_image_Iio_within` — the `lt`/`gt` part of the name stays put while the
*statement's* inequality flips. So the dual of the `lt`-named lemma is the `lt`-named one over
`Iio`, and it states `∃ z, z < f x ∧ …`. Both names exist and both typecheck where you need one, so
the wrong pick fails several lines later, inside the proof, not at the reference.

## 55. Instances that were `‹C G›` or `inferInstanceAs (C αᵒᵈ)`

Two idioms for "the dual has the same structure", both now unavailable:

```lean
-- Topology/Algebra/Group/ContinuousInv: was ‹ContinuousInv G›
instance OrderDual.instContinuousInv : ContinuousInv Gᵒᵈ :=
  ⟨continuous_toDual.comp (continuous_inv.comp continuous_ofDual)⟩

-- Topology/Separation/LinearUpperLowerSetTopology: was inferInstanceAs (CompletelyNormalSpace αᵒᵈ)
-- now the ten-line IsUpperSet proof, mirrored, with the two `conv … equals` targets swapped
```

The first repair is the general shape for any *structural* class carried along the equivalence:
sandwich the underlying operation between `continuous_toDual` and `continuous_ofDual`. It survives
`@[to_additive]` unchanged, since the two bridges say nothing about the order. The second has no
such shape — `CompletelyNormalSpace` is a `Prop`-valued class whose field quantifies over sets, so
transporting it would need the set-level dictionary; mirroring the proof is much shorter.

## 56. When the *definition* is the transport

`Function.rightLim` was not a theorem about the dual; it *was* the dual:

```lean
noncomputable def Function.rightLim (f : α → β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ f a
```

`f : α → β` is no longer a function `αᵒᵈ → β` and `a : α` is no longer a term of `αᵒᵈ`, so the
definition itself stops elaborating — every one of the file's ~30 dual declarations fails at once,
downstream of a single line. Two ways out:

* (a) keep the transport and insert the coercions:
  `@Function.leftLim αᵒᵈ β _ _ (f ∘ ⇑OrderDual.ofDual) (OrderDual.toDual a)`;
* (b) define `rightLim` directly, mirroring `leftLim`'s `if 𝓝[>] a = ⊥ ∨ ¬∃ y, … then f a else
  limUnder (𝓝[>] a) f`.

Chosen: (a). It is meaning-preserving, and — decisively — it keeps
`rightLim f a = leftLim (f ∘ ofDual) (toDual a)` true *by `rfl`*, which is the currency every
transport in the file is paid in. Under (b) that equation becomes a theorem whose proof has to
reconcile `Preorder.topology αᵒᵈ` with `Preorder.topology α`, and the `Monotone.dual` transports in
the same file (which mix a domain and a codomain dual) would have to be re-derived from scratch.
The cost of (a) is that the coercion `f ∘ ofDual` is visible in every unfolded goal.

## 57. `‹C E›`-style dual instances: use `where`, not the structure copy

`Analysis/Normed/Group/Constructions.lean` had four instances of the form "the dual carries the
same normed structure", written as a structure copy that silently reused the primal's fields. Under
the synonym-as-structure they produce ~100 errors between them (one per downstream `‖·‖` rewrite).
The repair is uniform and shorter than the original:

```lean
instance (priority := 100) seminormedGroup [SeminormedGroup E] : SeminormedGroup Eᵒᵈ where
  dist_eq x y := SeminormedGroup.dist_eq (ofDual x) (ofDual y)
```

`where` lets Lean synthesize the parent instances (`Norm Eᵒᵈ`, `PseudoMetricSpace Eᵒᵈ`, the group)
from the ones already in scope and leaves exactly one field to prove, and that field's proof is the
primal field read at `ofDual x`. Note the field is `dist x y = ‖x⁻¹ * y‖`, so `dist_eq_norm_div`
(which wants `SeminormedCommGroup`) is the wrong ingredient — reach for the class projection.

## 58. `simpa … using h` closes at reducible transparency; `exact` does not

The single most common last-line failure of this wave. `toDual u ≤ toDual v` and `v ≤ u` are
definitionally equal, but unfolding the `LE Eᵒᵈ` instance is not a *reducible* step, so

```lean
  simpa only [leftLim_toDual_comp] using this
  -- Type mismatch: After simplification, term `this` has type
  --   OrderDual.toDual (leftLim f x) ≤ OrderDual.toDual (f y)
  -- but is expected to have type  f y ≤ leftLim f x
```

Two repairs, in order of preference: put `OrderDual.toDual_le_toDual` (and `toDual_lt_toDual`,
`toDual_inj`) into the simp set so the flip happens *propositionally*; or, when the residue is an
instance-path mismatch rather than a flip — `@LE.le β inst✝.toSemilatticeInf.toLE …` vs
`@LE.le β ConditionallyCompleteLattice.….toLE …` — split into `simp only [...] at h; exact h`,
since `exact` checks at default transparency and accepts what `simpa` refuses.

## 59. The eighth private copy of the `nhdsWithin` bridge

```lean
private theorem nhdsWithin_toDual {X : Type*} [TopologicalSpace X] (s : Set X) (a : X) :
    𝓝[⇑ofDual ⁻¹' s] (toDual a) = Filter.map toDual (𝓝[s] a) := by
  rw [nhdsWithin, nhdsWithin, nhds_toDual, Filter.map_inf toDual.injective, Filter.map_principal,
    Equiv.image_eq_preimage_symm, OrderDual.toDual_symm_eq]
```

This is now the eighth file carrying its own copy (waves 33 added
`Topology/EMetricSpace/BoundedVariation.lean` and a second block in
`Topology/Order/LeftRightLim.lean`), together with the specializations `𝓝[<] (toDual a)
= map toDual (𝓝[>] a)` and `𝓝[≤] (toDual a) = map toDual (𝓝[≥] a)` and the `Tendsto` corollaries
that follow from it by `Filter.tendsto_map'_iff` / `Filter.map_le_map_iff toDual.injective`. Every
one of them used to be `rfl` — that is precisely why the library never named them. They are the
natural public companions of the existing `nhds_toDual`, and each new topology-order file on the
frontier needs them again. Whether to promote them (in `Topology/Constructions.lean`, beside
`nhds_toDual`) is a design decision for the campaign owner; until it is taken, they stay private and
duplicated, which is the honest way to leave the question open.

## 60. A statement that can no longer be *stated*

`AlgebraicGeometry/AffineSpace.lean` documents, with an `example`, that `Spec R` and
`(PrimeSpectrum R)ᵒᵈ` carry the same order but not the same instance:

```lean
example (R : CommRingCat) :
    inferInstance (α := Preorder (Spec R)) = inferInstance (α := Preorder (PrimeSpectrum R)ᵒᵈ) := by
  aesop (add simp spec_le_iff)
```

The equality typechecked only because `Preorder (Spec R)` and `Preorder (PrimeSpectrum R)ᵒᵈ` were
literally the same type — the synonym made `↥(Spec R)` and `(PrimeSpectrum R)ᵒᵈ` the same carrier.
With the structure, the two `Preorder`s live on different types and `=` no longer applies; there is
no coercion to insert, because it is the *statement* that has become ill-typed, not the proof.

This is a different failure from every other in this document, and worth flagging as such: the file
was recording an observation *about* the synonym. The repair states the same warning in a form that
survives — the `Spec R` preorder is the one lifted along `toDual`:

```lean
example (R : CommRingCat) :
    inferInstance (α := Preorder (Spec R)) =
      Preorder.lift fun p : Spec R ↦ OrderDual.toDual (show PrimeSpectrum R from p) := by
  refine Preorder.ext fun p q ↦ ?_
  aesop (add simp spec_le_iff)
```

Note that the campaign *improves* this file: the thing the comment warns about ("these instances are
not definitionally equal") is now enforced by the type system rather than by a comment.

## 61. No `atTop`/`atBot` bridge exists, so filter duals get mirrored

The order-filter API has no counterpart of `nhds_toDual` — nothing says
`atTop (αᵒᵈ) = map toDual (atBot α)`. So every `cocompact_le_atBot (α := αᵒᵈ)`-style transport in
`Topology/Order/Compact.lean` has to be mirrored instead (five lines each, all ingredients dual by
`@[to_dual]`), while the `nhds`-based ones in `Topology/Order/LeftRightLim.lean` transport in two.
The asymmetry is purely a question of which dictionary entries the library happens to have. Adding
the two `atTop`/`atBot` transports would be a small, self-contained public addition — noted here
rather than done, since new public API is out of this campaign's scope. Wave 33 produced the
second private copy, in `Topology/EMetricSpace/BoundedVariation.lean`:

```lean
private theorem atTop_dual {X : Type*} [Preorder X] :
    (atTop : Filter Xᵒᵈ) = Filter.map (toDual : X → Xᵒᵈ) atBot := by
  have h : (atTop : Filter Xᵒᵈ) = Filter.comap (ofDual : Xᵒᵈ → X) atBot := by
    simp only [atTop, atBot, Filter.comap_iInf, Filter.comap_principal]
    exact (OrderDual.toDual.surjective.iInf_comp fun a : Xᵒᵈ => 𝓟 (Ici a)).symm
  rw [h, Filter.map_eq_comap_of_inverse (m := (toDual : X → Xᵒᵈ)) (n := ofDual) rfl rfl]
```

together with its `𝓟 t ⊓ atBot` companion. Two copies is the threshold at which the question
stops being hypothetical.

## 62. A dual bridge stated as an `Iff` whose function is `?g ∘ toDual` costs a heartbeat timeout

Wave 33, `Mathlib/Topology/EMetricSpace/BoundedVariation.lean`. The natural bridge to write is

```lean
private theorem tendsto_comp_toDual_iff {f : X → Y} {t : Set X} {a : X} {l : Filter Y} :
    Tendsto (f ∘ ⇑ofDual) (𝓝[⇑ofDual ⁻¹' t] (toDual a)) l ↔ Tendsto f (𝓝[t] a) l
```

Used in argument position it is fine; used to *produce* a `Tendsto (?g ∘ ⇑ofDual) …` goal, the
function is a metavariable applied under a composition, so elaboration falls into higher-order
unification and six call sites died with `(deterministic) timeout at whnf`, 200000 heartbeats.
The rule the wave taught: an iff bridge is safe exactly when the relevant side mentions the
function as a *bare* metavariable (`UpperSemicontinuousWithinAt ?f s x`, first-order); the moment
it appears as `?g ∘ toDual`, it is not.

Three repairs, all of which keep every function rigid:

* state the bridge **one-directionally**, so the function comes from the hypothesis and is never
  a metavariable:

  ```lean
  private theorem tendsto_comp_ofDual (h : Tendsto f (𝓝[t] a) l) :
      Tendsto (f ∘ ⇑ofDual) (𝓝[⇑ofDual ⁻¹' t] (toDual a)) l := by
    rw [nhdsWithin_toDual, Filter.tendsto_map'_iff]; exact h
  ```

* in result position, rewrite the hypothesis instead of the goal:
  `have H := …; rw [nhdsWithin_toDual, Filter.tendsto_map'_iff] at H; exact H` — all first-order;

* where the *set* is what has to be guessed (`Ici (toDual a)` against `⇑ofDual ⁻¹' ?t`), pin it:
  `tendsto_comp_ofDual (t := s ∩ Ioi x) h'f`.

The same rule governs a family of sites in `Mathlib/Topology/Semicontinuity/Basic.lean`. There the
symptom is an application type mismatch rather than a timeout, but the cause is identical —
`ContinuousAt.comp`'s `?g ∘ ?f` has nothing rigid to bite on, so Lean guesses
`?f := Prod.mk (f x)` and the proof falls apart:

```lean
-- fails
  ContinuousAt.comp_lowerSemicontinuousWithinAt (δ := δᵒᵈ) (continuous_toDual.continuousAt.comp hg) …
-- works
  ContinuousAt.comp_lowerSemicontinuousWithinAt (δ := δᵒᵈ) (g := ⇑OrderDual.toDual ∘ g)
    (continuous_toDual.continuousAt.comp hg) …
```

At the doubly-dualised sites the inner `.comp` needs pinning too:
`hg.comp (f := ⇑OrderDual.ofDual) (x := OrderDual.toDual (f x)) continuous_ofDual.continuousAt`.

## 63. `Sort*`, not `Type*`, in a bridge over an index type

The `ciSup`/`iSup` semicontinuity lemmas need two things. First, `⨆ i, toDual (g i)` is *not*
defeq to `toDual (⨅ i, g i)`: `iSup` goes through `Set.range`, and membership in the range of
`fun i ↦ toDual (g i)` is an equality **in the dual type** (`∃ i, toDual (g i) = toDual x`), which
the structure does not see through. So the transported statement has to be corrected by
`simp only [← toDual_iInf] at H` before the semicontinuity bridge applies — the same crack as §49.

Second, the boundedness hypothesis needs its own bridge:

```lean
private lemma bddAbove_range_toDual {ι : Sort*} {g : ι → β} (h : BddBelow (Set.range g)) :
    BddAbove (Set.range fun i ↦ toDual (g i))
```

and it must be `ι : Sort*`. Written with `Type*` it fails with the unsolvable universe constraint
`?u + 1 =?= u_4` — `Set.range`'s index universe is a `Sort` level, and the semicontinuity file's
index variable really is a `Sort*`. The error surfaces as a type mismatch between two `range`
applications that print identically apart from their universe arguments, which is worth
recognising on sight.

## 64. `X → Eᵒᵈ` is not `X → E`: the Pi-dual transport has to go through an image

`Topology/Semicontinuity/Lindelof.lean` derives the lower-semicontinuous statement from the upper
one by `exists_countable_upperSemicontinuous_isGLB (E := Eᵒᵈ) h𝓕_cont h𝓕`. That one-liner depended
on `X → Eᵒᵈ` *being* `X → E`, so that a `𝓕 : Set (X → E)` could be re-read as a family of dual-valued
functions without moving. It cannot survive.

The repair is the general shape for any dual transport whose data is a *function into* the dualised
type: conjugate by `Φ f = ⇑toDual ∘ f`, apply the theorem to `Φ '' 𝓕`, and pull the answer back
along `Ψ g = ⇑ofDual ∘ g`.

```lean
  set Φ : (X → E) → (X → Eᵒᵈ) := fun f ↦ ⇑OrderDual.toDual ∘ f
  set Ψ : (X → Eᵒᵈ) → (X → E) := fun g ↦ ⇑OrderDual.ofDual ∘ g
  have hΦΨ : ∀ g, Φ (Ψ g) = g := fun _ ↦ rfl
  have hGLB : ∀ {𝓖 : Set (X → E)} {t : X → E}, IsLUB 𝓖 t → IsGLB (Φ '' 𝓖) (Φ t) := fun {𝓖 t} h ↦
    ⟨by rintro _ ⟨f, hf, rfl⟩; exact h.1 hf,
      fun g hg ↦ h.2 (show Ψ g ∈ upperBounds 𝓖 from fun f hf ↦ hg ⟨f, hf, rfl⟩)⟩
```

Everything inside the two bridges is `rfl` at the leaves — `f ≤ t` on `X → E` and `Φ t ≤ Φ f` on
`X → Eᵒᵈ` are the same proposition, pointwise — but the *sets* differ, so the two `⟨f, hf, rfl⟩`
image witnesses and the round trip `Set.image_image` … `Set.image_id` are unavoidable. Round trip:

```lean
  refine ⟨Ψ '' 𝓖, ?_, 𝓖_count.image _, hLUB ?_⟩
  · rintro _ ⟨g, hg, rfl⟩; obtain ⟨f, hf, rfl⟩ := 𝓖_sub hg; exact hf
  · rwa [Set.image_image, show (fun g ↦ Φ (Ψ g)) = id from funext hΦΨ, Set.image_id]
```

Worth knowing: Mathlib already contains exactly the missing tool, as a **private** definition —
`dualPiOrderIso : (∀ i, π i)ᵒᵈ ≃o ∀ i, (π i)ᵒᵈ` in `Order/Atoms.lean:1316`. It was private because
before the change it was needed only once. It is now the natural public companion of every
`(E := Eᵒᵈ)` transport over a function type; another entry for the design queue, beside §59 and §61.

### A named-argument trap, again

`IsLUB` is `IsLeast (upperBounds 𝓕) s`, i.e. an `And`. So `h.2 (b := Ψ g) …` does **not** name the
upper bound — it names `And.right`'s implicit `b`, and you get
`Application type mismatch … Ψ g has type X → E … but is expected to have type Prop`. Use
`h.2 (show Ψ g ∈ upperBounds 𝓖 from …)` instead. Same shape as `Iff.mp`'s parameters swallowing
`(f := …)` after a `.1` (§ earlier): after a structure projection, named arguments belong to the
projection, not to the thing you are projecting out of.

## 65. `𝓤 (αᵒᵈ)` has no bridge either, and Dini's theorem needs one

`Topology/UniformSpace/Dini.lean` proves the four `Antitone` forms of Dini's theorem by
`Monotone.… (G := Gᵒᵈ)`. Once `G → Gᵒᵈ` is a real map, both the family `F : ι → α → G` and the limit
`f` have to be pushed through `⇑toDual`, and the conclusion — a `TendstoUniformly*` statement, i.e.
a statement about the *uniformity* of `Gᵒᵈ` — has to be pulled back. The pull-back is exactly
`UniformContinuous.comp_tendsto{,Locally}Uniformly{,On}`, which all four exist; what does not exist
is the uniform continuity of `ofDual`:

```lean
private lemma uniformContinuous_ofDual {X : Type*} [UniformSpace X] :
    UniformContinuous (OrderDual.ofDual : Xᵒᵈ → X) :=
  uniformContinuous_comap
```

That this is `uniformContinuous_comap` on the nose is a small piece of luck worth recording:
`OrderDual.instUniformSpace` is `(UniformSpace.comap ofDual ‹_›).replaceTopology _`, and
`replaceTopology` rewrites only the topology field, so the *uniformity* is literally the comapped
one. (`uniformContinuous_toDual` is `uniformContinuous_comap' uniformContinuous_id` by the same
token.) The whole file is then four transports of the form

```lean
  uniformContinuous_ofDual.comp_tendstoLocallyUniformly <|
    Monotone.tendstoLocallyUniformly_of_forall_tendsto (G := Gᵒᵈ)
      (F := fun i ↦ ⇑OrderDual.toDual ∘ F i) (f := ⇑OrderDual.toDual ∘ f)
      (fun i ↦ continuous_toDual.comp (hF_cont i)) (fun _ _ hij x ↦ hF_anti hij x)
      (continuous_toDual.comp hf) (fun x ↦ (continuous_toDual.tendsto _).comp (h_tendsto x))
```

— note that `Monotone (fun i ↦ ⇑toDual ∘ F i)` from `Antitone F` is `fun _ _ hij x ↦ hF_anti hij x`,
pointwise and definitional; only the *packaging* changed.

The fifth site, `ContinuousMap.tendsto_of_antitone_of_pointwise`, was **not** transported: its data
is a bundled `F : ι → C(α, G)`, and pushing that through `toDual` means rebuilding every bundled
map. It mirrors its `Monotone` sibling in two lines instead — §48's rule, applied to a single
declaration rather than a whole file. The criterion that decides between transport and mirror is not
the length of the proof but whether the dualised data is *bundled*: an unbundled `α → G` composes
with `toDual` for free, a `C(α, G)` does not.

## 66. `EReal.negOrderIso` lands in `ERealᵒᵈ`, and that is now visible

```lean
def negOrderIso : EReal ≃o ERealᵒᵈ where toFun x := OrderDual.toDual (-x) …
```

so `OrderIso.limsup_apply negOrderIso : negOrderIso (limsup v f) = limsup (⇑negOrderIso ∘ v) f`
is an equation **in `ERealᵒᵈ`**, while `liminf_neg : liminf (-v) f = -limsup v f` is one in `EReal`.
Before, `.symm` sufficed. Now:

```lean
lemma liminf_neg : liminf (-v) f = -limsup v f :=
  congrArg OrderDual.ofDual EReal.negOrderIso.limsup_apply.symm
```

and this type-checks *only* because `limsup (⇑toDual ∘ u) F = toDual (liminf u F)` is still
definitional (see the rfl-bridge list). One `congrArg ofDual` is the whole cost of a codomain-dual
`OrderIso`: worth remembering as the first thing to try whenever an `≃o` into a dual is applied and
the result is one dualisation away from the goal.

## 67. `WithTop`'s order is *defined* through the dual, so `preimage_mono` picks a different `?f`

`Metric.thickening δ E` is `{x | infEDist x E < ENNReal.ofReal δ}` and the monotonicity lemma was

```lean
theorem thickening_mono (hle : δ₁ ≤ δ₂) (E : Set α) : thickening δ₁ E ⊆ thickening δ₂ E :=
  preimage_mono (Iio_subset_Iio (ENNReal.ofReal_le_ofReal hle))
```

which now fails with an expected type nobody wrote:

```
but is expected to have type
  WithBot.LT (WithTop.map OrderDual.toDual' (ENNReal.ofReal δ₁)) ⊆ …
```

The cause is not in `Metric` at all. `WithTop.instLT` is *defined* by dualising:

```lean
instance (priority := 10) WithTop.instLT : LT (WithTop α) where
  lt a b := WithBot.LT (α := αᵒᵈ) (b.map OrderDual.toDual') (a.map OrderDual.toDual')
```

so `infEDist x E < ofReal δ₁` whnf's to `WithBot.LT (map toDual' (ofReal δ₁)) (map toDual' (infEDist x E))`.
`preimage_mono` has to solve `?f ⁻¹' ?s =?= {x | …}` — higher-order — and while `WithTop.map toDual'`
was the identity the unifier chose `?f := (infEDist · E)`; now it absorbs the `map` into `?f` and
`?s` comes out as a partially applied `WithBot.LT`, which no `Iio` lemma matches. This is the
`OrderDual`-as-structure change surfacing *through a third type*: nothing in `Thickening.lean`
mentions a dual.

The repair is to stop asking for the preimage decomposition at all — the pointwise proof is shorter
and first-order:

```lean
    thickening δ₁ E ⊆ thickening δ₂ E := fun _ hx ↦ hx.trans_le (ENNReal.ofReal_le_ofReal hle)
    cthickening δ₁ E ⊆ cthickening δ₂ E := fun _ hx ↦ hx.trans (ENNReal.ofReal_le_ofReal hle)
```

Worth generalising: wherever a proof used `preimage_mono`/`image_subset` on a set given in
set-builder form, the unifier was doing a higher-order guess that happened to be right. Any change
to the *instance* used inside the predicate can flip that guess.

## 68. Reindexing `⋃`/`⨆` along `ofDual`, and why `simp` fires for one and not the other

`MeasureTheory/Measure/Continuity.lean` derives every `Antitone` continuity statement from the
`Monotone` one by `hs.dual_left.measure_iUnion`, which now returns a statement indexed by `ιᵒᵈ`:

```
μ (⋃ i : ιᵒᵈ, (s ∘ ofDual) i) = ⨆ i : ιᵒᵈ, μ ((s ∘ ofDual) i)
```

Reindexing is `Function.Surjective.iSup_comp` (and `iInf_comp`) applied to `OrderDual.ofDual`:

```lean
private lemma iSup_ofDual {M : Type*} [CompleteLattice M] (g : ι → M) :
    ⨆ i : ιᵒᵈ, g (OrderDual.ofDual i) = ⨆ i, g i :=
  OrderDual.ofDual.surjective.iSup_comp g
```

with `⋃`/`⋂` versions proved by `ext` + `Surjective.exists`/`.forall` (note: these need the
predicate pinned — `(p := fun i ↦ x ∈ t i)` — or the metavariable is never solved).

The instructive part is the asymmetry in `simp only [iUnion_ofDual, iSup_ofDual]`: the first fires,
the second silently does not. Both lemmas have LHS `F fun i ↦ ?g (ofDual i)`, which is not a Miller
pattern, so simp falls back to first-order matching:

* `?t (ofDual i) =?= s (ofDual i)` — first-order: heads line up, `?t := s`. **Fires.**
* `?g (ofDual i) =?= μ (s (ofDual i))` — the head is `μ` and the argument is `s (ofDual i)`, not
  `ofDual i`. No first-order solution. **Silently skipped.**

So the value-level reindexing has to be a `rw` with the function given explicitly,
`rwa [iSup_ofDual fun i ↦ μ (s i)] at h`, while the set-level one can stay in the simp set. A
`simpa … using` that leaves a goal "identical except for the index type" is this, every time.

## 69. Mirror when the dualised type sits in a *dependent* position

Two sites in wave 35 were mirrored rather than transported, on a sharper criterion than §48's:

* `aeSeq.iInf` was `iSup (β := βᵒᵈ) hf hp`. But `aeSeq hf p` takes the *proof*
  `hf : ∀ i, AEMeasurable (f i) μ` as an argument, so dualising `β` changes the type of `hf`, and
  the term `aeSeq hf p` in the goal is not the term the dual lemma produces. Mirroring is three
  lines (`filter_upwards …; simp [iInf_apply, hx]`).
* `tendsto_measure_iUnion_atBot` / `tendsto_measure_iInter_atBot` were
  `tendsto_measure_iUnion_atTop (ι := ιᵒᵈ) hm.dual_left`. Transporting needs the `atTop (ιᵒᵈ)`
  bridge of §61 *and* the index reindexing of §68 — two missing dictionary entries stacked. Their
  `Monotone` siblings are four lines whose every ingredient (`atBot_neBot_iff`,
  `tendsto_atBot_iSup`, `tendsto_atBot_iInf`) already exists by `@[to_dual]`. Mirrored.

Rule of thumb after three waves of this: transport when the dualised type appears only as the
*codomain of an unbundled function*; mirror when it appears inside a bundled structure (§65), in a
dependent argument, or behind a filter whose dual bridge does not exist (§61).
