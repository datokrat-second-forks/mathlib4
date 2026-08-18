# Migrating off `backward.isDefEq.respectTransparency` — handoff notes

## Intent

This branch tests a Lean fork (`../lean4-defeq`) in which `isDefEq` respects transparency:
implicit and instance-implicit arguments are compared at `.implicit` instead of being bumped to
`.default`, and metavariable assignments type-check at restricted transparency. Many Mathlib
declarations currently carry backward-compatibility options; the goal of these investigations is
to understand *why* each one is needed and to eliminate it — ideally replacing it with
`@[implicit_reducible]` annotations or small proof changes, so the new defaults can eventually
ship.

**Scope.** Only declarations carrying

```lean
set_option backward.isDefEq.respectTransparency.instances false in
```

are relevant targets. For those, the interesting task is to remove
`backward.isDefEq.respectTransparency false` **first**: `instances false` is almost always a
*symptom* of it, because

- `isInstanceMVar` (ExprDefEq.lean) reads only the `.instances` flag — it ignores the parent
  option and `.types`, contrary to its docstring — so the new instance-assignment machinery
  (exact-`.instances` type check + synth-and-unify fallback) runs even in old mode; and
- the first-pass implicit bump in `isDefEqArgsFirstPass` is gated on `respectTransparency = true`,
  so under old mode instance-mvar assignments (and the fallback's final `v =?= inst` unification)
  run at the caller's raw transparency — `.reducible` for `simp`/`rw` matching, where nothing
  unfolds. `instances false` papers over exactly this hybrid.

Once `respectTransparency false` is gone, `instances false` has so far always been removable too.
`backward.defeqAttrib.useBackward` is out of scope; assume it stays. A residual
`backward.isDefEq.respectTransparency.types false` (which sends *non-instance* mvar-type checks to
`.default` while keeping everything else new-regime) is an acceptable fallback when full defaults
are out of reach.

## Background: the transparency ladder

`reducible < instances < implicit < default`. `.instances` unfolds `[reducible]` +
`[instance_reducible]` (instances); `.implicit` additionally unfolds `[implicit_reducible]`.
Key consequences:

- `@[implicit_reducible]` marks help wherever a check runs at `.implicit` — argument comparisons
  under the new defaults, mvar-type checks (`.types` on), the synth-fallback's final unification
  when the bump is active. They do **not** help the direct instance-assignment type check, which
  is pinned to exactly `.instances` (`withExactInstancesConfig`).
- `@[instance_reducible]` on type synonyms or category wrappers is usually wrong: TC search then
  sees through them and resolves the underlying type's instances (verified failure:
  `instance_reducible Free` breaks `Preadditive (Free R C)` synthesis).

## Suggested workflow

1. Strip the `isDefEq` options from the declaration and compile the file
   (`lake env lean <file>`). Keep `defeqAttrib`.
2. Read the error. The note *"the target expression is not type-correct under the `implicit`
   transparency level"* names the game: some earlier step glued two spellings that only agree at
   `.default`. `set_option linter.tacticCheckInstances true` reports which constants block.
3. Useful traces, attached via `set_option ... in` to the failing tactic:
   - `trace.Meta.isDefEq.assign.checkTypes` — every mvar assignment with ✅/❌; nested lines under
     an ❌ instance assignment are the synth-fallback at work.
   - `trace.Meta.synthPending` — whether the fallback's synthesis ran.
   - `trace.Meta.isDefEq` + `trace.Meta.isDefEq.printTransparency` — the full tree with
     transparency tags; find the ❌ leaf and note at which transparency it failed.
   - `trace.Meta.Tactic.simp.rewrite` — diff the fired-lemma list between the working (options-on)
     and failing runs; the first missing lemma is the thread to pull.
4. Classify against the catalog below and try the corresponding fix. Verify by recompiling; also
   check which `implicit_reducible` marks are actually needed (the attribute command errors
   helpfully if a constant is already `[reducible]`/`[implicit_reducible]`).
5. Leave a short comment above the declaration recording the mechanism, and — where relevant —
   that `instances false` had only been needed because `respectTransparency false` suppresses the
   first-pass implicit bump.

**Gotcha:** `attribute [local ...] ... in` scopes over the *next command only*. An interleaved
standalone `set_option` (no `in`) silently swallows it (this was the actual bug in
`Grp/Colimits.lean`).

## Failure catalog (all instances observed so far)

1. **Wrapper-definition spelling mismatch.** The goal mixes a carrier spelled through a
   semireducible wrapper (`(F ⋙ uliftFunctor).obj j`, `↑(coproductCocone A B).pt`,
   `(monoidAlgebra R).obj G`, `↑(directLimitDiagram G f).obj i`) with its unfolded form, and some
   instance or implicit argument fails to compare below `.default`. *Fix:* `implicit_reducible`
   on the wrapper (`uliftFunctor`, `free`, `Free`, `embedding`, `monoidAlgebra`, `Under.forget`,
   `directLimitCocone`, `directLimitDiagram`, `Limits.BinaryCofan.mk`, …). Several plumbing defs
   are already marked upstream (`Functor.comp`, `forget₂`, `Under.mk`, `LinearEquiv.symm`,
   `Int.cast`) — the ecosystem is converging on this policy; missing marks are often just gaps.
   Examples: `Grp/Colimits.lean`, `MonCat/Adjunctions.lean`, `Ring/Adjunctions.lean`,
   `ModuleCat/Limits.lean`.

2. **Elaboration relying on instance-mvar assignment to solve term mvars.** A `change`/pattern
   with `_` postpones a TC problem (`HSMul R (X ⟶ ?m) ?γ`); under the old `.default` type check
   the instance assignment solved `?m` as a side effect; the exact-`.instances` check cannot, and
   the synth fallback refuses mvar-containing types → "typeclass instance problem is stuck".
   *Fix:* spell out the `_` so the instance's type is determined before assignment
   (`ModuleCat/Adjunctions.lean`).

3. **Default-only instance diamonds.** The proof equates two instance *paths* whose agreement is
   numeric-plumbing-deep, e.g. `Ring.toIntAlgebra (A ⊗[ℤ] B) ≟ Algebra.TensorProduct.leftAlgebra`
   (their `algebraMap`s differ by `Int.cast`/`zsmul` internals; marking the surface defs just
   moves the wall into coercion projections and `Int` matchers — verified whack-a-mole). The
   diamond can bite three ways: in a non-instance mvar's type check (fixable by `types false`),
   in an instance-mvar assignment (fixable by bump + marks), and inside a simp lemma's *pattern*
   (a rigid instance argument — no option short of `respectTransparency false` helps).
   *Fix:* restructure the proof so the two spellings are never equated — e.g.
   `Ring/Constructions.lean`'s `coproductCoconeIsColimit.uniq` was rewritten from
   `toIntAlgHom`/`liftEquiv`-injectivity to plain `RingHom` reasoning via
   `TensorProduct.induction_on`, after which *all* options (even `types false`) came off.

4. **Proof fields of delta-unfolded structure literals** *(mechanism behind the
   `DirectSum/Module.lean` fixes)*. A proof does `simp only [..., toModule, DFinsupp.lsum, ...]`,
   delta-unfolding a definition into a structure literal. Simp then rewrites the literal's *data*
   fields (e.g. `⇑liftAddHom … ⇝ ⇑sumAddHom …`), but the *proof* fields are auto-generated
   `_proof_N` constants whose **types** still mention the original spelling
   (`DFinsupp.lsum._proof_6 : ∀ …, liftAddHom … = …` sitting in a literal whose `toFun` says
   `sumAddHom`). The literal is then only default-transparency type-correct, and every later
   match or mvar assignment against it fails at `.implicit` — e.g. the traced blocker
   `?left_inv := DFinsupp.mapRange.linearEquiv._proof_5 …`, typed over
   `(DFinsupp.mapRange.addEquiv …).invFun`. Note this presents as a `.types`-check failure even
   when the declaration carried `instances false`. *Fix:* mark `implicit_reducible` exactly the
   definitions appearing in the `_proof_N` types (`DFinsupp.liftAddHom`,
   `DFinsupp.mapRange.addEquiv`, plus whatever coercion wrapper the field comparison needs,
   e.g. `AddEquiv.symm`). This is pleasantly mechanical: the failing checkTypes trace names them.
   Here too, `instances false` was only needed because `respectTransparency false` suppresses the
   first-pass implicit bump.

5. **API-level dual spellings.** The statement itself identifies an `→+`-flavored and a
   `→ₗ`-flavored spelling (`IsInternal A := Bijective (coeAddMonoidHom A)` used as
   `Bijective ⇑(coeLinearMap A)`), and the unfold chain runs through deep `DFinsupp` internals.
   Marks kept receding; *fix:* settle for `types false`
   (`DirectSum/Module.lean`, `ofBijective_coeLinearMap_*`).

## Observations for the Lean branch (`lean4-defeq`)

- `isInstanceMVar` gating: honors only `.instances`, not the parent option or `.types` — either
  the code or the docstring should change; as is, `respectTransparency false` is not a faithful
  escape hatch (it produces the hybrid described under *Scope*).
- Old mode lacks the first-pass bump entirely (new-mode bump is gated on
  `respectTransparency`), so easy-case instance assignments run at raw `.reducible` there.
- `synthInstanceTypedMVarAndUnify`'s final `v =?= inst` inherits the ambient transparency of the
  assignment site; consider pinning it (e.g. `withImplicitConfig`) so it cannot silently degrade.
- The type comparison in `checkTypesForInstanceTypedMVarAssignment` runs at exactly `.instances`,
  below where `implicit_reducible` lives; the commented-out `withCorrectTransparency` block in
  `checkTypesAndAssign` sketches the alternative. Several of the cases above are good test cases.
- Error recovery after a failed `apply`/autoparam can leak metavariables into the declaration
  (kernel errors `declaration has metavariables`, `unknown metavariable`) and make `@[simps]`
  generate degenerate lemmas (`… : desc s = desc s`). Seen in `ModuleCat/Limits.lean` and
  `Ring/Constructions.lean` before the fixes.
