/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Equivalence between subobjects and quotients in an abelian category

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

noncomputable section

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C]

/-!
`subobjectIsoSubobjectOp` needs `backward.isDefEq.instanceTypes false`.
* What fails (traced copy below): in the second branch, `Subobject.mk_eq_mk_of_comm` requires
  `Mono (kernel.ι (cokernel.π f))`; the synthesis applies the candidate `equalizer.ι_mono`, whose
  conclusion `Mono (equalizer.ι ?f ?g)` is unified with the goal. This unfolds the goal's
  `kernel.ι` to `equalizer.ι (cokernel.π f) 0`, exposing the `HasKernel` instance buried in the
  goal term: `kernelOrderHom._proof_1 X (op (cokernel f)) (cokernel.π f).op`, of type
  `HasKernel (cokernel.π f).op.unop`.
* After the candidate's `?f := cokernel.π f`, `?g := 0` are pinned, that buried value is assigned
  to the candidate's instance-typed mvar:
  `(?inst : HasEqualizer (cokernel.π f) 0) := (kernelOrderHom._proof_1 X (op (cokernel f))
  (cokernel.π f).op : HasKernel (cokernel.π f).op.unop)`. The assignment is rejected: the types
  differ by the `.op.unop` round-trip on the morphism index, which does not unfold at
  `.instances` (nor at `.implicit`) — the trace descends through
  `HasLimit (parallelPair …)` and stalls at `@colimit.ι =?= @Quiver.Hom.unop`.
* Known pattern (cf. `Mathlib/CategoryTheory/Filtered/CostructuredArrow.lean`): the desync
  pre-exists in the goal — the preceding `dsimp only [..., Quiver.Hom.unop_op]` normalized the
  *visible* morphism to `kernel.ι (cokernel.π f)` but left the instance buried in the term at
  its un-normalized `.op.unop` type; the unifier merely inherits the mismatch.

The correctly-typed instance is synthesizable, but the rejected instance is defeq to it at
`.implicit` only with `Quiver.Hom.op`/`Quiver.Hom.unop` made implicit-reducible (example below);
without that lever, both the types and the instances agree only at `.default`. `HasKernel` and
`Mono` are Prop-valued, so accepting the assignment would be kernel-sound by proof irrelevance;
but a Prop-exemption that re-checks the types at `.implicit` would NOT rescue this site.

Possible solutions:
* Make `Quiver.Hom.op`/`Quiver.Hom.unop` instance-reducible, so the round-trip unfolds at
  `.instances` transparency.
* Don't do the type check for propositional type classes (proof irrelevance).
* If an assignment fails, try to synthesize at the mvar's own type.
-/

-- The rejected and the synthesized instances are defeq at `.implicit` with the `op`/`unop` lever
-- (without it, even this fails).
set_option linter.auxLemma false in
attribute [local implicit_reducible] Quiver.Hom.op Quiver.Hom.unop in
example [Abelian C] {A X : C} (f : A ⟶ X) :
    (kernelOrderHom._proof_1 X (op (cokernel f)) (cokernel.π f).op)
      = (inferInstance : HasKernel (cokernel.π f)) := by
  with_implicit apply_rfl

/-
The fix: with the first-pass `.implicit` bump (`backward.isDefEq.firstPassBump`, default on) and
`Quiver.Hom.op`/`unop` implicit-reducible, the `markOrSynth` fallback goes through. The direct
`.instances` gate still rejects the buried `HasKernel (cokernel.π f).op.unop` candidate (by
design — instance search must not see through implicit-reducible constants), but after
synthesizing `HasEqualizer (cokernel.π f) 0` the candidate is accepted by proof irrelevance at
the bumped `.implicit` transparency, where the `.op.unop` round-trip now unfolds. No
`backward.isDefEq.instanceTypes "none"` needed.
-/
attribute [local implicit_reducible] Quiver.Hom.op Quiver.Hom.unop in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.instanceTypes "markOrSynth" in
set_option backward.defeqAttrib.useBackward true in
/-- In an abelian category, the subobjects and quotient objects of an object `X` are
order-isomorphic via taking kernels and cokernels.
Implemented here using subobjects in the opposite category,
since mathlib does not have a notion of quotient objects at the time of writing. -/
@[simps!]
def subobjectIsoSubobjectOp [Abelian C] (X : C) : Subobject X ≃o (Subobject (op X))ᵒᵈ := by
  refine OrderIso.ofHomInv (cokernelOrderHom X) (kernelOrderHom X) ?_ ?_
  · change (cokernelOrderHom X).comp (kernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, kernelOrderHom_coe, Subobject.lift_mk,
      cokernelOrderHom_coe, OrderHom.id_coe, id]
    refine Subobject.mk_eq_mk_of_comm _ _
        ⟨?_, ?_, Quiver.Hom.unop_inj ?_, Quiver.Hom.unop_inj ?_⟩ ?_
    · exact (Abelian.epiDesc f.unop _ (cokernel.condition (kernel.ι f.unop))).op
    · exact (cokernel.desc _ _ (kernel.condition f.unop)).op
    · rw [← cancel_epi (cokernel.π (kernel.ι f.unop))]
      simp only [unop_comp, Quiver.Hom.unop_op, unop_id_op, cokernel.π_desc_assoc,
        comp_epiDesc, Category.comp_id]
    · simp only [← cancel_epi f.unop, unop_comp, Quiver.Hom.unop_op, unop_id, comp_epiDesc_assoc,
        cokernel.π_desc, Category.comp_id]
    · exact Quiver.Hom.unop_inj (by simp only [unop_comp, Quiver.Hom.unop_op, comp_epiDesc])
  · change (kernelOrderHom X).comp (cokernelOrderHom X) = _
    refine OrderHom.ext _ _ (funext (Subobject.ind _ ?_))
    intro A f hf
    dsimp only [OrderHom.comp_coe, Function.comp_apply, cokernelOrderHom_coe, Subobject.lift_mk,
      kernelOrderHom_coe, OrderHom.id_coe, id, unop_op, Quiver.Hom.unop_op]
    refine Subobject.mk_eq_mk_of_comm _ _ ⟨?_, ?_, ?_, ?_⟩ ?_
    · exact Abelian.monoLift f _ (kernel.condition (cokernel.π f))
    · exact kernel.lift _ _ (cokernel.condition f)
    · simp only [← cancel_mono (kernel.ι (cokernel.π f)), Category.assoc, image.fac, monoLift_comp,
        Category.id_comp]
    · simp only [← cancel_mono f, Category.assoc, monoLift_comp, image.fac, Category.id_comp]
    · simp only [monoLift_comp]

/-- A well-powered abelian category is also well-copowered. -/
instance wellPowered_opposite [Abelian C] [LocallySmall.{w} C] [WellPowered.{w} C] :
    WellPowered.{w} Cᵒᵖ where
  subobject_small X :=
    (small_congr (subobjectIsoSubobjectOp (unop X)).toEquiv).1 inferInstance

end CategoryTheory.Abelian
