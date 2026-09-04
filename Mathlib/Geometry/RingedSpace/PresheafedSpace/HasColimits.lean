/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `TopCat` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheafed spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/

@[expose] public section


noncomputable section

universe v' u' v u

open CategoryTheory Opposite CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  TopCat TopCat.Presheaf TopologicalSpace

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

attribute [local simp] eqToHom_map

-- We could enable the following attribute:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens
-- although it doesn't appear to help in this file, in any case.

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem map_id_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) (j) (U) :
    (F.map (𝟙 j)).c.app U =
      (Pushforward.id (F.obj j).presheaf).inv.app U ≫
        (pushforwardEq (by simp) (F.obj j).presheaf).hom.app U := by
  simp [PresheafedSpace.congr_app (F.map_id j)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
theorem map_comp_c_app (F : J ⥤ PresheafedSpace.{_, _, v} C) {j₁ j₂ j₃}
    (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) :
    (F.map (f ≫ g)).c.app U =
      (F.map g).c.app U ≫
        ((pushforward C (F.map g).base).map (F.map f).c).app U ≫
          (pushforwardEq (congr_arg Hom.base (F.map_comp f g).symm) _).hom.app U := by
  simp [PresheafedSpace.congr_app (F.map_comp f g)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram of `PresheafedSpace C`s, its colimit is computed by pushing the sheaves onto
the colimit of the underlying spaces, and taking componentwise limit.
This is the componentwise diagram for an open set `U` of the colimit of the underlying spaces.
-/
@[simps]
def componentwiseDiagram (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) : Jᵒᵖ ⥤ C where
  obj j := (F.obj (unop j)).presheaf.obj (op ((Opens.map (colimit.ι F (unop j)).base).obj U))
  map {j k} f := (F.map f.unop).c.app _ ≫
    (F.obj (unop k)).presheaf.map (eqToHom (by rw [← colimit.w F f.unop, comp_base]; rfl))
  map_comp {i j k} f g := by
    simp only [assoc, CategoryTheory.NatTrans.naturality_assoc]
    simp

theorem pushforwardDiagramToColimit_obj_eq
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C)) (j : J) :
    (F ⋙ PresheafedSpace.forget C).obj j = (F.obj j).carrier :=
  (Functor.comp_obj F (PresheafedSpace.forget C) j).trans
    (PresheafedSpace.forget_obj C (F.obj j))

variable [HasColimitsOfShape J TopCat.{v}]

def pushforwardDiagramToColimitι
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C)) (j : J) :
    (F.obj j).carrier ⟶ colimit (F ⋙ PresheafedSpace.forget C) :=
  eqToHom (pushforwardDiagramToColimit_obj_eq F j).symm ≫
    colimit.ι (F ⋙ PresheafedSpace.forget C) j

theorem pushforwardDiagramToColimit_eqToHom_comp_ι
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C)) (j : J) :
    eqToHom (pushforwardDiagramToColimit_obj_eq F j) ≫
        pushforwardDiagramToColimitι F j =
      colimit.ι (F ⋙ PresheafedSpace.forget C) j := by
  unfold pushforwardDiagramToColimitι
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

omit [HasColimitsOfShape J TopCat] in
theorem pushforwardDiagramToColimit_map_coherence_inv
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C))
    {j j' : J} (f : j ⟶ j') :
    (F.map f).base ≫ eqToHom (pushforwardDiagramToColimit_obj_eq F j').symm =
      eqToHom (pushforwardDiagramToColimit_obj_eq F j).symm ≫
        (F ⋙ PresheafedSpace.forget C).map f := by
  rw [comp_eqToHom_iff, Category.assoc]
  apply (conj_eqToHom_iff_heq (F.map f).base
    ((F ⋙ PresheafedSpace.forget C).map f)
    (pushforwardDiagramToColimit_obj_eq F j).symm
    (pushforwardDiagramToColimit_obj_eq F j').symm).mpr
  rw [Functor.comp_map, PresheafedSpace.forget_map]
  rfl

omit [HasColimitsOfShape J TopCat] in
theorem pushforwardDiagramToColimit_map_coherence
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C))
    {j j' : J} (f : j ⟶ j') :
    (F ⋙ PresheafedSpace.forget C).map f ≫
        eqToHom (pushforwardDiagramToColimit_obj_eq F j') =
      eqToHom (pushforwardDiagramToColimit_obj_eq F j) ≫
        (F.map f).base := by
  rw [comp_eqToHom_iff, Category.assoc]
  apply (conj_eqToHom_iff_heq ((F ⋙ PresheafedSpace.forget C).map f)
    (F.map f).base
    (pushforwardDiagramToColimit_obj_eq F j)
    (pushforwardDiagramToColimit_obj_eq F j')).mpr
  rw [Functor.comp_map, PresheafedSpace.forget_map]
  rfl

theorem pushforwardDiagramToColimitι_naturality
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C))
    {j j' : J} (f : j ⟶ j') :
    (F.map f).base ≫ pushforwardDiagramToColimitι F j' =
      pushforwardDiagramToColimitι F j := by
  unfold pushforwardDiagramToColimitι
  rw [← colimit.w (F ⋙ PresheafedSpace.forget C) f]
  rw [← Category.assoc, pushforwardDiagramToColimit_map_coherence_inv, Category.assoc]

theorem pushforwardDiagramToColimitι_hom_ext
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C)) {X : TopCat}
    {f g : colimit (F ⋙ PresheafedSpace.forget C) ⟶ X}
    (h : ∀ j, pushforwardDiagramToColimitι F j ≫ f =
      pushforwardDiagramToColimitι F j ≫ g) : f = g := by
  apply colimit.hom_ext
  intro j
  have h' := congr_arg
    (fun k => eqToHom (pushforwardDiagramToColimit_obj_eq F j) ≫ k) (h j)
  simpa only [pushforwardDiagramToColimitι, ← Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp] using h'

def pushforwardDiagramToColimitDesc
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C)) (s : Cocone F) :
    colimit (F ⋙ PresheafedSpace.forget C) ⟶ s.pt.carrier :=
  colimit.desc (F ⋙ PresheafedSpace.forget C)
    { pt := s.pt.carrier
      ι :=
        { app := fun j => eqToHom (pushforwardDiagramToColimit_obj_eq F j) ≫
            (s.ι.app j).base
          naturality := fun {j j'} f => by
            dsimp
            simp only [Category.comp_id]
            rw [← Category.assoc, pushforwardDiagramToColimit_map_coherence, Category.assoc]
            exact congr_arg Hom.base (s.w f) } }

theorem pushforwardDiagramToColimitι_desc
    (F : CategoryTheory.Functor J (PresheafedSpace.{_, _, v} C))
    (s : Cocone F) (j : J) :
    pushforwardDiagramToColimitι F j ≫
        pushforwardDiagramToColimitDesc F s =
      (s.ι.app j).base := by
  unfold pushforwardDiagramToColimitι pushforwardDiagramToColimitDesc
  rw [Category.assoc, colimit.ι_desc]
  dsimp
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(Presheaf C X)ᵒᵖ`.
-/
@[simps]
def pushforwardDiagramToColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    J ⥤ (Presheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ where
  obj j := op (pushforwardDiagramToColimitι F j _* (F.obj j).presheaf)
  map {j j'} f :=
    ((pushforward C (pushforwardDiagramToColimitι F j')).map (F.map f).c ≫
      (Pushforward.comp (F.map f).base (pushforwardDiagramToColimitι F j')
        (F.obj j).presheaf).inv ≫
      (pushforwardEq (pushforwardDiagramToColimitι_naturality F f)
        (F.obj j).presheaf).hom).op
  map_id j := by
    apply (opEquiv _ _).injective
    refine NatTrans.ext (funext fun U => ?_)
    induction U with
    | op U =>
      simp [opEquiv]
      rfl
  map_comp {j₁ j₂ j₃} f g := by
    apply (opEquiv _ _).injective
    refine NatTrans.ext (funext fun U => ?_)
    dsimp [opEquiv]
    have :
      op ((Opens.map (F.map g).base).obj
          ((Opens.map (pushforwardDiagramToColimitι F j₃)).obj U.unop)) =
        op ((Opens.map (pushforwardDiagramToColimitι F j₂)).obj (unop U)) := by
      apply unop_injective
      rw [← Opens.map_comp_obj]
      exact Functor.congr_obj
        (congr_arg Opens.map (pushforwardDiagramToColimitι_naturality F g)) U.unop
    simp only [map_comp_c_app, pushforward_obj_obj, pushforward_map_app, comp_base,
      pushforwardEq_hom_app, op_obj, Opens.map_comp_obj, id_comp, assoc, eqToHom_map_comp,
      NatTrans.naturality_assoc, pushforward_obj_map, eqToHom_unop]
    simp [NatTrans.congr (α := (F.map f).c) this]

variable [∀ X : TopCat.{v}, HasLimitsOfShape Jᵒᵖ (X.Presheaf C)]

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
def colimit (F : J ⥤ PresheafedSpace.{_, _, v} C) : PresheafedSpace C where
  carrier := Limits.colimit (F ⋙ PresheafedSpace.forget C)
  presheaf := limit (pushforwardDiagramToColimit F).leftOp

@[simp]
theorem colimit_carrier (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).carrier = Limits.colimit (F ⋙ PresheafedSpace.forget C) :=
  rfl

@[simp]
theorem colimit_presheaf (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    (colimit F).presheaf = limit (pushforwardDiagramToColimit F).leftOp :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
@[simps]
def colimitCocone (F : J ⥤ PresheafedSpace.{_, _, v} C) : Cocone F where
  pt := colimit F
  ι :=
    { app := fun j =>
        { base := pushforwardDiagramToColimitι F j
          c := limit.π _ (op j) }
      naturality := fun {j j'} f => by
        ext1
        · exact pushforwardDiagramToColimitι_naturality F f
        · ext ⟨⟩
          simp [Functor.comp_obj, ← congr_arg NatTrans.app
            (limit.w (pushforwardDiagramToColimit F).leftOp f.op)] }

variable [HasLimitsOfShape Jᵒᵖ C]

namespace ColimitCoconeIsColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit`.
-/
def descCApp (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (U : (Opens s.pt.carrier)ᵒᵖ) :
    s.pt.presheaf.obj U ⟶
      (pushforwardDiagramToColimitDesc F s _*
            limit (pushforwardDiagramToColimit F).leftOp).obj
        U := by
  refine
    limit.lift _
        { pt := s.pt.presheaf.obj U
          π :=
            { app := fun j => ?_
              naturality := fun j j' f => ?_ } } ≫
      (limitObjIsoLimitCompEvaluation _ _).inv
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  · refine (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).presheaf.map (eqToHom ?_)
    dsimp
    rw [← Opens.map_comp_obj]
    rw [pushforwardDiagramToColimitι_desc]
  · dsimp
    simp only [Functor.leftOp_obj, pushforwardDiagramToColimit_obj, Opposite.unop_op,
      Functor.comp_map, evaluation_obj_map, Functor.leftOp_map,
      pushforwardDiagramToColimit_map, Quiver.Hom.unop_op]
    dsimp
    rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
    have w :=
      Functor.congr_obj
        (congr_arg Opens.map
          (pushforwardDiagramToColimitι_desc F s (unop j)))
        (unop U)
    simp only [Opens.map_comp_obj_unop] at w
    replace w := congr_arg op w
    have w' := NatTrans.congr (F.map f.unop).c w
    rw [w']
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem desc_c_naturality (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F)
    {U V : (Opens s.pt.carrier)ᵒᵖ} (i : U ⟶ V) :
    s.pt.presheaf.map i ≫ descCApp F s V =
      descCApp F s U ≫
        (pushforwardDiagramToColimitDesc F s _* (colimitCocone F).pt.presheaf).map
          i := by
  dsimp [descCApp]
  refine limit_obj_ext (fun j => ?_)
  have w := Functor.congr_hom (congr_arg Opens.map
    (pushforwardDiagramToColimitι_desc F s (unop j))) i.unop
  simp only [Opens.map_comp_map] at w
  simp [congr_arg Quiver.Hom.op w]

/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.colimitCoconeIsColimit`.
-/
def desc (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) : colimit F ⟶ s.pt where
  base := pushforwardDiagramToColimitDesc F s
  c :=
    { app := fun U => descCApp F s U
      naturality := fun _ _ i => desc_c_naturality F s i }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem desc_fac (F : J ⥤ PresheafedSpace.{_, _, v} C) (s : Cocone F) (j : J) :
    (colimitCocone F).ι.app j ≫ desc F s = s.ι.app j := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the original proof is just
  -- `ext <;> dsimp [desc, descCApp] <;> simpa`,
  -- but this has to be expanded a bit
  ext U
  · exact ConcreteCategory.congr_hom (pushforwardDiagramToColimitι_desc F s j) U
  · simp only [op_obj, desc, descCApp, Presheaf.comp_app, comp_c_app, colimitCocone_ι_app_c, assoc]
    rw [limitObjIsoLimitCompEvaluation_inv_π_app_assoc]
    simp

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `AlgebraicGeometry.PresheafedSpace.instHasColimits`.
-/
def colimitCoconeIsColimit (F : J ⥤ PresheafedSpace.{_, _, v} C) :
    IsColimit (colimitCocone F) where
  desc s := desc F s
  fac s := desc_fac F s
  uniq s m w := by
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t :
      m.base = pushforwardDiagramToColimitDesc F s := by
      apply pushforwardDiagramToColimitι_hom_ext F
      intro j
      rw [pushforwardDiagramToColimitι_desc]
      have hw := congr_arg Hom.base (w j)
      simpa only [comp_base, colimitCocone_ι_app_base] using hw
    ext : 1
    · exact t
    · refine NatTrans.ext (funext fun U => limit_obj_ext fun j => ?_)
      simp [desc, descCApp,
        PresheafedSpace.congr_app (w (unop j)).symm U,
        NatTrans.congr (limit.π (pushforwardDiagramToColimit F).leftOp j)
        (congr_arg op (Functor.congr_obj (congr_arg Opens.map t) (unop U)))]

instance : HasColimitsOfShape J (PresheafedSpace.{_, _, v} C) where
  has_colimit F := ⟨colimitCocone F, colimitCoconeIsColimit F⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : PreservesColimitsOfShape J (PresheafedSpace.forget.{v, u, v} C) :=
  ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F) <| by
    apply IsColimit.ofIsoColimit (colimit.isColimit _)
    fapply Cocone.ext
    · rfl
    · intro j
      simp only [Functor.mapCocone_ι_app, PresheafedSpace.forget_map]
      change colimit.ι (F ⋙ PresheafedSpace.forget C) j =
        eqToHom (pushforwardDiagramToColimit_obj_eq F j) ≫
          pushforwardDiagramToColimitι F j
      exact (pushforwardDiagramToColimit_eqToHom_comp_ι F j).symm⟩

/-- When `C` has limits, the category of presheafed spaces with values in `C` itself has colimits.
-/
instance instHasColimits [HasLimits C] : HasColimits (PresheafedSpace.{_, _, v} C) :=
  ⟨fun {_ _} => ⟨fun {F} => ⟨colimitCocone F, colimitCoconeIsColimit F⟩⟩⟩

/-- The underlying topological space of a colimit of presheafed spaces is
the colimit of the underlying topological spaces.
-/
instance forget_preservesColimits [HasLimits C] :
    PreservesColimits (PresheafedSpace.forget.{_, _, v} C) where
  preservesColimitsOfShape {J 𝒥} :=
    { preservesColimit := fun {F} => preservesColimit_of_preserves_colimit_cocone
          (colimitCoconeIsColimit F)
          (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _))) }

set_option backward.isDefEq.respectTransparency false in
/-- The components of the colimit of a diagram of `PresheafedSpace C` is obtained
via taking componentwise limits.
-/
def colimitPresheafObjIsoComponentwiseLimit (F : J ⥤ PresheafedSpace.{_, _, v} C) [HasColimit F]
    (U : Opens (Limits.colimit F).carrier) :
    (Limits.colimit F).presheaf.obj (op U) ≅ limit (componentwiseDiagram F U) := by
  refine
    ((sheafIsoOfIso (colimit.isoColimitCocone ⟨_, colimitCoconeIsColimit F⟩).symm).app
          (op U)).trans
      ?_
  refine (limitObjIsoLimitCompEvaluation _ _).trans (Limits.lim.mapIso ?_)
  fapply NatIso.ofComponents
  · intro X
    refine (F.obj (unop X)).presheaf.mapIso (eqToIso ?_)
    simp only [Functor.op_obj, op_inj_iff, Opens.map_coe, SetLike.ext'_iff,
      Set.preimage_preimage]
    refine congr_arg (Set.preimage · U.1) (funext fun x => ?_)
    simp only [colimitCocone, colimit, ← TopCat.comp_app]
    congr
    exact ι_preservesColimitIso_inv (forget C) F (unop X)
  · intro X Y f
    change ((F.map f.unop).c.app _ ≫ _ ≫ _) ≫ (F.obj (unop Y)).presheaf.map _ = _ ≫ _
    rw [TopCat.Presheaf.Pushforward.comp_inv_app]
    erw [Category.id_comp]
    rw [Category.assoc]
    erw [← (F.obj (unop Y)).presheaf.map_comp, (F.map f.unop).c.naturality_assoc,
      ← (F.obj (unop Y)).presheaf.map_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem colimitPresheafObjIsoComponentwiseLimit_inv_ι_app (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).inv ≫ (colimit.ι F j).c.app (op U) =
      limit.π _ (op j) := by
  delta colimitPresheafObjIsoComponentwiseLimit
  rw [Iso.trans_inv, Iso.trans_inv, Iso.app_inv, sheafIsoOfIso_inv, pushforwardToOfIso_app,
    congr_app (Iso.symm_inv _)]
  dsimp
  rw [map_id, comp_id, assoc, assoc, assoc, NatTrans.naturality,
      ← comp_c_app_assoc, congr_app (colimit.isoColimitCocone_ι_hom _ _), assoc,
      colimitCocone_ι_app_c, limitObjIsoLimitCompEvaluation_inv_π_app_assoc, limMap_π_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem colimitPresheafObjIsoComponentwiseLimit_hom_π (F : J ⥤ PresheafedSpace.{_, _, v} C)
    (U : Opens (Limits.colimit F).carrier) (j : J) :
    (colimitPresheafObjIsoComponentwiseLimit F U).hom ≫ limit.π _ (op j) =
      (colimit.ι F j).c.app (op U) := by
  rw [← Iso.eq_inv_comp, colimitPresheafObjIsoComponentwiseLimit_inv_ι_app]

end PresheafedSpace

end AlgebraicGeometry
