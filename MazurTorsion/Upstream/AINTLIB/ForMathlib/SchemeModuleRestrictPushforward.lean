/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restriction and pushforward of scheme modules

This file compares restriction of a pushforward with pushforward after restriction in a
cartesian square whose vertical maps are open immersions.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- On presheaves, restriction of a pushforward agrees with pushforward after restriction in a
cartesian square whose vertical maps are open immersions. -/
noncomputable def restrictPushforwardPresheafIsoOfIsPullback
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) :
    (toPresheafOfModules V).obj
        ((restrictFunctor iV).obj ((pushforward f).obj M)) ≅
      (toPresheafOfModules V).obj
        ((pushforward f').obj ((restrictFunctor iU).obj M)) := by
  refine PresheafOfModules.isoMk (fun W ↦ ?_) ?_
  · let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
    let e := M.presheaf.mapIso (eqToIso h).op
    refine ModuleCat.isoMk e ?_
    intro r
    ext x
    let eR : Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) ≅ Γ(U, f' ⁻¹ᵁ W.unop) :=
      X.presheaf.mapIso (eqToIso h).op ≪≫ iU.appIso _
    have hring : (iV.appIso W.unop).inv ≫ f.app _ = f'.app W.unop ≫ eR.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
      simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom,
        Iso.op_hom, eqToIso.hom, eqToHom_op, Scheme.Hom.appIso_hom',
        Scheme.Hom.map_appLE, eR, Scheme.Hom.appLE_comp_appLE, H.w]
    have hring' : (iV.appIso W.unop).inv ≫ f.app _ ≫ eR.hom =
        f'.app W.unop := by
      rw [← Category.assoc, hring]
      simp
    have hring'' : f'.app W.unop ≫ (iU.appIso (f' ⁻¹ᵁ W.unop)).inv =
        (iV.appIso W.unop).inv ≫ f.app _ ≫
          (X.presheaf.mapIso (eqToIso h).op).hom := by
      rw [← hring']
      simp only [eR, Iso.trans_hom, Category.assoc]
      rw [Iso.hom_inv_id, Category.comp_id]
    have hring''' : f'.app W.unop ≫ (iU.appIso (f' ⁻¹ᵁ W.unop)).inv =
        (iV.appIso W.unop).inv ≫ f.app _ ≫
          X.presheaf.map (eqToHom h).op := by
      simpa only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom] using hring''
    have hr' : (iU.appIso (f' ⁻¹ᵁ W.unop)).inv ((f'.app W.unop).hom r) =
        (X.presheaf.map (eqToHom h).op).hom
          ((f.app (iV ''ᵁ W.unop)).hom ((iV.appIso W.unop).inv r)) := by
      have hr := ConcreteCategory.congr_hom hring''' r
      change (iU.appIso (f' ⁻¹ᵁ W.unop)).inv ((f'.app W.unop).hom r) =
        (X.presheaf.map (eqToHom h).op).hom
          ((f.app (iV ''ᵁ W.unop)).hom ((iV.appIso W.unop).inv r)) at hr
      exact hr
    let x' : M.val.obj (.op (f ⁻¹ᵁ iV ''ᵁ W.unop)) := x
    let rU : Γ(X, iU ''ᵁ (f' ⁻¹ᵁ W.unop)) :=
      (iU.appIso (f' ⁻¹ᵁ W.unop)).inv ((f'.app W.unop).hom r)
    let rX : Γ(X, f ⁻¹ᵁ iV ''ᵁ W.unop) :=
      (f.app (iV ''ᵁ W.unop)).hom ((iV.appIso W.unop).inv r)
    change SMul.smul rU
        (e.hom x' : M.val.obj (.op (iU ''ᵁ (f' ⁻¹ᵁ W.unop)))) =
      e.hom (SMul.smul rX x')
    rw [show rU = (X.presheaf.map (eqToHom h).op).hom rX from hr']
    exact ((M.val.map (eqToHom h).op).hom.map_smul rX x').symm
  · intro W W' g
    apply ModuleCat.hom_ext
    ext x
    let x' : Γ(M, f ⁻¹ᵁ iV ''ᵁ W.unop) := x
    change M.presheaf.map _ (M.presheaf.map _ x') =
      M.presheaf.map _ (M.presheaf.map _ x')
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) x'

/-- Restriction of a pushforward agrees objectwise with pushforward after restriction in a
cartesian square whose vertical maps are open immersions. -/
noncomputable def restrictPushforwardIsoOfIsPullbackApp
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) (M : X.Modules) :
    (restrictFunctor iV).obj ((pushforward f).obj M) ≅
      (pushforward f').obj ((restrictFunctor iU).obj M) :=
  (fullyFaithfulToPresheafOfModules).preimageIso
    (restrictPushforwardPresheafIsoOfIsPullback f f' iU iV H M)

/-- Restriction of a pushforward agrees naturally with pushforward after restriction in a
cartesian square whose vertical maps are open immersions. -/
noncomputable def restrictPushforwardIsoOfIsPullback
    {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV f) :
    pushforward f ⋙ restrictFunctor iV ≅
      restrictFunctor iU ⋙ pushforward f' :=
  NatIso.ofComponents
    (fun M ↦ restrictPushforwardIsoOfIsPullbackApp f f' iU iV H M)
    (by
      intro M N q
      apply (fullyFaithfulToPresheafOfModules).map_injective
      apply PresheafOfModules.hom_ext
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
      change (N.val.map (eqToHom h).op).hom ((q.val.app _).hom x) =
        (q.val.app _).hom
          (show M.val.obj (.op (iU ''ᵁ (f' ⁻¹ᵁ W.unop))) from
            (M.val.map (eqToHom h).op).hom x)
      exact ConcreteCategory.congr_hom (q.val.naturality (eqToHom h).op).symm x)

end

end AlgebraicGeometry.Scheme.Modules
