/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.Picard.Pullback

/-!
# Monoidality of presheaf pullback composition

The canonical comparison from iterated pullback to pullback along a composite morphism
of schemes is monoidal for the presheaf-of-modules tensor products.

This is an exact-pin port of AINTLIB's `ForMathlib/PresheafPullbackCompMonoidal.lean`
at commit `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`. Its sole source adaptation is
redirecting the import to the retained option-free local pullback foundation.
-/

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace PresheafOfModules

/-- The canonical presheaf pullback-composition comparison is monoidal. -/
theorem pullbackComp_hom_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI : MonoidalCategory (PresheafOfModules
      ((TopologicalSpace.Opens.map f.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) := by
      rw [show (TopologicalSpace.Opens.map f.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) =
          ((TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) ⋙
            forget₂ CommRingCat RingCat by rfl]
      exact PresheafOfModules.monoidalCategory
    letI := pullbackMonoidal g
    letI := pullbackMonoidal f
    letI : (pullback
        (F := TopologicalSpace.Opens.map g.base ⋙ TopologicalSpace.Opens.map f.base)
        (R := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
        (schemeRingPresheafHom g ≫ Functor.whiskerLeft
          (TopologicalSpace.Opens.map g.base).op (schemeRingPresheafHom f))).Monoidal := by
      change (pullback (schemeRingPresheafHom (f ≫ g))).Monoidal
      exact pullbackMonoidal (f ≫ g)
    (pullbackComp (schemeRingPresheafHom g) (schemeRingPresheafHom f)).hom.IsMonoidal := by
  letI : MonoidalCategory (PresheafOfModules
    ((TopologicalSpace.Opens.map f.base).op ⋙
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) := by
    rw [show (TopologicalSpace.Opens.map f.base).op ⋙
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) =
        ((TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) ⋙
          forget₂ CommRingCat RingCat by rfl]
    exact PresheafOfModules.monoidalCategory
  let φg := schemeRingPresheafHom g
  let φf := schemeRingPresheafHom f
  let φfg := schemeRingPresheafHom (f ≫ g)
  letI qG : (pushforwardFactored φg).LaxMonoidal :=
    pushforwardFactoredLaxMonoidal φg
  letI qF : (pushforwardFactored φf).LaxMonoidal :=
    pushforwardFactoredLaxMonoidal φf
  letI qFG : (pushforwardFactored φfg).LaxMonoidal :=
    pushforwardFactoredLaxMonoidal φfg
  letI oG : (pullback φg).OplaxMonoidal := pullbackOplaxMonoidal φg
  haveI : IsIso (Functor.OplaxMonoidal.η (pullback φg)) := isIso_pullback_η g
  haveI : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φg) P Q) :=
    fun P Q => isIso_pullback_δ g P Q
  letI hG : (pullback φg).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φg)
  letI oF : (pullback φf).OplaxMonoidal := pullbackOplaxMonoidal φf
  haveI : IsIso (Functor.OplaxMonoidal.η (pullback φf)) := isIso_pullback_η f
  haveI : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φf) P Q) :=
    fun P Q => isIso_pullback_δ f P Q
  letI hF : (pullback φf).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φf)
  letI oFG : (pullback φfg).OplaxMonoidal := pullbackOplaxMonoidal φfg
  haveI : IsIso (Functor.OplaxMonoidal.η (pullback φfg)) := isIso_pullback_η (f ≫ g)
  haveI : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φfg) P Q) :=
    fun P Q => isIso_pullback_δ (f ≫ g) P Q
  letI hFG : (pullback φfg).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φfg)
  letI hComp : (pullback
      (F := TopologicalSpace.Opens.map g.base ⋙ TopologicalSpace.Opens.map f.base)
      (R := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
      (φg ≫ Functor.whiskerLeft (TopologicalSpace.Opens.map g.base).op φf)).Monoidal := by
    change (pullback φfg).Monoidal
    exact hFG
  letI hadjG : (pullbackPushforwardFactoredAdjunction φg).IsMonoidal := by
    infer_instance
  letI hadjF : (pullbackPushforwardFactoredAdjunction φf).IsMonoidal := by
    infer_instance
  letI hadjFG : (pullbackPushforwardFactoredAdjunction φfg).IsMonoidal := by
    infer_instance
  letI pG : (pushforward φg).LaxMonoidal := by
    change (pushforwardFactored φg).LaxMonoidal
    exact qG
  letI pF : (pushforward φf).LaxMonoidal := by
    change (pushforwardFactored φf).LaxMonoidal
    exact qF
  letI pFG : (pushforward φfg).LaxMonoidal := by
    change (pushforwardFactored φfg).LaxMonoidal
    exact qFG
  have hadjOrigG : (pullbackPushforwardAdjunction φg).IsMonoidal := by
    rw [← pullbackPushforwardFactoredAdjunction_eq φg]
    exact hadjG
  have hadjOrigF : (pullbackPushforwardAdjunction φf).IsMonoidal := by
    rw [← pullbackPushforwardFactoredAdjunction_eq φf]
    exact hadjF
  have hadjOrigFG : (pullbackPushforwardAdjunction φfg).IsMonoidal := by
    rw [← pullbackPushforwardFactoredAdjunction_eq φfg]
    exact hadjFG
  let α : pushforward φfg ⟶ pushforward φf ⋙ pushforward φg :=
    (pushforwardComp φg φf).inv
  have hα : α.IsMonoidal := by
    refine { unit := ?_, tensor := fun M N => ?_ }
    · rfl
    · ext1 U
      refine ModuleCat.MonoidalCategory.tensor_ext (fun x y => ?_)
      rfl
  have hadjOrigComp : ((pullbackPushforwardAdjunction φg).comp
      (pullbackPushforwardAdjunction φf)).IsMonoidal := by
    letI := hadjOrigG
    letI := hadjOrigF
    infer_instance
  have hmate : ((conjugateEquiv
      (pullbackPushforwardAdjunction φfg)
      ((pullbackPushforwardAdjunction φg).comp
        (pullbackPushforwardAdjunction φf))).symm α).IsMonoidal :=
    CategoryTheory.conjugateEquiv_symm_isMonoidal _ _ hadjOrigFG hadjOrigComp α hα
  rw [pullbackComp, Adjunction.leftAdjointCompIso_hom]
  exact hmate

end PresheafOfModules
