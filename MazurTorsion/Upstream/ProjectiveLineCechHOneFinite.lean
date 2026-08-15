/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleQuasicoherent
import MazurTorsion.Upstream.SchemeModuleBaseCechHOneFinite
import MazurTorsion.Upstream.SchemeModuleFinitePushforwardCech
import TauCeti.AlgebraicGeometry.ProjectiveLine.Smooth

/-!
# Coherent degree-one cohomology on the projective line

This file proves the target-side input needed to descend coherent `H¹`
finiteness along Tau Ceti's finite rational-function morphism.  The algebraic
core is the finite-principal-parts argument for the two standard affine
charts: a finite module over the polynomial chart has only finitely many
negative powers left after quotienting by sections from the chart at
infinity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Opposite

namespace MazurTorsion.AlgebraicGeometry.ProjectiveLineCohomology

universe u v w

open _root_.AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.ProjectiveLine
open _root_.MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

private abbrev TwoIndex (_K : Type u) := ULift.{u} (Fin 2)

private def standardCover (K : Type u) [Field K] :
    TwoIndex K → (scheme K).Opens
  | ⟨0⟩ => standardAffineOpen K
  | ⟨1⟩ => infinityAffineOpen K

private def leftIndex (K : Type u) : OrderedCechIndex (TwoIndex K) 0 :=
  ⟨fun _ ↦ ⟨0⟩, by intro a b h; fin_cases a; fin_cases b; simp at h⟩

private def rightIndex (K : Type u) : OrderedCechIndex (TwoIndex K) 0 :=
  ⟨fun _ ↦ ⟨1⟩, by intro a b h; fin_cases a; fin_cases b; simp at h⟩

private def pairIndex (K : Type u) : OrderedCechIndex (TwoIndex K) 1 :=
  ⟨fun j ↦ ⟨j⟩, fun _ _ h ↦ h⟩

private theorem orderedCechIndex_one_eq_pair
    (K : Type u) (i : OrderedCechIndex (TwoIndex K) 1) :
    i = pairIndex K := by
  have hi : StrictMono (fun j ↦ (i.1 j).down) := fun _ _ h ↦ i.2 h
  have hid : (fun j ↦ (i.1 j).down) = id := hi.eq_id
  apply Subtype.ext
  funext j
  apply ULift.ext
  simpa only [pairIndex, id_eq] using congrFun hid j

private theorem isEmpty_orderedCechIndex_two (K : Type u) :
    IsEmpty (OrderedCechIndex (TwoIndex K) 2) := by
  constructor
  intro i
  have hcard := Fintype.card_le_of_injective i.1 i.2.injective
  norm_num at hcard

private theorem orderedBaseCechComplex_d_one_two_standardCover_zero
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (orderedBaseCechComplex (structureMap K) M
      (standardCover K : TwoIndex K → (scheme K).Opens)).d 1 2 = 0 := by
  letI := isEmpty_orderedCechIndex_two K
  let Z := ModuleCat.of
    Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
    (orderedBaseCechTerm (structureMap K) M
      (standardCover K : TwoIndex K → (scheme K).Opens) 2)
  have hZ : IsZero Z := ModuleCat.isZero_of_subsingleton Z
  have hterm : IsZero
      (orderedBaseCechObject (structureMap K) M
        (standardCover K : TwoIndex K → (scheme K).Opens) 2) :=
    hZ.of_iso (orderedBaseCechObjectIsoPi
      (structureMap K) M
      (standardCover K : TwoIndex K → (scheme K).Opens) 2)
  exact hterm.eq_of_tgt _ _

/- The following chart computations are adapted from the private proofs in
Tau Ceti's `ProjectiveLine.Basic`.  They are repeated here because the
cohomology argument needs the resulting section identities, while the
upstream declarations intentionally are not public. -/

private lemma basicOpenIsoSpec_hom_appTop_affineCoordinateAway
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) =
      (standardAffineOpen K).topIso.inv (affineCoordinate K) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))).app ⊤
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K)) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (standardAffineOpen K).topIso.inv)
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K))) =
    (standardAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (affineCoordinateAway K))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_affineCoordinate
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one).inv.appTop
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  change e.inv.appTop ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun z ↦ e.inv.appTop z) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((standardAffineOpen K).topIso.inv (affineCoordinate K)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_affineCoordinateAway K).symm

private lemma awayι_preimage_standardAffineOpen (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one ⁻¹ᵁ standardAffineOpen K = ⊤ := by
  change Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) = ⊤
  rw [← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one]
  exact Scheme.Hom.preimage_opensRange _

private lemma awayι_appLE_affineCoordinate (K : Type u) [Field K] :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge (affineCoordinate K) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
        (affineCoordinateAway K) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  have hres : φ.resLE (standardAffineOpen K) ⊤
      (awayι_preimage_standardAffineOpen K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (standardAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (standardAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg
    (fun h ↦ h ((standardAffineOpen K).topIso.inv (affineCoordinate K))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge) (affineCoordinate K)) =
      (φ.resLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge).app ⊤
        ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge) (affineCoordinate K)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge)
            ((standardAffineOpen K).topIso.hom
              ((standardAffineOpen K).topIso.inv (affineCoordinate K))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv
        ((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv
            (affineCoordinateAway K)) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((standardAffineOpen K).topIso.inv (affineCoordinate K))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_affineCoordinate]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

private lemma basicOpenIsoSpec_hom_appTop_standard
    (K : Type u) [Field K]
    (z : HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))) :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv z) =
      (standardAffineOpen K).topIso.inv
        (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) z) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))).app ⊤ ((Scheme.ΓSpecIso _).inv z) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (standardAffineOpen K).topIso.inv) ((Scheme.ΓSpecIso _).inv z)) =
    (standardAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) z)
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_standard
    (K : Type u) [Field K]
    (z : HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))) :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one).inv.appTop
      ((standardAffineOpen K).topIso.inv
        (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) z)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv z := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun w ↦ e.inv.appTop w) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((standardAffineOpen K).topIso.inv
        (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) z)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_standard K z).symm

private lemma awayι_appLE_awayToSection_standard
    (K : Type u) [Field K]
    (z : HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))) :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge
        (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) z) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).inv z := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  have hres : φ.resLE (standardAffineOpen K) ⊤
      (awayι_preimage_standardAffineOpen K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (standardAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (standardAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg (fun h ↦ h ((standardAffineOpen K).topIso.inv
    (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) z))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge)
          (Proj.awayToSection (homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2)) z)) =
      (φ.resLE (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge).app ⊤
        ((standardAffineOpen K).topIso.inv
          (Proj.awayToSection (homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2)) z))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge)
            (Proj.awayToSection (homogeneousPieces K)
              (MvPolynomial.X (1 : Fin 2)) z)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge)
            ((standardAffineOpen K).topIso.hom
              ((standardAffineOpen K).topIso.inv
                (Proj.awayToSection (homogeneousPieces K)
                  (MvPolynomial.X (1 : Fin 2)) z))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv ((Scheme.ΓSpecIso _).inv z) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((standardAffineOpen K).topIso.inv
            (Proj.awayToSection (homogeneousPieces K)
              (MvPolynomial.X (1 : Fin 2)) z))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_standard]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

private lemma standardAffinePolynomialEquiv_C
    (K : Type u) [Field K] (c : homogeneousPieces K 0) :
    standardAffinePolynomialEquiv K (Polynomial.C c) =
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (algebraMap (homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))) c) := by
  simp [standardAffinePolynomialEquiv, Polynomial.C_eq_algebraMap]
  rfl

private noncomputable def standardBaseToAway
    (K : Type u) [Field K] :
    K →+* HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
      (Submonoid.powers (MvPolynomial.X (1 : Fin 2)))).comp
    (degreeZeroRingEquiv K).toRingHom

private lemma awayι_standard_comp_structureMap
    (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one ≫ structureMap K =
      Spec.map (CommRingCat.ofHom (standardBaseToAway K)) := by
  rw [structureMap, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

private lemma awayι_appLE_standard_injective
    (K : Type u) [Field K] :
    Function.Injective
      ((Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one).appLE
          (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2)) (X_one_mem_degree_one K)
      Nat.zero_lt_one).hom).2 x
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2)) (X_one_mem_degree_one K)
      Nat.zero_lt_one).hom).2 y
  change Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2)) x =
    Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2)) y
  change (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).appLE
        (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge
        (Proj.awayToSection (homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2)) x) =
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).appLE
        (standardAffineOpen K) ⊤
        (awayι_preimage_standardAffineOpen K).ge
        (Proj.awayToSection (homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2)) y) at hxy
  rw [awayι_appLE_awayToSection_standard,
    awayι_appLE_awayToSection_standard] at hxy
  exact congrArg (Proj.awayToSection (homogeneousPieces K)
    (MvPolynomial.X (1 : Fin 2)))
      ((ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of <|
          HomogeneousLocalization.Away (homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2)))).inv).1 hxy)

private lemma standardAffineOpen_le_structureMap_preimage_top
    (K : Type u) [Field K] :
    standardAffineOpen K ≤ structureMap K ⁻¹ᵁ
      (⊤ : (Spec (.of K)).Opens) := by
  simp

private lemma standardAffinePolynomialEquiv_C_base
    (K : Type u) [Field K]
    (r : Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))) :
    standardAffinePolynomialEquiv K
        (Polynomial.C (degreeZeroRingEquiv K
      ((Scheme.ΓSpecIso (.of K)).hom r))) =
      (structureMap K).appLE ⊤ (standardAffineOpen K)
        (standardAffineOpen_le_structureMap_preimage_top K) r := by
  apply awayι_appLE_standard_injective K
  rw [standardAffinePolynomialEquiv_C,
    awayι_appLE_awayToSection_standard]
  change (Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))).inv
        ((algebraMap (homogeneousPieces K 0)
          (HomogeneousLocalization.Away (homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (degreeZeroRingEquiv K ((Scheme.ΓSpecIso (.of K)).hom r))) =
    ((structureMap K).appLE ⊤ (standardAffineOpen K)
      (standardAffineOpen_le_structureMap_preimage_top K) ≫
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one).appLE
          (standardAffineOpen K) ⊤
          (awayι_preimage_standardAffineOpen K).ge) r
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  have hcomp := Scheme.Hom.appLE_comp_appLE φ (structureMap K)
    ⊤ (standardAffineOpen K) ⊤
      (standardAffineOpen_le_structureMap_preimage_top K)
      (awayι_preimage_standardAffineOpen K).ge
  have hcomp_r := ConcreteCategory.congr_hom hcomp r
  change _ = ((structureMap K).appLE ⊤ (standardAffineOpen K)
    (standardAffineOpen_le_structureMap_preimage_top K) ≫
    φ.appLE (standardAffineOpen K) ⊤
      (awayι_preimage_standardAffineOpen K).ge) r
  rw [hcomp_r]
  rw [awayι_standard_comp_structureMap]
  change (Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))).inv
        (standardBaseToAway K ((Scheme.ΓSpecIso (.of K)).hom r)) =
    (Spec.map (CommRingCat.ofHom (standardBaseToAway K))).appTop r
  calc
    _ = (CommRingCat.ofHom (standardBaseToAway K) ≫
          (Scheme.ΓSpecIso (.of <|
            HomogeneousLocalization.Away (homogeneousPieces K)
              (MvPolynomial.X (1 : Fin 2)))).inv)
        ((Scheme.ΓSpecIso (.of K)).hom r) := rfl
    _ = ((Scheme.ΓSpecIso (.of K)).inv ≫
          (Spec.map (CommRingCat.ofHom (standardBaseToAway K))).appTop)
        ((Scheme.ΓSpecIso (.of K)).hom r) := by
      rw [Scheme.ΓSpecIso_inv_naturality]
    _ = (Spec.map (CommRingCat.ofHom (standardBaseToAway K))).appTop
        ((Scheme.ΓSpecIso (.of K)).inv
          ((Scheme.ΓSpecIso (.of K)).hom r)) := rfl
    _ = _ := by rw [Iso.hom_inv_id_apply]

private noncomputable def baseDegreeZeroEquiv
    (K : Type u) [Field K] :
    Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) ≃+*
      homogeneousPieces K 0 :=
  (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.trans
    (degreeZeroRingEquiv K)

private theorem standard_eval₂_surjective
    (K : Type u) [Field K] :
    Function.Surjective
      (Polynomial.eval₂RingHom
        ((structureMap K).appLE ⊤ (standardAffineOpen K)
          (standardAffineOpen_le_structureMap_preimage_top K)).hom
        (affineCoordinate K)) := by
  let e : Polynomial Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) ≃+*
      Γ(scheme K, standardAffineOpen K) :=
    (Polynomial.mapEquiv (baseDegreeZeroEquiv K)).trans
      (standardAffinePolynomialEquiv K)
  have heval :
      Polynomial.eval₂RingHom
          ((structureMap K).appLE ⊤ (standardAffineOpen K)
            (standardAffineOpen_le_structureMap_preimage_top K)).hom
          (affineCoordinate K) =
        e.toRingHom := by
    ext r
    · simp only [RingHom.comp_apply]
      change Polynomial.eval₂
          ((structureMap K).appLE ⊤ (standardAffineOpen K)
            (standardAffineOpen_le_structureMap_preimage_top K)).hom
          (affineCoordinate K) (Polynomial.C r) = e (Polynomial.C r)
      rw [Polynomial.eval₂_C]
      rw [← standardAffinePolynomialEquiv_C_base K r]
      simp [e, baseDegreeZeroEquiv, Polynomial.mapEquiv_apply]
      rfl
    · simp [e, Polynomial.mapEquiv_apply]
  rw [heval]
  exact e.surjective

private lemma basicOpenIsoSpec_hom_appTop_inverseAffineCoordinateAway
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) Nat.zero_lt_one).hom.appTop
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K)) =
      (infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K) := by
  rw [Proj.basicOpenIsoSpec_hom]
  change (Proj.basicOpenToSpec (homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))).app ⊤
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K)) = _
  rw [Proj.basicOpenToSpec_app_top]
  change (((Scheme.ΓSpecIso (.of <|
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).hom ≫
      Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) ≫
      (infinityAffineOpen K).topIso.inv)
      ((Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K))) =
    (infinityAffineOpen K).topIso.inv
      (Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (inverseAffineCoordinateAway K))
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private lemma basicOpenIsoSpec_inv_appTop_inverseAffineCoordinate
    (K : Type u) [Field K] :
    (Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) Nat.zero_lt_one).inv.appTop
      ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K)) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K) := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) Nat.zero_lt_one
  change e.inv.appTop ((infinityAffineOpen K).topIso.inv
    (inverseAffineCoordinate K)) = _
  have hinj : Function.Injective e.hom.appTop := by
    intro x y hxy
    have h := congrArg (fun z ↦ e.inv.appTop z) hxy
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply] using h
  apply hinj
  change (e.inv.appTop ≫ e.hom.appTop)
      ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K)) = _
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact (basicOpenIsoSpec_hom_appTop_inverseAffineCoordinateAway K).symm

private lemma awayι_preimage_infinityAffineOpen (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) Nat.zero_lt_one ⁻¹ᵁ infinityAffineOpen K = ⊤ := by
  change Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) Nat.zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) = ⊤
  rw [← Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) Nat.zero_lt_one]
  exact Scheme.Hom.preimage_opensRange _

private lemma awayι_appLE_inverseAffineCoordinate (K : Type u) [Field K] :
    (Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) Nat.zero_lt_one).appLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen K).ge (inverseAffineCoordinate K) =
      (Scheme.ΓSpecIso (.of <|
        HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
        (inverseAffineCoordinateAway K) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) Nat.zero_lt_one
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) Nat.zero_lt_one
  have hres : φ.resLE (infinityAffineOpen K) ⊤
      (awayι_preimage_infinityAffineOpen K).ge =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv := by
    apply (cancel_mono (infinityAffineOpen K).ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    change (⊤ : (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens).ι ≫ φ =
      ((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv) ≫
        (infinityAffineOpen K).ι
    simp only [Category.assoc, Scheme.topIso_hom, e, φ,
      Proj.basicOpenIsoSpec_inv_ι]
  have happ := congrArg Scheme.Hom.appTop hres
  have heval := congrArg
    (fun h ↦ h ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))) happ
  let V : (Spec (.of <| HomogeneousLocalization.Away
    (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens := ⊤
  apply V.topIso.symm.commRingCatIsoToRingEquiv.injective
  convert heval using 1
  · change V.topIso.inv
      ((φ.appLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen K).ge) (inverseAffineCoordinate K)) =
      (φ.resLE (infinityAffineOpen K) ⊤
        (awayι_preimage_infinityAffineOpen K).ge).app ⊤
        ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))
    rw [Scheme.Hom.resLE_app_top]
    change V.topIso.inv
        ((φ.appLE (infinityAffineOpen K) ⊤
          (awayι_preimage_infinityAffineOpen K).ge) (inverseAffineCoordinate K)) =
      (⊤ : (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).Opens).topIso.inv
        ((φ.appLE (infinityAffineOpen K) ⊤
          (awayι_preimage_infinityAffineOpen K).ge)
            ((infinityAffineOpen K).topIso.hom
              ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))))
    rw [Iso.inv_hom_id_apply]
  · change V.topIso.inv
        ((Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).inv
            (inverseAffineCoordinateAway K)) =
        (((Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).topIso.hom ≫ e.inv).appTop)
          ((infinityAffineOpen K).topIso.inv (inverseAffineCoordinate K))
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [basicOpenIsoSpec_inv_appTop_inverseAffineCoordinate]
    dsimp [V]
    simp only [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl

private abbrev affineOverlapOpen (K : Type u) [Field K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

private lemma affineOverlapOpen_le_infinityAffineOpen
    (K : Type u) [Field K] :
    affineOverlapOpen K ≤ infinityAffineOpen K :=
  Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X (1 : Fin 2), rfl⟩

private lemma affineOverlapOpen_le_standardAffineOpen
    (K : Type u) [Field K] :
    affineOverlapOpen K ≤ standardAffineOpen K :=
  Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X (0 : Fin 2), mul_comm _ _⟩

private lemma inverseAffineCoordinateAway_mul_affineCoordinateAway_on_overlap
    (K : Type u) [Field K] :
    HomogeneousLocalization.awayMap (homogeneousPieces K)
        (X_one_mem_degree_one K) (show
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) =
            MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) from rfl)
        (inverseAffineCoordinateAway K) *
      HomogeneousLocalization.awayMap (homogeneousPieces K)
        (X_zero_mem_degree_one K) (show
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) =
            MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) from mul_comm _ _)
        (affineCoordinateAway K) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    inverseAffineCoordinateAway, affineCoordinateAway,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

private lemma inverseAffineCoordinate_mul_affineCoordinate_on_overlap
    (K : Type u) [Field K] :
    (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op
        (inverseAffineCoordinate K) *
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op
        (affineCoordinate K) = 1 := by
  change ((Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) ≫
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op)
        (inverseAffineCoordinateAway K)) *
    ((Proj.awayToSection (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) ≫
      (scheme K).presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op)
        (affineCoordinateAway K)) = 1
  rw [← Proj.awayMap_awayToSection (homogeneousPieces K)
      (X_one_mem_degree_one K) rfl,
    ← Proj.awayMap_awayToSection (homogeneousPieces K)
      (X_zero_mem_degree_one K) (mul_comm _ _)]
  change (Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))
        (HomogeneousLocalization.awayMap (homogeneousPieces K)
          (X_one_mem_degree_one K) rfl (inverseAffineCoordinateAway K)) *
    (Proj.awayToSection (homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))
        (HomogeneousLocalization.awayMap (homogeneousPieces K)
          (X_zero_mem_degree_one K) (mul_comm _ _) (affineCoordinateAway K)) = 1
  rw [← map_mul, inverseAffineCoordinateAway_mul_affineCoordinateAway_on_overlap, map_one]

private lemma standard_isLocalizationElem_eq_affineCoordinateAway
    (K : Type u) [Field K] :
    HomogeneousLocalization.Away.isLocalizationElem
      (X_one_mem_degree_one K) (X_zero_mem_degree_one K) =
        affineCoordinateAway K := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.isLocalizationElem, affineCoordinateAway,
    HomogeneousLocalization.Away.val_mk]

private lemma infinity_isLocalizationElem_eq_inverseAffineCoordinateAway
    (K : Type u) [Field K] :
    HomogeneousLocalization.Away.isLocalizationElem
      (X_zero_mem_degree_one K) (X_one_mem_degree_one K) =
        inverseAffineCoordinateAway K := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.isLocalizationElem, inverseAffineCoordinateAway,
    HomogeneousLocalization.Away.val_mk]

private lemma awayι_standard_preimage_infinityAffineOpen
    (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
        (X_one_mem_degree_one K) Nat.zero_lt_one ⁻¹ᵁ infinityAffineOpen K =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).basicOpen
          ((Scheme.ΓSpecIso _).inv (affineCoordinateAway K)) := by
  rw [basicOpen_eq_of_affine']
  simpa only [Iso.inv_hom_id_apply,
    standard_isLocalizationElem_eq_affineCoordinateAway] using
      (Proj.awayι_preimage_basicOpen (homogeneousPieces K)
        (X_one_mem_degree_one K) Nat.zero_lt_one
        (X_zero_mem_degree_one K) Nat.zero_lt_one)

private lemma awayι_infinity_preimage_standardAffineOpen
    (K : Type u) [Field K] :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
        (X_zero_mem_degree_one K) Nat.zero_lt_one ⁻¹ᵁ standardAffineOpen K =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).basicOpen
          ((Scheme.ΓSpecIso _).inv (inverseAffineCoordinateAway K)) := by
  rw [basicOpen_eq_of_affine']
  simpa only [Iso.inv_hom_id_apply,
    infinity_isLocalizationElem_eq_inverseAffineCoordinateAway] using
      (Proj.awayι_preimage_basicOpen (homogeneousPieces K)
        (X_zero_mem_degree_one K) Nat.zero_lt_one
        (X_one_mem_degree_one K) Nat.zero_lt_one)

private lemma awayι_standard_preimage_basicOpen_affineCoordinate
    (K : Type u) [Field K] :
    let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one
    φ ⁻¹ᵁ (scheme K).basicOpen (affineCoordinate K) =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).basicOpen
          ((Scheme.ΓSpecIso _).inv (affineCoordinateAway K)) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  calc
    φ ⁻¹ᵁ (scheme K).basicOpen (affineCoordinate K) =
        (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).basicOpen
            (φ.appLE (standardAffineOpen K) ⊤
              (awayι_preimage_standardAffineOpen K).ge (affineCoordinate K)) := by
          rw [Scheme.basicOpen_appLE]
          simp
    _ = (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))).basicOpen
            ((Scheme.ΓSpecIso _).inv (affineCoordinateAway K)) := by
      rw [awayι_appLE_affineCoordinate]

private lemma awayι_infinity_preimage_basicOpen_inverseAffineCoordinate
    (K : Type u) [Field K] :
    let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) Nat.zero_lt_one
    φ ⁻¹ᵁ (scheme K).basicOpen (inverseAffineCoordinate K) =
      (Spec (.of <| HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).basicOpen
          ((Scheme.ΓSpecIso _).inv (inverseAffineCoordinateAway K)) := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) Nat.zero_lt_one
  calc
    φ ⁻¹ᵁ (scheme K).basicOpen (inverseAffineCoordinate K) =
        (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).basicOpen
            (φ.appLE (infinityAffineOpen K) ⊤
              (awayι_preimage_infinityAffineOpen K).ge
                (inverseAffineCoordinate K)) := by
          rw [Scheme.basicOpen_appLE]
          simp
    _ = (Spec (.of <| HomogeneousLocalization.Away
          (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))).basicOpen
            ((Scheme.ΓSpecIso _).inv (inverseAffineCoordinateAway K)) := by
      rw [awayι_appLE_inverseAffineCoordinate]

private lemma basicOpen_affineCoordinate_eq_affineOverlapOpen
    (K : Type u) [Field K] :
    (scheme K).basicOpen (affineCoordinate K) = affineOverlapOpen K := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) Nat.zero_lt_one
  have hpre : φ ⁻¹ᵁ (scheme K).basicOpen (affineCoordinate K) =
      φ ⁻¹ᵁ affineOverlapOpen K := by
    rw [awayι_standard_preimage_basicOpen_affineCoordinate,
      affineOverlapOpen, Proj.basicOpen_mul, Scheme.Hom.preimage_inf,
      awayι_standard_preimage_infinityAffineOpen,
      awayι_preimage_standardAffineOpen, inf_top_eq]
  calc
    (scheme K).basicOpen (affineCoordinate K) =
        φ ''ᵁ φ ⁻¹ᵁ (scheme K).basicOpen (affineCoordinate K) := by
      rw [φ.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι,
        ]
      exact (inf_eq_right.mpr ((scheme K).basicOpen_le
        (affineCoordinate K))).symm
    _ = φ ''ᵁ φ ⁻¹ᵁ affineOverlapOpen K := congrArg (φ ''ᵁ ·) hpre
    _ = affineOverlapOpen K := by
      rw [φ.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι,
        ]
      exact inf_eq_right.mpr (affineOverlapOpen_le_standardAffineOpen K)

private lemma basicOpen_inverseAffineCoordinate_eq_affineOverlapOpen
    (K : Type u) [Field K] :
    (scheme K).basicOpen (inverseAffineCoordinate K) = affineOverlapOpen K := by
  let φ := Proj.awayι (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) Nat.zero_lt_one
  have hpre : φ ⁻¹ᵁ (scheme K).basicOpen (inverseAffineCoordinate K) =
      φ ⁻¹ᵁ affineOverlapOpen K := by
    rw [awayι_infinity_preimage_basicOpen_inverseAffineCoordinate,
      affineOverlapOpen, Proj.basicOpen_mul, Scheme.Hom.preimage_inf,
      awayι_preimage_infinityAffineOpen,
      awayι_infinity_preimage_standardAffineOpen, top_inf_eq]
  calc
    (scheme K).basicOpen (inverseAffineCoordinate K) =
        φ ''ᵁ φ ⁻¹ᵁ (scheme K).basicOpen (inverseAffineCoordinate K) := by
      rw [φ.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι,
        ]
      exact (inf_eq_right.mpr ((scheme K).basicOpen_le
        (inverseAffineCoordinate K))).symm
    _ = φ ''ᵁ φ ⁻¹ᵁ affineOverlapOpen K := congrArg (φ ''ᵁ ·) hpre
    _ = affineOverlapOpen K := by
      rw [φ.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι,
        ]
      exact inf_eq_right.mpr (affineOverlapOpen_le_infinityAffineOpen K)

private noncomputable def standardToOverlapBaseLinear
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (baseModulePresheaf (structureMap K) M).obj
        (op (standardAffineOpen K)) ⟶
      (baseModulePresheaf (structureMap K) M).obj
        (op (affineOverlapOpen K)) :=
  (baseModulePresheaf (structureMap K) M).map
    (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op

private noncomputable def infinityToOverlapBaseLinear
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (baseModulePresheaf (structureMap K) M).obj
        (op (infinityAffineOpen K)) ⟶
      (baseModulePresheaf (structureMap K) M).obj
        (op (affineOverlapOpen K)) :=
  (baseModulePresheaf (structureMap K) M).map
    (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op

private lemma standardCover_pairIntersection_eq_affineOverlapOpen
    (K : Type u) [Field K] :
    (∏ᶜ fun k : Fin 2 => standardCover K ((pairIndex K).1 k)) =
      affineOverlapOpen K := by
  rw [show (∏ᶜ fun k : Fin 2 => standardCover K ((pairIndex K).1 k)) =
      ⨅ k, standardCover K ((pairIndex K).1 k) from
    (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (Preorder.isLimitIInf _)).to_eq]
  rw [affineOverlapOpen, Proj.basicOpen_mul]
  ext x
  simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  constructor
  · intro hx
    have hstd := hx (0 : Fin 2)
    have hinf := hx (1 : Fin 2)
    change x ∈ standardAffineOpen K at hstd
    change x ∈ infinityAffineOpen K at hinf
    exact ⟨hinf, hstd⟩
  · rintro ⟨hinf, hstd⟩ k
    fin_cases k
    · exact hstd
    · exact hinf

private noncomputable def pairFactorIsoOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    baseCechFactor (structureMap K) M (standardCover K) 1
        (pairIndex K).1 ≅
      (baseModulePresheaf (structureMap K) M).obj
        (op (affineOverlapOpen K)) :=
  (baseModulePresheaf (structureMap K) M).mapIso
    (eqToIso (standardCover_pairIntersection_eq_affineOverlapOpen K)).symm.op

private noncomputable def orderedDegreeOneOverlapLinearEquiv
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (orderedBaseCechComplex (structureMap K) M
        (standardCover K : TwoIndex K → (scheme K).Opens)).X 1 ≃ₗ[
      Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))]
      (baseModulePresheaf (structureMap K) M).obj
        (op (affineOverlapOpen K)) := by
  let F := fun j : OrderedCechIndex (TwoIndex K) 1 ↦
    baseCechFactor (structureMap K) M (standardCover K) 1 j.1
  let p : (∀ i, F i) →ₗ[
      Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))] F (pairIndex K) :=
    { toFun := fun x ↦ x (pairIndex K)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      funext i
      have hi := orderedCechIndex_one_eq_pair K i
      subst i
      exact hxy
    · intro y
      let x : ∀ i : OrderedCechIndex (TwoIndex K) 1, F i := fun i ↦ by
        have hi := orderedCechIndex_one_eq_pair K i
        subst i
        exact y
      refine ⟨x, ?_⟩
      rfl
  exact (orderedBaseCechObjectIsoPi
      (structureMap K) M (standardCover K) 1).toLinearEquiv |>.trans
    ((LinearEquiv.ofBijective p hp).trans
      (pairFactorIsoOverlap K M).toLinearEquiv)

private theorem cechSingletonIntersection_eq
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 => U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun k : Fin 1 => U (i k)) 0)
  · exact leOfHom (Pi.lift fun k : Fin 1 => homOfLE (by
      rw [Subsingleton.elim k 0]))

private noncomputable def leftFactorIsoChart
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    baseCechFactor (structureMap K) M (standardCover K) 0
        (leftIndex K).1 ≅
      (baseModulePresheaf (structureMap K) M).obj
        (op (standardAffineOpen K)) :=
  (baseModulePresheaf (structureMap K) M).mapIso
    (eqToIso (by
      simpa only [standardCover, leftIndex] using
        cechSingletonIntersection_eq (standardCover K) (leftIndex K).1)).symm.op

private noncomputable def rightFactorIsoChart
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    baseCechFactor (structureMap K) M (standardCover K) 0
        (rightIndex K).1 ≅
      (baseModulePresheaf (structureMap K) M).obj
        (op (infinityAffineOpen K)) :=
  (baseModulePresheaf (structureMap K) M).mapIso
    (eqToIso (by
      simpa only [standardCover, rightIndex] using
        cechSingletonIntersection_eq (standardCover K) (rightIndex K).1)).symm.op

private noncomputable def degreeOneToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    orderedBaseCechObject (structureMap K) M
        (standardCover K : TwoIndex K → (scheme K).Opens) 1 ⟶
      (baseModulePresheaf (structureMap K) M).obj
        (op (affineOverlapOpen K)) :=
  (orderedDegreeOneOverlapLinearEquiv K M).toModuleIso.hom

private noncomputable def leftChartToDegreeZero
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (baseModulePresheaf (structureMap K) M).obj
        (op (standardAffineOpen K)) ⟶
      orderedBaseCechObject (structureMap K) M
        (standardCover K : TwoIndex K → (scheme K).Opens) 0 :=
  by
    classical
    exact (leftFactorIsoChart K M).inv ≫
      Pi.ι (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
        baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
        (leftIndex K)

private noncomputable def rightChartToDegreeZero
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (baseModulePresheaf (structureMap K) M).obj
        (op (infinityAffineOpen K)) ⟶
      orderedBaseCechObject (structureMap K) M
        (standardCover K : TwoIndex K → (scheme K).Opens) 0 :=
  by
    classical
    exact (rightFactorIsoChart K M).inv ≫
      Pi.ι (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
        baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
        (rightIndex K)

private theorem pairIndex_delete_zero
    (K : Type u) : (pairIndex K).delete 0 = rightIndex K := by
  apply Subtype.ext
  funext j
  fin_cases j
  rfl

private theorem pairIndex_delete_one
    (K : Type u) : (pairIndex K).delete 1 = leftIndex K := by
  apply Subtype.ext
  funext j
  fin_cases j
  rfl

private theorem leftIndex_ne_rightIndex
    (K : Type u) : leftIndex K ≠ rightIndex K := by
  intro h
  have hzero := congrArg (fun i : OrderedCechIndex (TwoIndex K) 0 ↦ i.1 0) h
  simp only [leftIndex, rightIndex, ULift.ext_iff, zero_ne_one] at hzero

private theorem degreeOneToOverlap_eq_projection
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    degreeOneToOverlap K M =
      Pi.π (fun j : OrderedCechIndex (TwoIndex K) 1 ↦
        baseCechFactor (structureMap K) M (standardCover K) 1 j.1)
          (pairIndex K) ≫
        (pairFactorIsoOverlap K M).hom := by
  ext x
  rfl

private theorem leftFactorRestriction_eq_standardToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (leftFactorIsoChart K M).inv ≫
        eqToHom (congrArg (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
          baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
            (pairIndex_delete_one K)).symm ≫
        (baseModulePresheaf (structureMap K) M).map
          (((FormalCoproduct.mk _ (standardCover K)).mapPower
            (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ
              (pairIndex K).1).op ≫
        (pairFactorIsoOverlap K M).hom =
      standardToOverlapBaseLinear K M := by
  let F := baseModulePresheaf (structureMap K) M
  let G := fun j : OrderedCechIndex (TwoIndex K) 0 ↦
    op (∏ᶜ fun k : Fin 1 ↦ standardCover K (j.1 k))
  let a := (eqToIso (by
    simpa only [standardCover, leftIndex] using
      cechSingletonIntersection_eq (standardCover K) (leftIndex K).1)).symm.op.inv
  let b := eqToHom (congrArg G (pairIndex_delete_one K)).symm
  let c := (((FormalCoproduct.mk _ (standardCover K)).mapPower
    (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ (pairIndex K).1).op
  let d :=
    (eqToIso (standardCover_pairIntersection_eq_affineOverlapOpen K)).symm.op.hom
  have hcast :
      eqToHom (congrArg (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
        baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
          (pairIndex_delete_one K)).symm =
        F.map b := by
    change eqToHom _ = F.map (eqToHom _)
    rw [eqToHom_map]
  have hopen :
      ((a ≫ b) ≫ c) ≫ d =
          (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op := by
    apply Subsingleton.elim
  rw [hcast]
  simp only [leftFactorIsoChart, pairFactorIsoOverlap,
    standardToOverlapBaseLinear, Functor.mapIso_inv, Functor.mapIso_hom]
  change F.map a ≫ F.map b ≫ F.map c ≫ F.map d = F.map _
  calc
    _ = (F.map a ≫ F.map b) ≫ (F.map c ≫ F.map d) :=
      (Category.assoc (F.map a) (F.map b) (F.map c ≫ F.map d)).symm
    _ = F.map (a ≫ b) ≫ (F.map c ≫ F.map d) :=
      congrArg (fun q ↦ q ≫ (F.map c ≫ F.map d)) (F.map_comp a b).symm
    _ = (F.map (a ≫ b) ≫ F.map c) ≫ F.map d :=
      (Category.assoc (F.map (a ≫ b)) (F.map c) (F.map d)).symm
    _ = F.map ((a ≫ b) ≫ c) ≫ F.map d :=
      congrArg (fun q ↦ q ≫ F.map d) (F.map_comp (a ≫ b) c).symm
    _ = F.map (((a ≫ b) ≫ c) ≫ d) := (F.map_comp ((a ≫ b) ≫ c) d).symm
    _ = _ := congrArg F.map hopen

private theorem rightFactorRestriction_eq_infinityToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    (rightFactorIsoChart K M).inv ≫
        eqToHom (congrArg (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
          baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
            (pairIndex_delete_zero K)).symm ≫
        (baseModulePresheaf (structureMap K) M).map
          (((FormalCoproduct.mk _ (standardCover K)).mapPower
            (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ
              (pairIndex K).1).op ≫
        (pairFactorIsoOverlap K M).hom =
      infinityToOverlapBaseLinear K M := by
  let F := baseModulePresheaf (structureMap K) M
  let G := fun j : OrderedCechIndex (TwoIndex K) 0 ↦
    op (∏ᶜ fun k : Fin 1 ↦ standardCover K (j.1 k))
  let a := (eqToIso (by
    simpa only [standardCover, rightIndex] using
      cechSingletonIntersection_eq (standardCover K) (rightIndex K).1)).symm.op.inv
  let b := eqToHom (congrArg G (pairIndex_delete_zero K)).symm
  let c := (((FormalCoproduct.mk _ (standardCover K)).mapPower
    (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ (pairIndex K).1).op
  let d :=
    (eqToIso (standardCover_pairIntersection_eq_affineOverlapOpen K)).symm.op.hom
  have hcast :
      eqToHom (congrArg (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
        baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
          (pairIndex_delete_zero K)).symm =
        F.map b := by
    change eqToHom _ = F.map (eqToHom _)
    rw [eqToHom_map]
  have hopen :
      ((a ≫ b) ≫ c) ≫ d =
          (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op := by
    apply Subsingleton.elim
  rw [hcast]
  simp only [rightFactorIsoChart, pairFactorIsoOverlap,
    infinityToOverlapBaseLinear, Functor.mapIso_inv, Functor.mapIso_hom]
  change F.map a ≫ F.map b ≫ F.map c ≫ F.map d = F.map _
  calc
    _ = (F.map a ≫ F.map b) ≫ (F.map c ≫ F.map d) :=
      (Category.assoc (F.map a) (F.map b) (F.map c ≫ F.map d)).symm
    _ = F.map (a ≫ b) ≫ (F.map c ≫ F.map d) :=
      congrArg (fun q ↦ q ≫ (F.map c ≫ F.map d)) (F.map_comp a b).symm
    _ = (F.map (a ≫ b) ≫ F.map c) ≫ F.map d :=
      (Category.assoc (F.map (a ≫ b)) (F.map c) (F.map d)).symm
    _ = F.map ((a ≫ b) ≫ c) ≫ F.map d :=
      congrArg (fun q ↦ q ≫ F.map d) (F.map_comp (a ≫ b) c).symm
    _ = F.map (((a ≫ b) ≫ c) ≫ d) := (F.map_comp ((a ≫ b) ≫ c) d).symm
    _ = _ := congrArg F.map hopen

private theorem standardCover_coface_comp_pairProjection
    (K : Type u) [Field K] (M : (scheme K).Modules) (k : Fin 2) :
    orderedBaseCechCoface (structureMap K) M (standardCover K) 0 k ≫
        Pi.π (fun j : OrderedCechIndex (TwoIndex K) 1 ↦
          baseCechFactor (structureMap K) M (standardCover K) 1 j.1)
          (pairIndex K) =
      Pi.π (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
        baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
          ((pairIndex K).delete k) ≫
        (baseModulePresheaf (structureMap K) M).map
          (((FormalCoproduct.mk _ (standardCover K)).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ
              (pairIndex K).1).op := by
  simpa only [Nat.zero_add] using
    orderedBaseCechCoface_comp_π (structureMap K) M
      (standardCover K) 0 k (pairIndex K)

private theorem standardCover_coface_comp_degreeOneToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) (k : Fin 2) :
    orderedBaseCechCoface (structureMap K) M (standardCover K) 0 k ≫
        degreeOneToOverlap K M =
      Pi.π (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
        baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
          ((pairIndex K).delete k) ≫
        (baseModulePresheaf (structureMap K) M).map
          (((FormalCoproduct.mk _ (standardCover K)).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ
              (pairIndex K).1).op ≫
        (pairFactorIsoOverlap K M).hom := by
  rw [degreeOneToOverlap_eq_projection]
  let c := orderedBaseCechCoface (structureMap K) M (standardCover K) 0 k
  let p := Pi.π (fun j : OrderedCechIndex (TwoIndex K) 1 ↦
    baseCechFactor (structureMap K) M (standardCover K) 1 j.1) (pairIndex K)
  let q := Pi.π (fun j : OrderedCechIndex (TwoIndex K) 0 ↦
    baseCechFactor (structureMap K) M (standardCover K) 0 j.1)
      ((pairIndex K).delete k)
  let r := (baseModulePresheaf (structureMap K) M).map
    (((FormalCoproduct.mk _ (standardCover K)).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ (pairIndex K).1).op
  let d := (pairFactorIsoOverlap K M).hom
  have hcp : c ≫ p = q ≫ r :=
    standardCover_coface_comp_pairProjection K M k
  change c ≫ p ≫ d = q ≫ r ≫ d
  exact Eq.trans (Category.assoc c p d).symm
    (Eq.trans ((reassoc_of% hcp) d) (Category.assoc q r d))

private theorem leftChart_coface_one_eq_standardToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    leftChartToDegreeZero K M ≫
        orderedBaseCechCoface (structureMap K) M (standardCover K) 0 1 ≫
        degreeOneToOverlap K M =
      standardToOverlapBaseLinear K M := by
  classical
  let F₀ := fun j : OrderedCechIndex (TwoIndex K) 0 ↦
    baseCechFactor (structureMap K) M (standardCover K) 0 j.1
  let l := (leftFactorIsoChart K M).inv
  let i := Pi.ι F₀ (leftIndex K)
  let c := orderedBaseCechCoface (structureMap K) M (standardCover K) 0 1
  let e := degreeOneToOverlap K M
  let q := Pi.π F₀ ((pairIndex K).delete 1)
  let r := (baseModulePresheaf (structureMap K) M).map
    (((FormalCoproduct.mk _ (standardCover K)).mapPower
      (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ (pairIndex K).1).op
  let d := (pairFactorIsoOverlap K M).hom
  let t := eqToHom (congrArg F₀ (pairIndex_delete_one K)).symm
  have hce : c ≫ e = q ≫ r ≫ d :=
    standardCover_coface_comp_degreeOneToOverlap K M 1
  have hiq : i ≫ q = t := by
    dsimp only [i, q, t]
    rw [Pi.ι_π, dif_pos (pairIndex_delete_one K).symm]
  have hiq_tail : i ≫ (q ≫ r ≫ d) = t ≫ r ≫ d := by
    calc
      _ = (i ≫ q) ≫ (r ≫ d) := (Category.assoc i q (r ≫ d)).symm
      _ = t ≫ (r ≫ d) := congrArg (fun z ↦ z ≫ (r ≫ d)) hiq
      _ = _ := rfl
  change (l ≫ i) ≫ c ≫ e = standardToOverlapBaseLinear K M
  calc
    _ = (l ≫ i) ≫ (q ≫ r ≫ d) :=
      congrArg (fun z ↦ (l ≫ i) ≫ z) hce
    _ = l ≫ (i ≫ (q ≫ r ≫ d)) := Category.assoc l i (q ≫ r ≫ d)
    _ = l ≫ (t ≫ r ≫ d) := congrArg (fun z ↦ l ≫ z) hiq_tail
    _ = _ := leftFactorRestriction_eq_standardToOverlap K M

private theorem rightChart_coface_zero_eq_infinityToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    rightChartToDegreeZero K M ≫
        orderedBaseCechCoface (structureMap K) M (standardCover K) 0 0 ≫
        degreeOneToOverlap K M =
      infinityToOverlapBaseLinear K M := by
  classical
  let F₀ := fun j : OrderedCechIndex (TwoIndex K) 0 ↦
    baseCechFactor (structureMap K) M (standardCover K) 0 j.1
  let l := (rightFactorIsoChart K M).inv
  let i := Pi.ι F₀ (rightIndex K)
  let c := orderedBaseCechCoface (structureMap K) M (standardCover K) 0 0
  let e := degreeOneToOverlap K M
  let q := Pi.π F₀ ((pairIndex K).delete 0)
  let r := (baseModulePresheaf (structureMap K) M).map
    (((FormalCoproduct.mk _ (standardCover K)).mapPower
      (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ (pairIndex K).1).op
  let d := (pairFactorIsoOverlap K M).hom
  let t := eqToHom (congrArg F₀ (pairIndex_delete_zero K)).symm
  have hce : c ≫ e = q ≫ r ≫ d :=
    standardCover_coface_comp_degreeOneToOverlap K M 0
  have hiq : i ≫ q = t := by
    dsimp only [i, q, t]
    rw [Pi.ι_π, dif_pos (pairIndex_delete_zero K).symm]
  have hiq_tail : i ≫ (q ≫ r ≫ d) = t ≫ r ≫ d := by
    calc
      _ = (i ≫ q) ≫ (r ≫ d) := (Category.assoc i q (r ≫ d)).symm
      _ = t ≫ (r ≫ d) := congrArg (fun z ↦ z ≫ (r ≫ d)) hiq
      _ = _ := rfl
  change (l ≫ i) ≫ c ≫ e = infinityToOverlapBaseLinear K M
  calc
    _ = (l ≫ i) ≫ (q ≫ r ≫ d) :=
      congrArg (fun z ↦ (l ≫ i) ≫ z) hce
    _ = l ≫ (i ≫ (q ≫ r ≫ d)) := Category.assoc l i (q ≫ r ≫ d)
    _ = l ≫ (t ≫ r ≫ d) := congrArg (fun z ↦ l ≫ z) hiq_tail
    _ = _ := rightFactorRestriction_eq_infinityToOverlap K M

private theorem leftChart_coface_zero_eq_zero
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    leftChartToDegreeZero K M ≫
        orderedBaseCechCoface (structureMap K) M (standardCover K) 0 0 ≫
        degreeOneToOverlap K M = 0 := by
  classical
  let F₀ := fun j : OrderedCechIndex (TwoIndex K) 0 ↦
    baseCechFactor (structureMap K) M (standardCover K) 0 j.1
  let l := (leftFactorIsoChart K M).inv
  let i := Pi.ι F₀ (leftIndex K)
  let c := orderedBaseCechCoface (structureMap K) M (standardCover K) 0 0
  let e := degreeOneToOverlap K M
  let q := Pi.π F₀ ((pairIndex K).delete 0)
  let r := (baseModulePresheaf (structureMap K) M).map
    (((FormalCoproduct.mk _ (standardCover K)).mapPower
      (SimplexCategory.δ (0 : Fin 2)).toOrderHom.toFun).φ (pairIndex K).1).op
  let d := (pairFactorIsoOverlap K M).hom
  have hce : c ≫ e = q ≫ r ≫ d :=
    standardCover_coface_comp_degreeOneToOverlap K M 0
  have hne : leftIndex K ≠ (pairIndex K).delete 0 := by
    rw [pairIndex_delete_zero]
    exact leftIndex_ne_rightIndex K
  have hiq : i ≫ q = 0 := by
    dsimp only [i, q]
    rw [Pi.ι_π, dif_neg hne]
  have hiq_tail : i ≫ (q ≫ r ≫ d) = 0 := by
    calc
      _ = (i ≫ q) ≫ (r ≫ d) := (Category.assoc i q (r ≫ d)).symm
      _ = 0 ≫ (r ≫ d) := congrArg (fun z ↦ z ≫ (r ≫ d)) hiq
      _ = 0 := zero_comp
  change (l ≫ i) ≫ c ≫ e = 0
  calc
    _ = (l ≫ i) ≫ (q ≫ r ≫ d) :=
      congrArg (fun z ↦ (l ≫ i) ≫ z) hce
    _ = l ≫ (i ≫ (q ≫ r ≫ d)) := Category.assoc l i (q ≫ r ≫ d)
    _ = l ≫ 0 := congrArg (fun z ↦ l ≫ z) hiq_tail
    _ = 0 := comp_zero

private theorem rightChart_coface_one_eq_zero
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    rightChartToDegreeZero K M ≫
        orderedBaseCechCoface (structureMap K) M (standardCover K) 0 1 ≫
        degreeOneToOverlap K M = 0 := by
  classical
  let F₀ := fun j : OrderedCechIndex (TwoIndex K) 0 ↦
    baseCechFactor (structureMap K) M (standardCover K) 0 j.1
  let l := (rightFactorIsoChart K M).inv
  let i := Pi.ι F₀ (rightIndex K)
  let c := orderedBaseCechCoface (structureMap K) M (standardCover K) 0 1
  let e := degreeOneToOverlap K M
  let q := Pi.π F₀ ((pairIndex K).delete 1)
  let r := (baseModulePresheaf (structureMap K) M).map
    (((FormalCoproduct.mk _ (standardCover K)).mapPower
      (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).φ (pairIndex K).1).op
  let d := (pairFactorIsoOverlap K M).hom
  have hce : c ≫ e = q ≫ r ≫ d :=
    standardCover_coface_comp_degreeOneToOverlap K M 1
  have hne : rightIndex K ≠ (pairIndex K).delete 1 := by
    rw [pairIndex_delete_one]
    exact (leftIndex_ne_rightIndex K).symm
  have hiq : i ≫ q = 0 := by
    dsimp only [i, q]
    rw [Pi.ι_π, dif_neg hne]
  have hiq_tail : i ≫ (q ≫ r ≫ d) = 0 := by
    calc
      _ = (i ≫ q) ≫ (r ≫ d) := (Category.assoc i q (r ≫ d)).symm
      _ = 0 ≫ (r ≫ d) := congrArg (fun z ↦ z ≫ (r ≫ d)) hiq
      _ = 0 := zero_comp
  change (l ≫ i) ≫ c ≫ e = 0
  calc
    _ = (l ≫ i) ≫ (q ≫ r ≫ d) :=
      congrArg (fun z ↦ (l ≫ i) ≫ z) hce
    _ = l ≫ (i ≫ (q ≫ r ≫ d)) := Category.assoc l i (q ≫ r ≫ d)
    _ = l ≫ 0 := congrArg (fun z ↦ l ≫ z) hiq_tail
    _ = 0 := comp_zero

private theorem leftChart_differential_eq_neg_standardToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    leftChartToDegreeZero K M ≫
        (orderedBaseCechComplex (structureMap K) M (standardCover K)).d 0 1 ≫
        degreeOneToOverlap K M =
      -standardToOverlapBaseLinear K M := by
  rw [orderedBaseCechComplex_d]
  change leftChartToDegreeZero K M ≫
      orderedBaseCechDifferential (structureMap K) M (standardCover K) 0 ≫
      degreeOneToOverlap K M = -standardToOverlapBaseLinear K M
  rw [orderedBaseCechDifferential, Fin.sum_univ_two]
  simp only [
    Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, Preadditive.comp_add, Preadditive.add_comp,
    ]
  rw [leftChart_coface_zero_eq_zero]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp]
  rw [leftChart_coface_one_eq_standardToOverlap]
  simp

private theorem rightChart_differential_eq_infinityToOverlap
    (K : Type u) [Field K] (M : (scheme K).Modules) :
    rightChartToDegreeZero K M ≫
        (orderedBaseCechComplex (structureMap K) M (standardCover K)).d 0 1 ≫
        degreeOneToOverlap K M =
      infinityToOverlapBaseLinear K M := by
  rw [orderedBaseCechComplex_d]
  change rightChartToDegreeZero K M ≫
      orderedBaseCechDifferential (structureMap K) M (standardCover K) 0 ≫
      degreeOneToOverlap K M = infinityToOverlapBaseLinear K M
  rw [orderedBaseCechDifferential, Fin.sum_univ_two]
  simp only [
    Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, Preadditive.comp_add, Preadditive.add_comp,
    ]
  rw [rightChart_coface_zero_eq_infinityToOverlap]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp]
  rw [rightChart_coface_one_eq_zero]
  simp

private theorem finite_principalParts
    {K : Type u} {A : Type v} {B : Type w}
    {M₀ : Type*} {Minf : Type*} {P : Type*}
    [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    [AddCommGroup M₀] [AddCommGroup Minf] [AddCommGroup P]
    [Module K M₀] [Module K Minf] [Module K P]
    [Module A M₀] [Module A P] [Module B Minf] [Module B P]
    [IsScalarTower K A M₀] [IsScalarTower K A P]
    [IsScalarTower K B Minf] [IsScalarTower K B P]
    (t : A) (s : B)
    (r₀ : M₀ →ₗ[A] P) (rinf : Minf →ₗ[B] P)
    [Module.Finite A M₀]
    [IsLocalizedModule.Away t r₀]
    [IsLocalizedModule.Away s rinf]
    (hpoly : Function.Surjective
      (Polynomial.eval₂RingHom (algebraMap K A) t))
    (hinv : ∀ p : P, s • (t • p) = p) :
    Module.Finite K
      (P ⧸ ((r₀.restrictScalars K).range ⊔
        (rinf.restrictScalars K).range)) := by
  classical
  let D : Submodule K P :=
    (r₀.restrictScalars K).range ⊔ (rinf.restrictScalars K).range
  let q : P →ₗ[K] P ⧸ D := D.mkQ
  have hinvPow : ∀ (n : ℕ) (p : P), s ^ n • (t ^ n • p) = p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro p
        rw [pow_succ', pow_succ, mul_smul, mul_smul, ih (t • p), hinv]
  obtain ⟨G, hGfinite, hGspan⟩ := Submodule.fg_def.mp
    (Module.Finite.fg_top (R := A) (M := M₀))
  have hcut : ∀ g : M₀, ∃ n : ℕ, ∃ m : Minf,
      s ^ n • r₀ g = rinf m := by
    intro g
    obtain ⟨x, hx⟩ := IsLocalizedModule.surj (Submonoid.powers s) rinf (r₀ g)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (x.2 : B) s).mp x.2.property
    refine ⟨n, x.1, ?_⟩
    rw [hn]
    simpa only [Submonoid.smul_def] using hx
  choose cut lift hcut using hcut
  let generators : Finset (P ⧸ D) :=
    hGfinite.toFinset.biUnion fun g ↦
      (Finset.range (cut g)).image fun j ↦ q (s ^ j • r₀ g)
  have hgenerator (g : M₀) (hg : g ∈ G) (j : ℕ) (hj : j < cut g) :
      q (s ^ j • r₀ g) ∈ Submodule.span K (↑generators : Set (P ⧸ D)) := by
    apply Submodule.subset_span
    simp only [generators, Finset.mem_coe, Finset.mem_biUnion, Set.Finite.mem_toFinset,
      Finset.mem_image, Finset.mem_range]
    exact ⟨g, hg, j, hj, rfl⟩
  have hq_r₀ (m : M₀) : q (r₀ m) = 0 := by
    change D.mkQ (r₀ m) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_left ((r₀.restrictScalars K).mem_range_self m)
  have hq_rinf (m : Minf) : q (rinf m) = 0 := by
    change D.mkQ (rinf m) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right ((rinf.restrictScalars K).mem_range_self m)
  have hlarge (g : M₀) (k : ℕ) (hk : cut g ≤ k) :
      q (s ^ k • r₀ g) = 0 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, pow_add, mul_smul, hcut, ← rinf.map_smul, hq_rinf]
  let W : Submodule K (P ⧸ D) :=
    Submodule.span K (↑generators : Set (P ⧸ D))
  have hgenerator_all (g : M₀) (hg : g ∈ G) (k : ℕ) :
      q (s ^ k • r₀ g) ∈ W := by
    by_cases hk : k < cut g
    · exact hgenerator g hg k hk
    · rw [hlarge g k (Nat.le_of_not_gt hk)]
      exact W.zero_mem
  have hmonomial (m : M₀)
      (hm : ∀ k : ℕ, q (s ^ k • r₀ m) ∈ W)
      (k n : ℕ) (c : K) :
      q (s ^ k • r₀ ((Polynomial.eval₂RingHom
        (algebraMap K A) t) (Polynomial.monomial n c) • m)) ∈ W := by
    rw [r₀.map_smul]
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
    rw [mul_smul,
      IsScalarTower.algebraMap_smul A c (t ^ n • r₀ m),
      SMulCommClass.smul_comm (s ^ k) c (t ^ n • r₀ m), q.map_smul]
    by_cases hnk : n ≤ k
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
      rw [add_comm n d, pow_add, mul_smul, hinvPow]
      exact W.smul_mem c (hm d)
    · have hkn : k ≤ n := Nat.le_of_not_ge hnk
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
      rw [pow_add, mul_smul, hinvPow, ← r₀.map_smul, hq_r₀, smul_zero]
      exact W.zero_mem
  have hpoly_smul (m : M₀)
      (hm : ∀ k : ℕ, q (s ^ k • r₀ m) ∈ W)
      (a : A) (k : ℕ) : q (s ^ k • r₀ (a • m)) ∈ W := by
    obtain ⟨p, rfl⟩ := hpoly a
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' =>
        simpa only [map_add, add_smul, smul_add] using W.add_mem hp hp'
    | monomial n c => exact hmonomial m hm k n c
  have hspan : ∀ m : M₀, m ∈ Submodule.span A G →
      ∀ k : ℕ, q (s ^ k • r₀ m) ∈ W := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm => exact hgenerator_all m hm
    | zero => simp only [map_zero, smul_zero, map_zero]; exact fun _ ↦ W.zero_mem
    | add x y _ _ hx hy =>
        intro k
        simp only [map_add, smul_add, map_add]
        exact W.add_mem (hx k) (hy k)
    | smul a x _ hx => exact hpoly_smul x hx a
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨↑generators, generators.finite_toSet, ?_⟩
  apply top_unique
  intro z _
  obtain ⟨p, rfl⟩ := D.mkQ_surjective z
  obtain ⟨x, hx⟩ := IsLocalizedModule.surj (Submonoid.powers t) r₀ p
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (x.2 : A) t).mp x.2.property
  have hp : p = s ^ k • r₀ x.1 := by
    calc
      p = s ^ k • (t ^ k • p) := (hinvPow k p).symm
      _ = s ^ k • r₀ x.1 := by
        rw [hk]
        simpa only [Submonoid.smul_def] using congrArg (s ^ k • ·) hx
  rw [hp]
  have hxspan : x.1 ∈ Submodule.span A G := by
    rw [hGspan]
    exact Submodule.mem_top
  exact hspan x.1 hxspan k

private lemma infinityAffineOpen_le_structureMap_preimage_top
    (K : Type u) [Field K] :
    infinityAffineOpen K ≤ structureMap K ⁻¹ᵁ
      (⊤ : (Spec (.of K)).Opens) := by
  simp

private lemma affineOverlapOpen_le_structureMap_preimage_top
    (K : Type u) [Field K] :
    affineOverlapOpen K ≤ structureMap K ⁻¹ᵁ
      (⊤ : (Spec (.of K)).Opens) := by
  simp

private theorem isLocalizedModuleAway_of_basicOpen_eq
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) {V : X.Opens}
    (hV : X.basicOpen f = V) (hVU : V ≤ U.1) :
    letI : Algebra Γ(X, U.1) Γ(X, V) :=
      ((X.presheaf.map (homOfLE hVU).op).hom).toAlgebra
    letI : Module Γ(X, U.1) Γ(M, V) :=
      Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, V))
    IsLocalizedModule.Away f
      ({ toFun := M.presheaf.map (homOfLE hVU).op
         map_add' := fun x y ↦ map_add _ x y
         map_smul' := fun r x ↦ M.map_smul (homOfLE hVU) r x } :
        Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, V)) := by
  subst V
  simpa only using
    (isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen
      M U f)

private theorem standardCover_principalParts_finite
    (K : Type u) [Field K] (M : (scheme K).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      ((baseModulePresheaf (structureMap K) M).obj
          (op (affineOverlapOpen K)) ⧸
        ((standardToOverlapBaseLinear K M).hom.range ⊔
          (infinityToOverlapBaseLinear K M).hom.range)) := by
  let R := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  let A := Γ(scheme K, standardAffineOpen K)
  let B := Γ(scheme K, infinityAffineOpen K)
  let C := Γ(scheme K, affineOverlapOpen K)
  let M₀ := Γ(M, standardAffineOpen K)
  let Minf := Γ(M, infinityAffineOpen K)
  let P := Γ(M, affineOverlapOpen K)
  letI : Field R :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  letI : Algebra R A :=
    ((structureMap K).appLE ⊤ (standardAffineOpen K)
      (standardAffineOpen_le_structureMap_preimage_top K)).hom.toAlgebra
  letI : Algebra R B :=
    ((structureMap K).appLE ⊤ (infinityAffineOpen K)
      (infinityAffineOpen_le_structureMap_preimage_top K)).hom.toAlgebra
  letI : Algebra R C :=
    ((structureMap K).appLE ⊤ (affineOverlapOpen K)
      (affineOverlapOpen_le_structureMap_preimage_top K)).hom.toAlgebra
  letI : Module R M₀ := ModuleCat.isModule
    ((baseModulePresheaf (structureMap K) M).obj (op (standardAffineOpen K)))
  letI : Module R Minf := ModuleCat.isModule
    ((baseModulePresheaf (structureMap K) M).obj (op (infinityAffineOpen K)))
  letI : Module R P := ModuleCat.isModule
    ((baseModulePresheaf (structureMap K) M).obj (op (affineOverlapOpen K)))
  let res₀Ring := (scheme K).presheaf.map
    (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op
  let resinfRing := (scheme K).presheaf.map
    (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op
  letI : Algebra A C := res₀Ring.hom.toAlgebra
  letI : Algebra B C := resinfRing.hom.toAlgebra
  letI : Module A P := Module.compHom P (algebraMap A C)
  letI : Module B P := Module.compHom P (algebraMap B C)
  letI : IsScalarTower R A M₀ :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R B Minf :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R A P :=
    IsScalarTower.of_algebraMap_smul fun r p ↦ by
      change res₀Ring ((structureMap K).appLE ⊤ (standardAffineOpen K)
          (standardAffineOpen_le_structureMap_preimage_top K) r) • p =
        (structureMap K).appLE ⊤ (affineOverlapOpen K)
          (affineOverlapOpen_le_structureMap_preimage_top K) r • p
      congr 1
  letI : IsScalarTower R B P :=
    IsScalarTower.of_algebraMap_smul fun r p ↦ by
      change resinfRing ((structureMap K).appLE ⊤ (infinityAffineOpen K)
          (infinityAffineOpen_le_structureMap_preimage_top K) r) • p =
        (structureMap K).appLE ⊤ (affineOverlapOpen K)
          (affineOverlapOpen_le_structureMap_preimage_top K) r • p
      congr 1
  let r₀ : M₀ →ₗ[A] P :=
    { toFun := M.presheaf.map
        (homOfLE (affineOverlapOpen_le_standardAffineOpen K)).op
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := fun r x ↦
        M.map_smul (homOfLE (affineOverlapOpen_le_standardAffineOpen K)) r x }
  let rinf : Minf →ₗ[B] P :=
    { toFun := M.presheaf.map
        (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)).op
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := fun r x ↦
        M.map_smul (homOfLE (affineOverlapOpen_le_infinityAffineOpen K)) r x }
  letI : Module.Finite A M₀ :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M
      ⟨standardAffineOpen K, isAffineOpen_standardAffineOpen K⟩
  have hloc₀ : IsLocalizedModule.Away (affineCoordinate K) r₀ := by
    simpa only [r₀, A, M₀, P, res₀Ring] using
      (isLocalizedModuleAway_of_basicOpen_eq M
        ⟨standardAffineOpen K, isAffineOpen_standardAffineOpen K⟩
        (affineCoordinate K)
        (basicOpen_affineCoordinate_eq_affineOverlapOpen K)
        (affineOverlapOpen_le_standardAffineOpen K))
  letI : IsLocalizedModule.Away (affineCoordinate K) r₀ := hloc₀
  have hlocinf : IsLocalizedModule.Away (inverseAffineCoordinate K) rinf := by
    simpa only [rinf, B, Minf, P, resinfRing] using
      (isLocalizedModuleAway_of_basicOpen_eq M
        ⟨infinityAffineOpen K, isAffineOpen_infinityAffineOpen K⟩
        (inverseAffineCoordinate K)
        (basicOpen_inverseAffineCoordinate_eq_affineOverlapOpen K)
        (affineOverlapOpen_le_infinityAffineOpen K))
  letI : IsLocalizedModule.Away (inverseAffineCoordinate K) rinf := hlocinf
  have hinv : ∀ p : P,
      inverseAffineCoordinate K • (affineCoordinate K • p) = p := by
    intro p
    change resinfRing (inverseAffineCoordinate K) •
        (res₀Ring (affineCoordinate K) • p) = p
    rw [← mul_smul, inverseAffineCoordinate_mul_affineCoordinate_on_overlap,
      one_smul]
  have hfinite := finite_principalParts
    (K := R) (A := A) (B := B) (M₀ := M₀) (Minf := Minf) (P := P)
    (affineCoordinate K) (inverseAffineCoordinate K) r₀ rinf
    (standard_eval₂_surjective K) hinv
  change Module.Finite R
    (P ⧸ ((standardToOverlapBaseLinear K M).hom.range ⊔
      (infinityToOverlapBaseLinear K M).hom.range))
  have hr₀ : (standardToOverlapBaseLinear K M).hom =
      r₀.restrictScalars R := by
    ext x
    rfl
  have hrinf : (infinityToOverlapBaseLinear K M).hom =
      rinf.restrictScalars R := by
    ext x
    rfl
  rw [hr₀, hrinf]
  exact hfinite

private theorem standardCover_coker_d_zero_one_finite
    (K : Type u) [Field K] (M : (scheme K).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (((orderedBaseCechComplex (structureMap K) M (standardCover K)).X 1) ⧸
        ((orderedBaseCechComplex (structureMap K) M
          (standardCover K)).d 0 1).hom.range) := by
  let R := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  let C := orderedBaseCechComplex (structureMap K) M (standardCover K)
  let P := (baseModulePresheaf (structureMap K) M).obj
    (op (affineOverlapOpen K))
  let e := orderedDegreeOneOverlapLinearEquiv K M
  let D : Submodule R P :=
    (standardToOverlapBaseLinear K M).hom.range ⊔
      (infinityToOverlapBaseLinear K M).hom.range
  let Dd : Submodule R P := (C.d 0 1).hom.range.map e.toLinearMap
  have hstandard :
      (standardToOverlapBaseLinear K M).hom.range ≤ Dd := by
    rintro y ⟨x, rfl⟩
    have hx := ConcreteCategory.congr_hom
      (leftChart_differential_eq_neg_standardToOverlap K M) x
    change e.toLinearMap
        ((C.d 0 1).hom ((leftChartToDegreeZero K M).hom x)) =
      -((standardToOverlapBaseLinear K M).hom x) at hx
    have hneg : -((standardToOverlapBaseLinear K M).hom x) ∈ Dd := by
      exact ⟨(C.d 0 1).hom ((leftChartToDegreeZero K M).hom x),
        ⟨(leftChartToDegreeZero K M).hom x, rfl⟩, hx⟩
    simpa only [neg_neg] using Dd.neg_mem hneg
  have hinfinity :
      (infinityToOverlapBaseLinear K M).hom.range ≤ Dd := by
    rintro y ⟨x, rfl⟩
    refine ⟨(C.d 0 1).hom ((rightChartToDegreeZero K M).hom x),
      ⟨(rightChartToDegreeZero K M).hom x, rfl⟩, ?_⟩
    have hx := ConcreteCategory.congr_hom
      (rightChart_differential_eq_infinityToOverlap K M) x
    change e.toLinearMap
        ((C.d 0 1).hom ((rightChartToDegreeZero K M).hom x)) =
      (infinityToOverlapBaseLinear K M).hom x at hx
    exact hx
  have hD : D ≤ Dd := sup_le hstandard hinfinity
  letI : Module.Finite R (P ⧸ D) := by
    dsimp only [R, P, D]
    exact standardCover_principalParts_finite K M
  let qDD : (P ⧸ D) →ₗ[R] (P ⧸ Dd) :=
    Submodule.mapQ D Dd LinearMap.id (by simpa using hD)
  have hqDD : Function.Surjective qDD := by
    intro y
    induction y using Quotient.inductionOn' with
    | _ x =>
        refine ⟨Submodule.Quotient.mk x, ?_⟩
        rfl
  letI : Module.Finite R (P ⧸ Dd) :=
    Module.Finite.of_surjective qDD hqDD
  let qEquiv :
      ((C.X 1) ⧸ (C.d 0 1).hom.range) ≃ₗ[R] (P ⧸ Dd) :=
    Submodule.Quotient.equiv (C.d 0 1).hom.range Dd e rfl
  exact Module.Finite.equiv qEquiv.symm

private theorem homology_one_finite_of_coker_finite
    {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hd : C.d 1 2 = 0)
    [Module.Finite R ((C.X 1) ⧸ (C.d 0 1).hom.range)] :
    Module.Finite R (C.homology 1) := by
  have hnext : (ComplexShape.up ℕ).next 1 = 2 :=
    (ComplexShape.up ℕ).next_eq' (by simp)
  let l : C.X 1 ⟶ C.cycles 1 :=
    C.liftCycles (𝟙 _) 2 hnext (by simpa using hd)
  have hl : C.iCycles 1 ≫ l = 𝟙 _ := by
    apply (cancel_mono (C.iCycles 1)).mp
    dsimp only [l]
    rw [Category.assoc, C.liftCycles_i]
    simp
  let z : C.X 1 ⟶ C.homology 1 := l ≫ C.homologyπ 1
  have hiz : C.iCycles 1 ≫ z = C.homologyπ 1 := by
    dsimp only [z]
    rw [← Category.assoc, hl, Category.id_comp]
  have hz : Function.Surjective z.hom := by
    intro y
    obtain ⟨x, rfl⟩ :=
      (ModuleCat.epi_iff_surjective (C.homologyπ 1)).mp inferInstance y
    refine ⟨(C.iCycles 1).hom x, ?_⟩
    change ((C.iCycles 1 ≫ z).hom) x = (C.homologyπ 1).hom x
    rw [hiz]
  have hdz : C.d 0 1 ≫ z = 0 := by
    dsimp only [z, l]
    rw [← Category.assoc, C.comp_liftCycles]
    exact C.liftCycles_homologyπ_eq_zero_of_boundary
      (C.d 0 1) 2 hnext (𝟙 _) (by simp)
  have hrange : (C.d 0 1).hom.range ≤ z.hom.ker := by
    rw [LinearMap.range_le_ker_iff]
    ext x
    exact ConcreteCategory.congr_hom hdz x
  let zQ : ((C.X 1) ⧸ (C.d 0 1).hom.range) →ₗ[R] C.homology 1 :=
    Submodule.liftQ (C.d 0 1).hom.range z.hom hrange
  apply Module.Finite.of_surjective zQ
  intro y
  obtain ⟨x, rfl⟩ := hz y
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  dsimp only [zQ]
  rw [Submodule.liftQ_apply]

private theorem standardCover_isOpenCover
    (K : Type u) [Field K] : IsOpenCover (standardCover K) := by
  rw [IsOpenCover]
  apply le_antisymm le_top
  rw [← standardAffineOpen_sup_infinityAffineOpen_eq_top K]
  apply sup_le
  · exact le_iSup (standardCover K) ⟨(0 : Fin 2)⟩
  · exact le_iSup (standardCover K) ⟨(1 : Fin 2)⟩

private theorem standardCover_isAffineOpen
    (K : Type u) [Field K] (i : TwoIndex K) :
    IsAffineOpen (standardCover K i) := by
  rcases i with ⟨i⟩
  fin_cases i
  · exact isAffineOpen_standardAffineOpen K
  · exact isAffineOpen_infinityAffineOpen K

private theorem standardCover_ordered_homology_one_finite
    (K : Type u) [Field K] (M : (scheme K).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      ((orderedBaseCechComplex (structureMap K) M
        (standardCover K)).homology 1) := by
  let C := orderedBaseCechComplex (structureMap K) M (standardCover K)
  letI : Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      ((C.X 1) ⧸ (C.d 0 1).hom.range) :=
    standardCover_coker_d_zero_one_finite K M
  exact homology_one_finite_of_coker_finite C
    (orderedBaseCechComplex_d_one_two_standardCover_zero K M)

/-- The global-functions action on genuine `H¹` of a module on `P¹`,
transported through the two-standard-affine-cover comparison. -/
@[instance_reducible]
noncomputable def genuineSheafHOneBaseModule
    (K : Type u) [Field K] (M : (scheme K).Modules)
    [M.IsQuasicoherent] :
    Module Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (GenuineSheafHOne M) :=
  genuineSheafHOneBaseModule_of_affineOpenCover
    (structureMap K) M (standardCover K)
    (standardCover_isOpenCover K) (standardCover_isAffineOpen K)

/-- A finite-type quasicoherent module on `P¹` over a field has finite
genuine sheaf cohomology in degree one.  The module structure is the one
transported through the checked two-standard-affine-cover comparison. -/
theorem genuineSheafHOne_finite
    (K : Type u) [Field K] (M : (scheme K).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := genuineSheafHOneBaseModule K M
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (GenuineSheafHOne M) := by
  exact
    genuineSheafHOne_finite_of_ordered_affineOpenCover
      (structureMap K) M (standardCover K)
      (standardCover_isOpenCover K) (standardCover_isAffineOpen K)
      (standardCover_ordered_homology_one_finite K M)

private theorem preimage_standardCover_isOpenCover
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) :
    IsOpenCover (fun i ↦ f ⁻¹ᵁ standardCover K i) := by
  exact (standardCover_isOpenCover K).comap f.base.hom

private theorem preimage_standardCover_isAffineOpen
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) [IsAffineHom f] (i : TwoIndex K) :
    IsAffineOpen (f ⁻¹ᵁ standardCover K i) :=
  (standardCover_isAffineOpen K i).preimage f

private theorem ordered_homology_one_finite_of_finite_to_projectiveLine
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) [IsFinite f] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      ((orderedBaseCechComplex (f ≫ structureMap K) M
        (fun i ↦ f ⁻¹ᵁ standardCover K i)).homology 1) := by
  let N := (pushforward f).obj M
  letI : N.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom f
  letI : N.IsFiniteType := isFiniteType_pushforward_of_isFinite f
  letI : Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      ((orderedBaseCechComplex (structureMap K) N
        (standardCover K)).homology 1) :=
    standardCover_ordered_homology_one_finite K N
  let e := HomologicalComplex.homologyMapIso
    (orderedBaseCechComplexPushforwardIso f (structureMap K) M
      (standardCover K)) 1
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- The base-field action on genuine `H¹` for a module on a scheme finite
over `P¹`, transported through the inverse images of the two standard
affine charts. -/
@[instance_reducible]
noncomputable def genuineSheafHOneBaseModuleOfFiniteToProjectiveLine
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) [IsFinite f] (M : X.Modules)
    [M.IsQuasicoherent] :
    Module Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (GenuineSheafHOne M) :=
  genuineSheafHOneBaseModule_of_affineOpenCover
    (f ≫ structureMap K) M (fun i ↦ f ⁻¹ᵁ standardCover K i)
    (preimage_standardCover_isOpenCover K f)
    (preimage_standardCover_isAffineOpen K f)

/-- Degree-one genuine sheaf cohomology is finite for every coherent module
on a scheme finite over `P¹`.  This is the finite-morphism consumer of the
two-chart principal-parts calculation above. -/
theorem genuineSheafHOne_finite_of_finite_to_projectiveLine
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) [IsFinite f] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := genuineSheafHOneBaseModuleOfFiniteToProjectiveLine K f M
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (GenuineSheafHOne M) := by
  exact genuineSheafHOne_finite_of_ordered_affineOpenCover
    (f ≫ structureMap K) M (fun i ↦ f ⁻¹ᵁ standardCover K i)
    (preimage_standardCover_isOpenCover K f)
    (preimage_standardCover_isAffineOpen K f)
    (ordered_homology_one_finite_of_finite_to_projectiveLine K f M)

/-- Degree-one genuine sheaf cohomology is finite for the canonical action of
base global functions induced by a finite morphism to `P¹`. -/
theorem genuineSheafHOne_finite_canonical_of_finite_to_projectiveLine
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) [IsFinite f] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := baseSectionsHOneModule (f ≫ structureMap K) M
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (H M 1) := by
  let U := fun i ↦ f ⁻¹ᵁ standardCover K i
  letI : Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      ((baseCechComplex (f ≫ structureMap K) M U).homology 1) :=
    nativeBaseCechHOne_finite_of_ordered
      (f ≫ structureMap K) M U
      (ordered_homology_one_finite_of_finite_to_projectiveLine K f M)
  letI := baseSectionsHOneModule (f ≫ structureMap K) M
  exact Module.Finite.equiv
    (nativeBaseCechHOneLinearEquivCanonical_of_affineOpenCover
      (f ≫ structureMap K) M U
      (preimage_standardCover_isOpenCover K f)
      (preimage_standardCover_isAffineOpen K f))

/-- The ground-field action on genuine `H¹` for a module on a scheme finite
over `P¹`.  It is the restriction of the explicit global-functions action
along the canonical map from the field to the global functions of its
spectrum. -/
@[instance_reducible]
noncomputable def genuineSheafHOneFieldModuleOfFiniteToProjectiveLine
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) [IsFinite f] (M : X.Modules)
    [M.IsQuasicoherent] :
    Module K (GenuineSheafHOne M) := by
  letI := genuineSheafHOneBaseModuleOfFiniteToProjectiveLine K f M
  exact Module.compHom (GenuineSheafHOne M)
    (Scheme.ΓSpecIso (.of K)).inv.hom

/-- Genuine degree-one sheaf cohomology of a coherent module on a scheme
finite over `P¹` is finite-dimensional over the ground field.  The finite
map is an explicit hypothesis; this theorem does not assert that an arbitrary
proper curve has already been equipped with one. -/
theorem genuineSheafHOne_finiteDimensional_of_finite_to_projectiveLine
    {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ scheme K) [IsFinite f] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := genuineSheafHOneFieldModuleOfFiniteToProjectiveLine K f M
    FiniteDimensional K (GenuineSheafHOne M) := by
  let R := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  letI : Algebra K R := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : Module R (GenuineSheafHOne M) :=
    genuineSheafHOneBaseModuleOfFiniteToProjectiveLine K f M
  letI : Module K (GenuineSheafHOne M) :=
    genuineSheafHOneFieldModuleOfFiniteToProjectiveLine K f M
  letI : IsScalarTower K R (GenuineSheafHOne M) :=
    IsScalarTower.of_compHom K R (GenuineSheafHOne M)
  have hR : RingHom.Finite (algebraMap K R) := by
    change RingHom.Finite (Scheme.ΓSpecIso (.of K)).inv.hom
    exact
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.finite
  letI : Module.Finite K R := RingHom.finite_algebraMap.mp hR
  letI : Module.Finite R (GenuineSheafHOne M) :=
    genuineSheafHOne_finite_of_finite_to_projectiveLine K f M
  exact Module.Finite.trans R (GenuineSheafHOne M)

end MazurTorsion.AlgebraicGeometry.ProjectiveLineCohomology
