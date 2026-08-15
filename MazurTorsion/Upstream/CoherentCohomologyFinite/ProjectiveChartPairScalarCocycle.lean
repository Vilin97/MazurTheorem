/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartPairDefectVanishing

/-!
# Scalar cocycles on pairwise projective-chart overlaps

This file compares arbitrary affine-chart scalars with their homogeneous
localizations on a pairwise standard-chart intersection.  It then proves
the pairwise coordinate-ratio cocycle used to turn annihilated defects
into genuinely compatible corrected chart sections.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open HomogeneousLocalization
open SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

private theorem eq_trans_three
    {A : Sort*} {a b c e : A}
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = e) : a = e :=
  h₁.trans (h₂.trans h₃)

/-- An element of the `j`-th chart ring, localized at `Xₗ/Xⱼ` and
written in the homogeneous localization whose denominator is `XₗXⱼ`. -/
def chartPairAwayOfElement
    (l j : Fin (d + 1)) (r : chartRing k d j) :
    Away (homogeneousGrading k d)
      (coordinate k l * coordinate k j) :=
  chartProductSwap k d l j
    (awayMap (homogeneousGrading k d)
      (coordinate_mem_degreeOne k l)
      (rfl :
        coordinate k j * coordinate k l =
          coordinate k j * coordinate k l)
      r)

/-- The explicit spectrum model of `D(Xₗ/Xⱼ)` sends the homogeneous
localization of an arbitrary chart element to its ordinary restriction. -/
theorem chartRatioOpenToProductIso_appTop_element
    (l j : Fin (d + 1)) (r : chartRing k d j) :
    (chartRatioOpenToProductIso k d l j).hom.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k l * coordinate k j))).inv
            (chartPairAwayOfElement k d l j r)) =
      (show (Spec (chartRing k d j)).Opens from
        PrimeSpectrum.basicOpen
          (chartRatioElement k d l j)).ι.appTop
        ((Scheme.ΓSpecIso (chartRing k d j)).inv r) := by
  have hpair :
      (chartProductSwap k d l j).symm
          (chartPairAwayOfElement k d l j r) =
        awayMap (homogeneousGrading k d)
          (coordinate_mem_degreeOne k l)
          (rfl :
            coordinate k j * coordinate k l =
              coordinate k j * coordinate k l)
          r := by
    rw [chartPairAwayOfElement,
      RingEquiv.symm_apply_apply]
  change Away (homogeneousGrading k d) (coordinate k j) at r
  change
    (chartRatioOpenToProductIso k d l j).hom.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k l * coordinate k j))).inv
            (chartPairAwayOfElement k d l j r)) =
      (show
        (Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j))).Opens
        from PrimeSpectrum.basicOpen
          (chartRatio k d l j)).ι.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k j))).inv r)
  have hswap :
      (Spec.map
          (chartProductSwap k d l j).toCommRingCatIso.inv).appTop
          ((Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k l * coordinate k j))).inv
              (chartPairAwayOfElement k d l j r)) =
        (Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k j * coordinate k l))).inv
            (awayMap (homogeneousGrading k d)
              (coordinate_mem_degreeOne k l)
              (rfl :
                coordinate k j * coordinate k l =
                  coordinate k j * coordinate k l)
              r) := by
    calc
      _ = (Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k j * coordinate k l))).inv
          ((chartProductSwap k d l j).symm
            (chartPairAwayOfElement k d l j r)) := by
        rw [← CommRingCat.comp_apply,
          ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      _ = _ := by
        exact congrArg
          (Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k j * coordinate k l))).inv hpair
  have haway :
      (Spec.map (CommRingCat.ofHom
          (awayMap (homogeneousGrading k d)
            (coordinate_mem_degreeOne k l)
            (rfl :
              coordinate k j * coordinate k l =
                coordinate k j * coordinate k l)))).appTop
          ((Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k j))).inv r) =
        (Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k j * coordinate k l))).inv
            (awayMap (homogeneousGrading k d)
              (coordinate_mem_degreeOne k l)
              (rfl :
                coordinate k j * coordinate k l =
                  coordinate k j * coordinate k l)
              r) := by
    rw [← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    rfl
  rw [← chartRatioOpenIso_hom_fac k d l j]
  simp only [chartRatioOpenToProductIso, Iso.trans_hom,
    Scheme.Hom.comp_appTop]
  simp only [chartProductSwapSpecIso]
  calc
    _ = (chartRatioOpenIso k d l j).hom.appTop
          ((Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k j * coordinate k l))).inv
              (awayMap (homogeneousGrading k d)
                (coordinate_mem_degreeOne k l)
                (rfl :
                  coordinate k j * coordinate k l =
                    coordinate k j * coordinate k l)
                r)) :=
      congrArg (chartRatioOpenIso k d l j).hom.appTop hswap
    _ = (chartRatioOpenIso k d l j).hom.appTop
          ((Spec.map (CommRingCat.ofHom
            (awayMap (homogeneousGrading k d)
              (coordinate_mem_degreeOne k l)
              (rfl :
                coordinate k j * coordinate k l =
                  coordinate k j * coordinate k l)))).appTop
            ((Scheme.ΓSpecIso (.of <| Away
              (homogeneousGrading k d)
              (coordinate k j))).inv r)) :=
      congrArg (chartRatioOpenIso k d l j).hom.appTop haway.symm
    _ = _ := (CommRingCat.comp_apply _ _ _).symm

/-- The same comparison in the projective product-basic-open model. -/
theorem chartRatioOpenToBasicOpenIso_appTop_element
    (l j : Fin (d + 1)) (r : chartRing k d j) :
    (chartRatioOpenToBasicOpenIso k d l j).hom.appTop
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k l * coordinate k j)).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k l * coordinate k j)
            (chartPairAwayOfElement k d l j r))) =
      (show (Spec (chartRing k d j)).Opens from
        PrimeSpectrum.basicOpen
          (chartRatioElement k d l j)).ι.appTop
        ((Scheme.ΓSpecIso (chartRing k d j)).inv r) := by
  have hspec :
      (Proj.basicOpenIsoSpec
        (homogeneousGrading k d)
        (coordinate k l * coordinate k j)
        (coordinate_mul_mem_degreeTwo k d l j)
        (by omega)).inv.appTop
          ((Proj.basicOpen (homogeneousGrading k d)
            (coordinate k l * coordinate k j)).topIso.inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k l * coordinate k j)
              (chartPairAwayOfElement k d l j r))) =
        (Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k l * coordinate k j))).inv
            (chartPairAwayOfElement k d l j r) := by
    let e :=
      Proj.basicOpenIsoSpec
        (homogeneousGrading k d)
        (coordinate k l * coordinate k j)
        (coordinate_mul_mem_degreeTwo k d l j)
        (by omega)
    have hhom :
        e.hom.appTop
            ((Scheme.ΓSpecIso (.of <| Away
              (homogeneousGrading k d)
              (coordinate k l * coordinate k j))).inv
                (chartPairAwayOfElement k d l j r)) =
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k l * coordinate k j)).topIso.inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k l * coordinate k j)
              (chartPairAwayOfElement k d l j r)) := by
      dsimp only [e]
      simp only [Proj.basicOpenIsoSpec_hom,
        Proj.basicOpenToSpec_app_top,
        CommRingCat.comp_apply, Iso.inv_hom_id_apply]
      rw [CommRingCat.comp_apply]
    calc
      _ = e.inv.appTop
          (e.hom.appTop
            ((Scheme.ΓSpecIso (.of <| Away
              (homogeneousGrading k d)
              (coordinate k l * coordinate k j))).inv
                (chartPairAwayOfElement k d l j r))) :=
        congrArg e.inv.appTop hhom.symm
      _ = _ := by
        rw [← CommRingCat.comp_apply,
          ← Scheme.Hom.comp_appTop]
        simp
  change
    (chartRatioOpenToProductIso k d l j).hom.appTop
        ((Proj.basicOpenIsoSpec
          (homogeneousGrading k d)
          (coordinate k l * coordinate k j)
          (coordinate_mul_mem_degreeTwo k d l j)
          (by omega)).inv.appTop
          ((Proj.basicOpen (homogeneousGrading k d)
            (coordinate k l * coordinate k j)).topIso.inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k l * coordinate k j)
              (chartPairAwayOfElement k d l j r)))) =
      (show (Spec (chartRing k d j)).Opens from
        PrimeSpectrum.basicOpen
          (chartRatioElement k d l j)).ι.appTop
        ((Scheme.ΓSpecIso (chartRing k d j)).inv r)
  calc
    _ = (chartRatioOpenToProductIso k d l j).hom.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k l * coordinate k j))).inv
            (chartPairAwayOfElement k d l j r)) :=
      congrArg
        (chartRatioOpenToProductIso k d l j).hom.appTop hspec
    _ = _ :=
      chartRatioOpenToProductIso_appTop_element
        k d l j r

/-- Equality transport from the ambient pair overlap to its product-basic-open
model. -/
def chartPairProductSectionsIso (l j : Fin (d + 1)) :
    Γ(scheme k d, standardChart k j ⊓ standardChart k l) ≅
      Γ(scheme k d,
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k l * coordinate k j)) :=
  eqToIso (congrArg (fun U => Γ(scheme k d, U))
    (standardChart_inf_eq_productBasicOpen k d l j))

/-- Equality transport which reverses the order of the two standard opens. -/
def chartPairSwapSectionsIso (l j : Fin (d + 1)) :
    Γ(scheme k d, standardChart k l ⊓ standardChart k j) ≅
      Γ(scheme k d, standardChart k j ⊓ standardChart k l) :=
  eqToIso (congrArg (fun U => Γ(scheme k d, U))
    (inf_comm (standardChart k l) (standardChart k j)))

/-- Equality transport induced by commuting the two coordinate factors. -/
abbrev chartPairProductCommuteSectionsIso (l j : Fin (d + 1)) :
    Γ(scheme k d,
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k j * coordinate k l)) ≅
      Γ(scheme k d,
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k l * coordinate k j)) :=
  eqToIso (congrArg
    (fun q => Γ(scheme k d,
      Proj.basicOpen (homogeneousGrading k d) q))
    (mul_comm (coordinate k j) (coordinate k l)))

/-- The homogeneous section on the ambient pair overlap represented by a
localized element of the `j`-th affine chart ring. -/
def chartPairAwaySectionOfElement
    (l j : Fin (d + 1)) (r : chartRing k d j) :
    Γ(scheme k d, standardChart k j ⊓ standardChart k l) :=
  (chartPairProductSectionsIso k d l j).inv
      (Proj.awayToSection (homogeneousGrading k d)
        (coordinate k l * coordinate k j)
        (chartPairAwayOfElement k d l j r))

/-- Transporting an arbitrary affine-chart scalar to a pair overlap is
the homogeneous localization described by `chartPairAwayOfElement`. -/
theorem chartScalarOnPair_eq_awaySectionOfElement
    (l j : Fin (d + 1)) (r : chartRing k d j) :
    chartScalarOnPair k d l j r =
      chartPairAwaySectionOfElement k d l j r := by
  letI : IsOpenImmersion ((standardAffineOpenCover k d).f j) :=
    (standardAffineOpenCover k d).map_prop j
  let U : (Spec (chartRing k d j)).Opens :=
    PrimeSpectrum.basicOpen (chartRatioElement k d l j)
  let B : (scheme k d).Opens :=
    Proj.basicOpen (homogeneousGrading k d)
      (coordinate k l * coordinate k j)
  let e : U.toScheme ≅ B.toScheme :=
    chartRatioOpenToBasicOpenIso k d l j
  let f : Spec (chartRing k d j) ⟶ scheme k d :=
    (standardAffineOpenCover k d).f j
  letI : IsOpenImmersion f := by
    dsimp only [f]
    exact (standardAffineOpenCover k d).map_prop j
  let g : B.toScheme ⟶ scheme k d := B.ι
  let a : Γ(Spec (chartRing k d j), ⊤) :=
    (Scheme.ΓSpecIso (chartRing k d j)).inv r
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op a
  let w : Γ(scheme k d, B) :=
    Proj.awayToSection (homogeneousGrading k d)
      (coordinate k l * coordinate k j)
      (chartPairAwayOfElement k d l j r)
  let t : Γ(B.toScheme, ⊤) := B.topIso.inv w
  let hF : f ''ᵁ U =
      standardChart k j ⊓ standardChart k l :=
    standardAffineCover_image_chartRatio k d l j
  let hB :
      standardChart k j ⊓ standardChart k l = B :=
    standardChart_inf_eq_productBasicOpen k d l j
  let hNested :
      (U.ι ≫ f) ''ᵁ (⊤ : U.toScheme.Opens) =
        f ''ᵁ U := by
    rw [Scheme.Hom.comp_image, U.ι_image_top]
  let hLeft :
      (U.ι ≫ f) ''ᵁ (⊤ : U.toScheme.Opens) =
        standardChart k j ⊓ standardChart k l :=
    hNested.trans hF
  let hIso :
      (e.hom ≫ g) ''ᵁ (⊤ : U.toScheme.Opens) =
        g ''ᵁ (⊤ : B.toScheme.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso]
  let hG :
      g ''ᵁ (⊤ : B.toScheme.Opens) = B :=
    B.ι_image_top
  let hRight :
      (e.hom ≫ g) ''ᵁ (⊤ : U.toScheme.Opens) =
        standardChart k j ⊓ standardChart k l :=
    hIso.trans (hG.trans hB.symm)
  have hratio :
      e.hom.appTop t = U.ι.appTop a := by
    exact chartRatioOpenToBasicOpenIso_appTop_element
      k d l j r
  have hfg : e.hom ≫ g = U.ι ≫ f := by
    exact chartRatioOpenToBasicOpenIso_hom_ι k d l j
  have hnested :
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V)) hNested)).hom
          (((U.ι ≫ f).appIso ⊤).inv (U.ι.appTop a)) =
        (f.appIso U).inv q := by
    exact appIso_inv_nested_open f U a
  have hleft :
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V)) hLeft)).hom
          (((U.ι ≫ f).appIso ⊤).inv (U.ι.appTop a)) =
        (eqToIso (congrArg
          (fun V => Γ(scheme k d, V)) hF)).hom
            ((f.appIso U).inv q) := by
    rw [show hLeft = hNested.trans hF from
      Subsingleton.elim _ _]
    rw [Γ_eqToIso_hom_trans_apply hNested hF,
      hnested]
  have hmiddle :
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V)) hLeft)).hom
          (((U.ι ≫ f).appIso ⊤).inv (U.ι.appTop a)) =
        (eqToIso (congrArg
          (fun V => Γ(scheme k d, V)) hRight)).hom
            (((e.hom ≫ g).appIso ⊤).inv
              (e.hom.appTop t)) := by
    rw [← hratio]
    exact
      (appIso_inv_transport_of_eq hfg
        (standardChart k j ⊓ standardChart k l)
        hRight hLeft (e.hom.appTop t)).symm
  have hiso :
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V)) hIso)).hom
          (((e.hom ≫ g).appIso ⊤).inv
            (e.hom.appTop t)) =
        (g.appIso ⊤).inv t := by
    exact appIso_inv_natural_iso_over e g t
  have hright :
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V)) hRight)).hom
          (((e.hom ≫ g).appIso ⊤).inv
            (e.hom.appTop t)) =
        (eqToIso (congrArg
          (fun V => Γ(scheme k d, V)) hB.symm)).hom w := by
    rw [show hRight =
        (hIso.trans hG).trans hB.symm from
      Subsingleton.elim _ _]
    rw [Γ_eqToIso_hom_trans_apply
      (hIso.trans hG) hB.symm]
    rw [Γ_eqToIso_hom_trans_apply hIso hG]
    rw [hiso]
    change
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V)) hB.symm)).hom
          ((eqToIso (congrArg
            (fun V => Γ(scheme k d, V)) hG)).hom
              ((B.ι.appIso ⊤).inv (B.topIso.inv w))) =
        (eqToIso (congrArg
          (fun V => Γ(scheme k d, V)) hB.symm)).hom w
    rw [opens_ι_appIso_inv_topIso_inv B w]
  change
    (eqToIso (congrArg
      (fun V => Γ(scheme k d, V)) hF)).hom
        ((f.appIso U).inv q) =
      (eqToIso (congrArg
        (fun V => Γ(scheme k d, V)) hB)).inv w
  rw [Γ_eqToIso_inv_eq_hom_symm hB]
  exact hleft.symm.trans (hmiddle.trans hright)

/-- The ring map localizing the `l`-th chart ring to the `l,j` product
overlap. -/
def chartPairAwayFromLRingHom (l j : Fin (d + 1)) :
    chartRing k d l →+*
      Away (homogeneousGrading k d)
        (coordinate k l * coordinate k j) := by
  change Away (homogeneousGrading k d) (coordinate k l) →+* _
  exact awayMap (homogeneousGrading k d)
    (coordinate_mem_degreeOne k j)
    (rfl :
      coordinate k l * coordinate k j =
        coordinate k l * coordinate k j)

theorem chartPairAwayFromLRingHom_apply
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    chartPairAwayFromLRingHom k d l j r =
      awayMap (homogeneousGrading k d)
        (coordinate_mem_degreeOne k j)
        (rfl :
          coordinate k l * coordinate k j =
            coordinate k l * coordinate k j)
        r := by
  rfl

/-- A scalar from chart `l`, localized to the `l,j` overlap and written
with denominator `XₗXⱼ`. -/
def chartPairAwayFromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    Away (homogeneousGrading k d)
      (coordinate k l * coordinate k j) :=
  chartPairAwayFromLRingHom k d l j r

/-- Explicit homogeneous representative of `Xᵢ/Xⱼ` after localization
to the `j,l` overlap. -/
theorem chartPairAwayOfElement_chartRatio
    (i l j : Fin (d + 1)) :
    chartPairAwayOfElement k d l j
        (chartRatioElement k d i j) =
      Away.mk (homogeneousGrading k d)
        (coordinate_mul_mem_degreeTwo k d l j) 1
        (coordinate k i * coordinate k l)
        (coordinate_mul_mem_degreeTwo k d i l) := by
  rw [chartPairAwayOfElement, chartRatioElement,
    chartRatio, Away.isLocalizationElem, awayMap_mk]
  simp only [pow_one, chartProductSwap]
  exact castAway_mk
    (𝒜 := homogeneousGrading k d) (q := 2) (n := 1)
    (mul_comm (coordinate k j) (coordinate k l))
    (coordinate_mul_mem_degreeTwo k d j l)
    (coordinate_mul_mem_degreeTwo k d l j)
    (coordinate_mul_mem_degreeTwo k d i l)

/-- Explicit homogeneous representative of `Xᵢ/Xₗ` transported from
chart `l` to the same pair overlap. -/
theorem chartPairAwayFromL_chartRatio
    (i l j : Fin (d + 1)) :
    chartPairAwayFromL k d l j
        (chartRatioElement k d i l) =
      Away.mk (homogeneousGrading k d)
        (coordinate_mul_mem_degreeTwo k d l j) 1
        (coordinate k i * coordinate k j)
        (coordinate_mul_mem_degreeTwo k d i j) := by
  rw [chartPairAwayFromL, chartPairAwayFromLRingHom_apply, chartRatioElement,
    chartRatio, Away.isLocalizationElem, awayMap_mk]
  simp only [pow_one]

/-- The three coordinate ratios satisfy
`(Xₗ/Xⱼ)(Xᵢ/Xₗ) = Xᵢ/Xⱼ` in the homogeneous localization of the
pairwise overlap. -/
theorem chartPairAway_cocycle
    (i l j : Fin (d + 1)) :
    chartPairAwayOfElement k d l j
          (chartRatioElement k d l j) *
        chartPairAwayFromL k d l j
          (chartRatioElement k d i l) =
      chartPairAwayOfElement k d l j
        (chartRatioElement k d i j) := by
  rw [chartPairAwayOfElement_chartRatio,
    chartPairAwayFromL_chartRatio,
    chartPairAwayOfElement_chartRatio]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- A chain consisting of an inverse equality transport followed by two
forward equality transports is the direct transport along the composite
equality.  Keeping this general avoids unfolding the projective-open terms
when the result is used below. -/
theorem Γ_eqToIso_hom_hom_inv_apply
    {X : Scheme.{0}} {A B C D : X.Opens}
    (hAC : A = C) (hAB : A = B) (hBD : B = D)
    (hCD : C = D) (x : Γ(X, C)) :
    (eqToIso (congrArg (fun U => Γ(X, U)) hBD)).hom
        ((eqToIso (congrArg (fun U => Γ(X, U)) hAB)).hom
          ((eqToIso (congrArg (fun U => Γ(X, U)) hAC)).inv x)) =
      (eqToIso (congrArg (fun U => Γ(X, U)) hCD)).hom x := by
  rw [Γ_eqToIso_inv_eq_hom_symm hAC]
  rw [← Γ_eqToIso_hom_trans_apply hAC.symm hAB]
  rw [← Γ_eqToIso_hom_trans_apply
    (hAC.symm.trans hAB) hBD]

/-- Equality transport along `A = B`, after undoing `A = C`, agrees with
inverse transport along `B = D` whenever the direct `C = D` transport is
known. -/
theorem Γ_eqToIso_hom_inv_eq_inv_of_direct
    {X : Scheme.{0}} {A B C D : X.Opens}
    (hAC : A = C) (hAB : A = B) (hBD : B = D)
    (hCD : C = D) (x : Γ(X, C)) (y : Γ(X, D))
    (hxy :
      (eqToIso (congrArg (fun U => Γ(X, U)) hCD)).hom x = y) :
    (eqToIso (congrArg (fun U => Γ(X, U)) hAB)).hom
        ((eqToIso (congrArg (fun U => Γ(X, U)) hAC)).inv x) =
      (eqToIso (congrArg (fun U => Γ(X, U)) hBD)).inv y := by
  let E := eqToIso (congrArg (fun U => Γ(X, U)) hBD)
  apply E.commRingCatIsoToRingEquiv.injective
  change E.hom _ = E.hom (E.inv y)
  rw [E.inv_hom_id_apply]
  exact (Γ_eqToIso_hom_hom_inv_apply hAC hAB hBD hCD x).trans hxy

/-- In a commutative square of ring isomorphisms, transporting backwards
along one side and forwards along the other agrees with inverse transport
along the remaining side. -/
theorem commRingCat_isoSquare_inv_transport
    {A B C D : CommRingCat}
    (EAC : A ≅ C) (EAB : A ≅ B)
    (EBD : B ≅ D) (ECD : C ≅ D)
    (hcomm : EAB.hom ≫ EBD.hom = EAC.hom ≫ ECD.hom)
    (x : C) (y : D) (hxy : ECD.hom x = y) :
    EAB.hom (EAC.inv x) = EBD.inv y := by
  apply EBD.commRingCatIsoToRingEquiv.injective
  change EBD.hom (EAB.hom (EAC.inv x)) = EBD.hom (EBD.inv y)
  rw [EBD.inv_hom_id_apply]
  have happ := congrArg
    (fun (q : A ⟶ D) => q.hom (EAC.inv x)) hcomm
  simp only [CommRingCat.comp_apply] at happ
  rw [happ, EAC.inv_hom_id_apply]
  exact hxy

/-- Commuting the two factors defining a projective basic open transports
the corresponding homogeneous-localization section by the cast
equivalence. -/
theorem awayToSection_cast
    (f g : MvPolynomial (Fin (d + 1)) k)
    (h : f = g)
    (r : Away (homogeneousGrading k d) f) :
    (eqToIso (congrArg
      (fun q =>
        Γ(scheme k d,
          Proj.basicOpen (homogeneousGrading k d) q))
      h)).hom
        (Proj.awayToSection (homogeneousGrading k d)
          f r) =
      Proj.awayToSection (homogeneousGrading k d)
        g (RingEquiv.cast h r) := by
  subst g
  rfl

/-- Equality transport of homogeneous sections, followed by an equality in
the transported localization. -/
theorem awayToSection_cast_of_cast_eq
    (f g : MvPolynomial (Fin (d + 1)) k)
    (h : f = g)
    (r : Away (homogeneousGrading k d) f)
    (s : Away (homogeneousGrading k d) g)
    (hrs : RingEquiv.cast h r = s) :
    (eqToIso (congrArg
      (fun q =>
        Γ(scheme k d,
          Proj.basicOpen (homogeneousGrading k d) q))
      h)).hom
        (Proj.awayToSection (homogeneousGrading k d) f r) =
      Proj.awayToSection (homogeneousGrading k d) g s :=
  (awayToSection_cast k d f g h r).trans
    (congrArg
      (Proj.awayToSection (homogeneousGrading k d) g) hrs)

/-- Casting the chart-`l` homogeneous representative from denominator
`XⱼXₗ` to `XₗXⱼ` gives the direct localization representative. -/
theorem cast_chartPairAwayOfElement_swap
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    RingEquiv.cast
        (mul_comm (coordinate k j) (coordinate k l))
        (chartPairAwayOfElement k d j l r) =
      chartPairAwayFromL k d l j r := by
  dsimp only [chartPairAwayOfElement,
    chartPairAwayFromL, chartProductSwap]
  change
    (RingEquiv.cast
      (mul_comm (coordinate k j) (coordinate k l)))
      ((RingEquiv.cast
        (mul_comm (coordinate k l) (coordinate k j)))
          (awayMap (homogeneousGrading k d)
            (coordinate_mem_degreeOne k j)
            (rfl :
              coordinate k l * coordinate k j =
                coordinate k l * coordinate k j)
            r)) =
      awayMap (homogeneousGrading k d)
        (coordinate_mem_degreeOne k j)
        (rfl :
          coordinate k l * coordinate k j =
            coordinate k l * coordinate k j)
        r
  have he :
      (RingEquiv.cast
          (mul_comm (coordinate k l) (coordinate k j)) :
        Away (homogeneousGrading k d)
            (coordinate k l * coordinate k j) ≃+*
          Away (homogeneousGrading k d)
            (coordinate k j * coordinate k l)) =
        (RingEquiv.cast
          (mul_comm (coordinate k j) (coordinate k l)) :
        Away (homogeneousGrading k d)
            (coordinate k j * coordinate k l) ≃+*
          Away (homogeneousGrading k d)
            (coordinate k l * coordinate k j)).symm := by
    ext x
    rfl
  rw [he, RingEquiv.apply_symm_apply]

/-- The native product-basic-open section obtained from a scalar on chart
`l`. -/
abbrev chartPairNativeAwaySectionFromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    Γ(scheme k d,
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k j * coordinate k l)) :=
  Proj.awayToSection (homogeneousGrading k d)
    (coordinate k j * coordinate k l)
    (chartPairAwayOfElement k d j l r)

/-- The same scalar represented on the commuted product-basic-open model. -/
abbrev chartPairCommonAwaySectionFromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    Γ(scheme k d,
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k l * coordinate k j)) :=
  Proj.awayToSection (homogeneousGrading k d)
    (coordinate k l * coordinate k j)
    (chartPairAwayFromL k d l j r)

/-- Direct equality transport across commutation of the product denominator
sends the native homogeneous section to the representative localized from
the other chart. -/
abbrev chartPairCastedAwaySectionFromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    Γ(scheme k d,
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k l * coordinate k j)) :=
  (chartPairProductCommuteSectionsIso k d l j).hom
    (chartPairNativeAwaySectionFromL k d l j r)

/-- The named equality-transport section is the representative localized
directly from chart `l`. -/
theorem chartPairAwaySection_cast_fromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    (eqToIso (congrArg
      (fun q =>
        Γ(scheme k d,
          Proj.basicOpen (homogeneousGrading k d) q))
      (mul_comm (coordinate k j) (coordinate k l)))).hom
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k j * coordinate k l)
          (chartPairAwayOfElement k d j l r)) =
      Proj.awayToSection (homogeneousGrading k d)
        (coordinate k l * coordinate k j)
        (chartPairAwayFromL k d l j r) := by
  rw [← cast_chartPairAwayOfElement_swap k d l j r]
  exact awayToSection_cast k d
      (coordinate k j * coordinate k l)
      (coordinate k l * coordinate k j)
      (mul_comm (coordinate k j) (coordinate k l))
      (chartPairAwayOfElement k d j l r)

/-- The named pair-overlap transports form a commutative square. -/
theorem chartPairSectionsIso_hom_commute
    (l j : Fin (d + 1)) :
    (chartPairSwapSectionsIso k d l j).hom ≫
        (chartPairProductSectionsIso k d l j).hom =
      (chartPairProductSectionsIso k d j l).hom ≫
        (eqToIso (congrArg
          (fun q =>
            Γ(scheme k d,
              Proj.basicOpen (homogeneousGrading k d) q))
          (mul_comm (coordinate k j) (coordinate k l)))).hom := by
  dsimp only [chartPairSwapSectionsIso,
    chartPairProductSectionsIso]
  rw [Γ_eqToIso_hom_trans
    (inf_comm (standardChart k l) (standardChart k j))
    (standardChart_inf_eq_productBasicOpen k d l j)]
  rw [Γ_eqToIso_hom_trans
    (standardChart_inf_eq_productBasicOpen k d j l)
    (congrArg (Proj.basicOpen (homogeneousGrading k d))
      (mul_comm (coordinate k j) (coordinate k l)))]

/-- Evaluating the transport square after undoing the native product-open
identification leaves only the commuted product-open transport. -/
abbrev chartPairNativeTransportedSectionFromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :=
  (chartPairProductSectionsIso k d l j).hom
    ((chartPairSwapSectionsIso k d l j).hom
      ((chartPairProductSectionsIso k d j l).inv
        (chartPairNativeAwaySectionFromL k d l j r)))

theorem chartPairSectionsIso_hom_native_fromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    chartPairNativeTransportedSectionFromL k d l j r =
      (eqToIso (congrArg
        (fun q =>
          Γ(scheme k d,
            Proj.basicOpen (homogeneousGrading k d) q))
        (mul_comm (coordinate k j) (coordinate k l)))).hom
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k j * coordinate k l)
            (chartPairAwayOfElement k d j l r)) := by
  unfold chartPairNativeTransportedSectionFromL
  have happ := congrArg
    (fun q => q.hom
      ((chartPairProductSectionsIso k d j l).inv
        (chartPairNativeAwaySectionFromL k d l j r)))
    (chartPairSectionsIso_hom_commute k d l j)
  simp only [CommRingCat.comp_apply] at happ
  rw [happ, (chartPairProductSectionsIso k d j l).inv_hom_id_apply]

/-- The chart scalar in its native product-open model. -/
theorem chartScalarOnPair_eq_native_fromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    chartScalarOnPair k d j l r =
      (chartPairProductSectionsIso k d j l).inv
        (chartPairNativeAwaySectionFromL k d l j r) := by
  simpa only [chartPairAwaySectionOfElement,
    chartPairNativeAwaySectionFromL] using
    chartScalarOnPair_eq_awaySectionOfElement k d j l r

/-- Applying the common product-open map preserves the native scalar
comparison. -/
theorem chartPairProduct_hom_swap_scalar_eq_native
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    (chartPairProductSectionsIso k d l j).hom
        ((chartPairSwapSectionsIso k d l j).hom
          (chartScalarOnPair k d j l r)) =
      chartPairNativeTransportedSectionFromL k d l j r :=
  congrArg
    (fun z => (chartPairProductSectionsIso k d l j).hom
      ((chartPairSwapSectionsIso k d l j).hom z))
    (chartScalarOnPair_eq_native_fromL k d l j r)

/-- After applying the common product-open isomorphism, the transported
chart scalar is the explicit common homogeneous section. -/
theorem chartPairTransportedScalar_hom_fromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    (chartPairProductSectionsIso k d l j).hom
        ((chartPairSwapSectionsIso k d l j).hom
          (chartScalarOnPair k d j l r)) =
      chartPairCommonAwaySectionFromL k d l j r := by
  exact eq_trans_three
    (chartPairProduct_hom_swap_scalar_eq_native k d l j r)
    (chartPairSectionsIso_hom_native_fromL k d l j r)
    (chartPairAwaySection_cast_fromL k d l j r)

/-- A scalar transported from chart `l` to the ambient `j,l` pairwise
intersection. -/
def chartScalarFromLOnPair
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    Γ(scheme k d, standardChart k j ⊓ standardChart k l) :=
  (chartPairSwapSectionsIso k d l j).hom
      (chartScalarOnPair k d j l r)

/-- The homogeneous section on the common ambient pair overlap
represented by a scalar from chart `l`. -/
def chartPairAwaySectionFromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    Γ(scheme k d, standardChart k j ⊓ standardChart k l) :=
  (chartPairProductSectionsIso k d l j).inv
      (chartPairCommonAwaySectionFromL k d l j r)

/-- Cross-chart scalar transport agrees with the direct homogeneous
localization on the common pair overlap. -/
theorem chartScalarFromLOnPair_eq_awaySectionFromL
    (l j : Fin (d + 1)) (r : chartRing k d l) :
    chartScalarFromLOnPair k d l j r =
      chartPairAwaySectionFromL k d l j r := by
  apply (chartPairProductSectionsIso k d l j).commRingCatIsoToRingEquiv.injective
  change
    (chartPairProductSectionsIso k d l j).hom
        ((chartPairSwapSectionsIso k d l j).hom
          (chartScalarOnPair k d j l r)) =
      (chartPairProductSectionsIso k d l j).hom
        ((chartPairProductSectionsIso k d l j).inv
          (chartPairCommonAwaySectionFromL k d l j r))
  rw [(chartPairProductSectionsIso k d l j).inv_hom_id_apply]
  exact chartPairTransportedScalar_hom_fromL k d l j r

/-- The three homogeneous sections on an ambient pair overlap satisfy
the coordinate-ratio cocycle. -/
theorem chartPairAwaySection_cocycle
    (i l j : Fin (d + 1)) :
    chartPairAwaySectionOfElement k d l j
          (chartRatioElement k d l j) *
        chartPairAwaySectionFromL k d l j
          (chartRatioElement k d i l) =
      chartPairAwaySectionOfElement k d l j
        (chartRatioElement k d i j) := by
  rw [chartPairAwaySectionOfElement,
    chartPairAwaySectionFromL,
    chartPairAwaySectionOfElement,
    chartPairCommonAwaySectionFromL,
    ← map_mul, ← map_mul, chartPairAway_cocycle]

/-- Ambient pair-overlap form of
`(Xₗ/Xⱼ)(Xᵢ/Xₗ) = Xᵢ/Xⱼ`. -/
theorem chartScalarOnPair_cocycle
    (i l j : Fin (d + 1)) :
    chartScalarOnPair k d l j
          (chartRatioElement k d l j) *
        chartScalarFromLOnPair k d l j
          (chartRatioElement k d i l) =
      chartScalarOnPair k d l j
        (chartRatioElement k d i j) := by
  rw [chartScalarOnPair_eq_awaySectionOfElement,
    chartScalarFromLOnPair_eq_awaySectionFromL,
    chartScalarOnPair_eq_awaySectionOfElement]
  exact chartPairAwaySection_cocycle k d i l j

/-- Pair-overlap scalar transport preserves powers. -/
theorem chartScalarOnPair_pow
    (l j : Fin (d + 1))
    (r : chartRing k d j) (N : ℕ) :
    chartScalarOnPair k d l j (r ^ N) =
      chartScalarOnPair k d l j r ^ N := by
  dsimp only [chartScalarOnPair]
  simp only [map_pow]

/-- Cross-chart scalar transport to a pair overlap preserves powers. -/
theorem chartScalarFromLOnPair_pow
    (l j : Fin (d + 1))
    (r : chartRing k d l) (N : ℕ) :
    chartScalarFromLOnPair k d l j (r ^ N) =
      chartScalarFromLOnPair k d l j r ^ N := by
  rw [chartScalarFromLOnPair,
    chartScalarFromLOnPair, chartScalarOnPair_pow,
    map_pow]

/-- Power form of the pair-overlap coordinate-ratio cocycle. -/
theorem chartScalarOnPair_cocycle_pow
    (N : ℕ) (i l j : Fin (d + 1)) :
    chartScalarOnPair k d l j
            (chartRatioElement k d l j) ^ N *
        chartScalarFromLOnPair k d l j
            (chartRatioElement k d i l) ^ N =
      chartScalarOnPair k d l j
          (chartRatioElement k d i j) ^ N := by
  rw [← mul_pow, chartScalarOnPair_cocycle]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
