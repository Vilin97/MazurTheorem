/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartTripleOverlap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCocycleSections

/-!
# Scalar transition functions on projective-chart overlaps

This file compares the affine regular functions `Xᵢ / Xⱼ` with the
homogeneous fractions used in the Serre-twist descent datum.  The
comparison is first made on pairwise overlaps and then restricted to a
common triple overlap.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist
open HomogeneousLocalization

variable (k : Type) [CommRing k] (d : ℕ)

private theorem presheaf_map_eqToIso_apply
    {X : Scheme.{0}}
    (F : X.Opensᵒᵖ ⥤ CommRingCat.{0})
    {A B A' B' : X.Opens}
    (eA : A = A') (eB : B = B')
    (h : A ≤ B) (h' : A' ≤ B')
    (x : F.obj (.op B)) :
    (eqToIso (congrArg (fun U => F.obj (.op U)) eA)).hom
        (F.map (homOfLE h).op x) =
      F.map (homOfLE h').op
        ((eqToIso
          (congrArg (fun U => F.obj (.op U)) eB)).hom x) := by
  subst A'
  subst B'
  rfl

private theorem opens_ι_appIso_inv_appTop
    {X : Scheme.{0}} (U : X.Opens) (s : Γ(X, ⊤)) :
    (U.ι.appIso ⊤).inv (U.ι.appTop s) =
      (eqToIso (congrArg (fun W => Γ(X, W))
        U.ι_image_top)).inv
        (X.presheaf.map U.leTop.op s) := by
  have hcomp :
      U.ι.appTop ≫ (U.ι.appIso
          (⊤ : U.toScheme.Opens)).inv =
        X.presheaf.map
          (homOfLE
            (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤
              (⊤ : X.Opens) from le_top)).op := by
    convert
      (Scheme.Hom.appLE_appIso_inv U.ι
        (U := (⊤ : X.Opens))
        (V := (⊤ : U.toScheme.Opens))
        (show (⊤ : U.toScheme.Opens) ≤
          U.ι ⁻¹ᵁ (⊤ : X.Opens) by simp)) using 1
    simp [Scheme.Hom.appLE]
    exact (Category.comp_id _).symm
  rw [← ConcreteCategory.comp_apply, hcomp]
  rw [Γ_eqToIso_inv_eq_presheaf_map U.ι_image_top]
  rw [← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  congr 1

theorem appIso_inv_nested_open
    {A X : Scheme.{0}} (f : A ⟶ X) [IsOpenImmersion f]
    (U : A.Opens) (s : Γ(A, ⊤)) :
    (eqToIso (congrArg (fun W => Γ(X, W))
      (by
        rw [Scheme.Hom.comp_image, U.ι_image_top]))).hom
        (((U.ι ≫ f).appIso ⊤).inv (U.ι.appTop s)) =
      (f.appIso U).inv
        (A.presheaf.map U.leTop.op s) := by
  let hU : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U :=
    U.ι_image_top
  let hc :
      f ''ᵁ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) =
        (U.ι ≫ f) ''ᵁ (⊤ : U.toScheme.Opens) :=
    (Scheme.Hom.comp_image U.ι f ⊤).symm
  let ho :
      (U.ι ≫ f) ''ᵁ (⊤ : U.toScheme.Opens) =
        f ''ᵁ U := by
    rw [Scheme.Hom.comp_image, hU]
  simp only [Scheme.Hom.comp_appIso, Iso.trans_inv,
    ConcreteCategory.comp_apply]
  change
    (eqToIso (congrArg (fun W => Γ(X, W)) ho)).hom
        ((X.presheaf.mapIso (eqToIso hc).op).inv
          ((f.appIso (U.ι ''ᵁ
            (⊤ : U.toScheme.Opens))).inv
            ((U.ι.appIso ⊤).inv (U.ι.appTop s)))) =
      (f.appIso U).inv
        (A.presheaf.map U.leTop.op s)
  rw [opens_ι_appIso_inv_appTop]
  rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom hc]
  rw [← ConcreteCategory.comp_apply,
    Γ_eqToIso_hom_trans hc ho]
  rw [show hc.trans ho =
      congrArg (fun V => f ''ᵁ V) hU from
    Subsingleton.elim _ _]
  exact appIso_inv_eqToIso_transport f hU
    (A.presheaf.map U.leTop.op s)

theorem Γ_eqToIso_hom_trans_apply
    {X : Scheme.{0}} {U V W : X.Opens}
    (hUV : U = V) (hVW : V = W)
    (s : Γ(X, U)) :
    (eqToIso (congrArg (fun T => Γ(X, T))
      (hUV.trans hVW))).hom s =
      (eqToIso (congrArg (fun T => Γ(X, T)) hVW)).hom
        ((eqToIso (congrArg
          (fun T => Γ(X, T)) hUV)).hom s) := by
  rw [← ConcreteCategory.comp_apply,
    Γ_eqToIso_hom_trans hUV hVW]

theorem Γ_eqToIso_inv_eq_hom_symm
    {X : Scheme.{0}} {U V : X.Opens} (h : U = V) :
    (eqToIso (congrArg (fun T => Γ(X, T)) h)).inv =
      (eqToIso
        (congrArg (fun T => Γ(X, T)) h.symm)).hom := by
  subst V
  simp

theorem appIso_inv_transport_of_eq
    {A X : Scheme.{0}} {f g : A ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g]
    (hfg : f = g) (V : X.Opens)
    (hf : f ''ᵁ (⊤ : A.Opens) = V)
    (hg : g ''ᵁ (⊤ : A.Opens) = V)
    (s : Γ(A, ⊤)) :
    (eqToIso (congrArg (fun W => Γ(X, W)) hf)).hom
        ((f.appIso ⊤).inv s) =
      (eqToIso (congrArg (fun W => Γ(X, W)) hg)).hom
        ((g.appIso ⊤).inv s) := by
  subst g
  rw [show hg = hf from Subsingleton.elim _ _]

theorem opens_ι_appIso_inv_topIso_inv
    {X : Scheme.{0}} (U : X.Opens) (r : Γ(X, U)) :
    (eqToIso (congrArg (fun W => Γ(X, W))
      U.ι_image_top)).hom
        ((U.ι.appIso ⊤).inv (U.topIso.inv r)) = r := by
  have htop :
      (eqToIso (congrArg (fun W => Γ(X, W))
        U.ι_image_top)).hom = U.topIso.hom := by
    rw [Γ_eqToIso_hom_eq_presheaf_map U.ι_image_top]
    symm
    exact Scheme.Opens.topIso_hom U
  rw [htop, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv]
  exact U.topIso.inv_hom_id_apply r

/-- A chart-ring scalar restricted to a ratio basic open and transported
to the corresponding ambient pairwise intersection. -/
def chartScalarOnPair
    (i j : Fin (d + 1))
    (r : chartRing k d j) :
    Γ(scheme k d, standardChart k j ⊓ standardChart k i) :=
  let U : (Spec (chartRing k d j)).Opens :=
    chartRatioOpen k d i j
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op
      ((Scheme.ΓSpecIso (chartRing k d j)).inv r)
  (eqToIso (congrArg
    (fun V => Γ(scheme k d, V))
    (standardAffineCover_image_chartRatio k d i j))).hom
    ((ConcreteCategory.hom
      ((standardChartMap k d j).appIso U).inv) q)

/-- Pair-overlap transport is semilinear for the transported affine-chart
scalar. -/
theorem chartOverlapSectionsIso_hom_smul
    (M : (scheme k d).Modules)
    (i j : Fin (d + 1))
    (r : chartRing k d j)
    (s : Γ(chartModule k d M j,
      chartRatioOpen k d i j)) :
    (chartOverlapSectionsIso k d M i j).hom (r • s) =
      chartScalarOnPair k d i j r •
        (chartOverlapSectionsIso k d M i j).hom s := by
  rw [AlgebraicGeometry.Scheme.Modules.smul_Spec_def]
  dsimp only [chartOverlapSectionsIso, chartScalarOnPair]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  let U : (Spec (chartRing k d j)).Opens :=
    chartRatioOpen k d i j
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op
      ((Scheme.ΓSpecIso (chartRing k d j)).inv r)
  have hsmul :
      (M.restrictAppIso
          (standardChartMap k d j) U).hom
          (q • s) =
        ((standardChartMap k d j).appIso U).inv q •
          (M.restrictAppIso
            (standardChartMap k d j) U).hom s := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) s)
      (AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom
        (standardChartMap k d j) M U q)
  refine (congrArg
    (eqToIso (congrArg (fun V => Γ(M, V))
      (standardAffineCover_image_chartRatio
        k d i j))).hom hsmul).trans ?_
  exact eqToIso_smul_apply M
    (standardAffineCover_image_chartRatio k d i j) _ _

/-- Restricting a transported pair scalar to a smaller product basic
open agrees with transporting the scalar directly to that product open. -/
theorem chartScalarOnTriple_eq_restrict_pairJL
    (i l j : Fin (d + 1))
    (r : chartRing k d j) :
    chartScalarOnTriple k d i l j r =
      (scheme k d).presheaf.map
        (homOfLE (chartTriple_le_pairJL k d i l j)).op
        (chartScalarOnPair k d l j r) := by
  letI : IsOpenImmersion ((standardAffineOpenCover k d).f j) :=
    (standardAffineOpenCover k d).map_prop j
  let U : (Spec (chartRing k d j)).Opens :=
    PrimeSpectrum.basicOpen (chartRatioElement k d l j)
  let W : (Spec (chartRing k d j)).Opens :=
    PrimeSpectrum.basicOpen
      (chartRatioElement k d i j *
        chartRatioElement k d l j)
  let hWU : W ≤ U :=
    PrimeSpectrum.basicOpen_mul_le_right
      (chartRatioElement k d i j)
      (chartRatioElement k d l j)
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op
      ((Scheme.ΓSpecIso (chartRing k d j)).inv r)
  have hq :
      (Spec (chartRing k d j)).presheaf.map W.leTop.op
          ((Scheme.ΓSpecIso (chartRing k d j)).inv r) =
        (Spec (chartRing k d j)).presheaf.map
          (homOfLE hWU).op q := by
    have hm :
        (Spec (chartRing k d j)).presheaf.map U.leTop.op ≫
            (Spec (chartRing k d j)).presheaf.map
              (homOfLE hWU).op =
          (Spec (chartRing k d j)).presheaf.map W.leTop.op := by
      rw [← Functor.map_comp]
      rfl
    exact (congrArg
      (fun (φ : _ ⟶ _) =>
        (ConcreteCategory.hom φ)
          ((Scheme.ΓSpecIso (chartRing k d j)).inv r)) hm).symm
  have hnat :
      (((standardAffineOpenCover k d).f j).appIso W).inv
          ((Spec (chartRing k d j)).presheaf.map
            (homOfLE hWU).op q) =
        (scheme k d).presheaf.map
          (homOfLE
            (Scheme.Hom.image_mono
              ((standardAffineOpenCover k d).f j) hWU)).op
          ((((standardAffineOpenCover k d).f j).appIso U).inv q) := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) q)
      (((standardAffineOpenCover k d).f j).appIso_inv_naturality
        (homOfLE hWU).op)
  dsimp only [chartScalarOnTriple, chartScalarOnPair]
  rw [hq]
  refine (congrArg
    (eqToIso (congrArg (fun V => Γ(scheme k d, V))
      (standardAffineCover_image_chartRatio_mul
        k d i l j))).hom hnat).trans ?_
  exact
    presheaf_map_eqToIso_apply (scheme k d).presheaf
      (standardAffineCover_image_chartRatio_mul k d i l j)
      (standardAffineCover_image_chartRatio k d l j)
      _ (chartTriple_le_pairJL k d i l j)
      ((((standardAffineOpenCover k d).f j).appIso U).inv q)

/-- The analogous restriction identity through the pair formed by the
first and base charts. -/
theorem chartScalarOnTriple_eq_restrict_pairJI
    (i l j : Fin (d + 1))
    (r : chartRing k d j) :
    chartScalarOnTriple k d i l j r =
      (scheme k d).presheaf.map
        (homOfLE (chartTriple_le_pairJI k d i l j)).op
        (chartScalarOnPair k d i j r) := by
  letI : IsOpenImmersion ((standardAffineOpenCover k d).f j) :=
    (standardAffineOpenCover k d).map_prop j
  let U : (Spec (chartRing k d j)).Opens :=
    PrimeSpectrum.basicOpen (chartRatioElement k d i j)
  let W : (Spec (chartRing k d j)).Opens :=
    PrimeSpectrum.basicOpen
      (chartRatioElement k d i j *
        chartRatioElement k d l j)
  let hWU : W ≤ U :=
    PrimeSpectrum.basicOpen_mul_le_left
      (chartRatioElement k d i j)
      (chartRatioElement k d l j)
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op
      ((Scheme.ΓSpecIso (chartRing k d j)).inv r)
  have hq :
      (Spec (chartRing k d j)).presheaf.map W.leTop.op
          ((Scheme.ΓSpecIso (chartRing k d j)).inv r) =
        (Spec (chartRing k d j)).presheaf.map
          (homOfLE hWU).op q := by
    have hm :
        (Spec (chartRing k d j)).presheaf.map U.leTop.op ≫
            (Spec (chartRing k d j)).presheaf.map
              (homOfLE hWU).op =
          (Spec (chartRing k d j)).presheaf.map W.leTop.op := by
      rw [← Functor.map_comp]
      rfl
    exact (congrArg
      (fun (φ : _ ⟶ _) =>
        (ConcreteCategory.hom φ)
          ((Scheme.ΓSpecIso (chartRing k d j)).inv r)) hm).symm
  have hnat :
      (((standardAffineOpenCover k d).f j).appIso W).inv
          ((Spec (chartRing k d j)).presheaf.map
            (homOfLE hWU).op q) =
        (scheme k d).presheaf.map
          (homOfLE
            (Scheme.Hom.image_mono
              ((standardAffineOpenCover k d).f j) hWU)).op
          ((((standardAffineOpenCover k d).f j).appIso U).inv q) := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) q)
      (((standardAffineOpenCover k d).f j).appIso_inv_naturality
        (homOfLE hWU).op)
  dsimp only [chartScalarOnTriple, chartScalarOnPair]
  rw [hq]
  refine (congrArg
    (eqToIso (congrArg (fun V => Γ(scheme k d, V))
      (standardAffineCover_image_chartRatio_mul
        k d i l j))).hom hnat).trans ?_
  exact
    presheaf_map_eqToIso_apply (scheme k d).presheaf
      (standardAffineCover_image_chartRatio_mul k d i l j)
      (standardAffineCover_image_chartRatio k d i j)
      _ (chartTriple_le_pairJI k d i l j)
      ((((standardAffineOpenCover k d).f j).appIso U).inv q)

/-- The ambient pairwise intersection is the homogeneous product basic
open, with the factors written in the order used by the Serre datum. -/
lemma standardChart_inf_eq_productBasicOpen
    (i j : Fin (d + 1)) :
    standardChart k j ⊓ standardChart k i =
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j) := by
  change
    Proj.basicOpen (homogeneousGrading k d) (coordinate k j) ⊓
        Proj.basicOpen (homogeneousGrading k d) (coordinate k i) =
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
  rw [Proj.basicOpen_mul]
  exact inf_comm _ _

/-- The homogeneous fraction `Xᵢ / Xⱼ`, regarded as an ambient regular
function on the pairwise intersection of the `j`-th and `i`-th charts. -/
def chartPairAwaySection
    (i j : Fin (d + 1)) :
    Γ(scheme k d, standardChart k j ⊓ standardChart k i) :=
  (eqToIso (congrArg (fun U => Γ(scheme k d, U))
    (standardChart_inf_eq_productBasicOpen k d i j))).inv
      (Proj.awayToSection (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
        (awayFraction k d i j))

/-- The affine-chart function `Xᵢ / Xⱼ`, transported to the ambient
pairwise overlap, is the homogeneous fraction used by the Serre datum. -/
theorem chartScalarOnPair_chartRatio
    (i j : Fin (d + 1)) :
    chartScalarOnPair k d i j (chartRatioElement k d i j) =
      chartPairAwaySection k d i j := by
  let U : (Spec (chartRing k d j)).Opens :=
    chartRatioOpen k d i j
  let B : (scheme k d).Opens :=
    Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
  let e : U.toScheme ≅ B.toScheme :=
    chartRatioOpenToBasicOpenIso k d i j
  let f : Spec (chartRing k d j) ⟶ scheme k d :=
    standardChartMap k d j
  let g : B.toScheme ⟶ scheme k d := B.ι
  let a : Γ(Spec (chartRing k d j), ⊤) :=
    (Scheme.ΓSpecIso (chartRing k d j)).inv
      (chartRatioElement k d i j)
  let q : Γ(Spec (chartRing k d j), U) :=
    (Spec (chartRing k d j)).presheaf.map U.leTop.op a
  let w : Γ(scheme k d, B) :=
    Proj.awayToSection (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
      (awayFraction k d i j)
  let t : Γ(B.toScheme, ⊤) := B.topIso.inv w
  let hF : f ''ᵁ U =
      standardChart k j ⊓ standardChart k i :=
    standardAffineCover_image_chartRatio k d i j
  let hB :
      standardChart k j ⊓ standardChart k i = B :=
    standardChart_inf_eq_productBasicOpen k d i j
  let hNested :
      (U.ι ≫ f) ''ᵁ (⊤ : U.toScheme.Opens) =
        f ''ᵁ U := by
    rw [Scheme.Hom.comp_image, U.ι_image_top]
  let hLeft :
      (U.ι ≫ f) ''ᵁ (⊤ : U.toScheme.Opens) =
        standardChart k j ⊓ standardChart k i :=
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
        standardChart k j ⊓ standardChart k i :=
    hIso.trans (hG.trans hB.symm)
  have hratio :
      e.hom.appTop t = U.ι.appTop a := by
    exact chartRatioOpenToBasicOpenIso_appTop_awayFraction
      k d i j
  have hfg : e.hom ≫ g = U.ι ≫ f := by
    exact chartRatioOpenToBasicOpenIso_hom_ι k d i j
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
        (standardChart k j ⊓ standardChart k i)
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

/-- The ambient open used by affine chart transport is the homogeneous
triple basic open used by the Serre cocycle. -/
lemma chartTripleOpen_eq_tripleOpen
    (i l j : Fin (d + 1)) :
    standardChart k j ⊓
        (standardChart k i ⊓ standardChart k l) =
      tripleOpen k d i l j := by
  change
    Proj.basicOpen (homogeneousGrading k d) (coordinate k j) ⊓
        (Proj.basicOpen (homogeneousGrading k d) (coordinate k i) ⊓
          Proj.basicOpen (homogeneousGrading k d) (coordinate k l)) =
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k l * coordinate k j)
  rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
  ac_rfl

theorem ambientAwaySection_restrict
    {q : ℕ}
    (xf xg : MvPolynomial (Fin (d + 1)) k)
    (hg : xg ∈ homogeneousGrading k d q)
    (xt : MvPolynomial (Fin (d + 1)) k)
    (hxt : xt = xf * xg)
    (hopen :
      Proj.basicOpen (homogeneousGrading k d) xt ≤
        Proj.basicOpen (homogeneousGrading k d) xf)
    (a : Away (homogeneousGrading k d) xf) :
    (scheme k d).presheaf.map (homOfLE hopen).op
        (Proj.awayToSection
          (homogeneousGrading k d) xf a) =
      Proj.awayToSection (homogeneousGrading k d) xt
        (awayMap (homogeneousGrading k d) hg hxt a) := by
  have hs :=
    section_restrict k d xf xg hg xt hxt hopen a
  rw [← ConcreteCategory.comp_apply,
    topIso_inv_homOfLE_appTop,
    ConcreteCategory.comp_apply] at hs
  have h := congrArg
    (Proj.basicOpen (homogeneousGrading k d) xt).topIso.hom hs
  simpa only [Iso.inv_hom_id_apply] using h

/-- The `Xᵢ/Xₗ` triple-overlap scalar, expressed on the affine ambient
triple intersection. -/
def chartTripleAwayIJ
    (i l j : Fin (d + 1)) :
    Γ(scheme k d, standardChart k j ⊓
      (standardChart k i ⊓ standardChart k l)) :=
  (eqToIso (congrArg (fun U => Γ(scheme k d, U))
    (chartTripleOpen_eq_tripleOpen k d i l j))).inv
      (Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayIJ k d i l j))

/-- The `Xₗ/Xⱼ` triple-overlap scalar in the affine ambient model. -/
def chartTripleAwayJK
    (i l j : Fin (d + 1)) :
    Γ(scheme k d, standardChart k j ⊓
      (standardChart k i ⊓ standardChart k l)) :=
  (eqToIso (congrArg (fun U => Γ(scheme k d, U))
    (chartTripleOpen_eq_tripleOpen k d i l j))).inv
      (Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayJK k d i l j))

/-- The `Xᵢ/Xⱼ` triple-overlap scalar in the affine ambient model. -/
def chartTripleAwayIK
    (i l j : Fin (d + 1)) :
    Γ(scheme k d, standardChart k j ⊓
      (standardChart k i ⊓ standardChart k l)) :=
  (eqToIso (congrArg (fun U => Γ(scheme k d, U))
    (chartTripleOpen_eq_tripleOpen k d i l j))).inv
      (Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayIK k d i l j))

/-- The base-`j` chart scalar `Xₗ/Xⱼ` is the `JK` homogeneous fraction
on the common triple overlap. -/
theorem chartScalarOnTriple_chartRatio_lj
    (i l j : Fin (d + 1)) :
    chartScalarOnTriple k d i l j
        (chartRatioElement k d l j) =
      chartTripleAwayJK k d i l j := by
  rw [chartScalarOnTriple_eq_restrict_pairJL,
    chartScalarOnPair_chartRatio]
  let hT := chartTripleOpen_eq_tripleOpen k d i l j
  let hB := standardChart_inf_eq_productBasicOpen k d l j
  let hChart := chartTriple_le_pairJL k d i l j
  let hHom := tripleOpen_le_jk k d i l j
  let E :=
    eqToIso (congrArg (fun U => Γ(scheme k d, U)) hT)
  apply E.commRingCatIsoToRingEquiv.injective
  have ht :=
    presheaf_map_eqToIso_apply (scheme k d).presheaf
      hT hB hChart hHom
      (chartPairAwaySection k d l j)
  rw [chartPairAwaySection,
    Iso.inv_hom_id_apply] at ht
  change
    E.hom
        ((scheme k d).presheaf.map
          (homOfLE hChart).op
          ((eqToIso (congrArg
            (fun U => Γ(scheme k d, U)) hB)).inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k l * coordinate k j)
              (awayFraction k d l j)))) =
      E.hom
        ((eqToIso (congrArg
          (fun U => Γ(scheme k d, U)) hT)).inv
          (Proj.awayToSection (homogeneousGrading k d)
            (tripleCoordinate k d i l j)
            (tripleAwayJK k d i l j)))
  rw [ht]
  rw [ambientAwaySection_restrict k d
    (coordinate k l * coordinate k j) (coordinate k i)
    (coordinate_mem_degreeOne k i)
    (tripleCoordinate k d i l j)
    (by ring) hHom (awayFraction k d l j)]
  change
    Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayJK k d i l j) =
      E.hom (E.inv
        (Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayJK k d i l j)))
  exact (E.inv_hom_id_apply _).symm

/-- The base-`j` chart scalar `Xᵢ/Xⱼ` is the `IK` homogeneous fraction
on the common triple overlap. -/
theorem chartScalarOnTriple_chartRatio_ij
    (i l j : Fin (d + 1)) :
    chartScalarOnTriple k d i l j
        (chartRatioElement k d i j) =
      chartTripleAwayIK k d i l j := by
  rw [chartScalarOnTriple_eq_restrict_pairJI,
    chartScalarOnPair_chartRatio]
  let hT := chartTripleOpen_eq_tripleOpen k d i l j
  let hB := standardChart_inf_eq_productBasicOpen k d i j
  let hChart := chartTriple_le_pairJI k d i l j
  let hHom := tripleOpen_le_ik k d i l j
  let E :=
    eqToIso (congrArg (fun U => Γ(scheme k d, U)) hT)
  apply E.commRingCatIsoToRingEquiv.injective
  have ht :=
    presheaf_map_eqToIso_apply (scheme k d).presheaf
      hT hB hChart hHom
      (chartPairAwaySection k d i j)
  rw [chartPairAwaySection,
    Iso.inv_hom_id_apply] at ht
  change
    E.hom
        ((scheme k d).presheaf.map
          (homOfLE hChart).op
          ((eqToIso (congrArg
            (fun U => Γ(scheme k d, U)) hB)).inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k i * coordinate k j)
              (awayFraction k d i j)))) =
      E.hom
        ((eqToIso (congrArg
          (fun U => Γ(scheme k d, U)) hT)).inv
          (Proj.awayToSection (homogeneousGrading k d)
            (tripleCoordinate k d i l j)
            (tripleAwayIK k d i l j)))
  rw [ht]
  rw [ambientAwaySection_restrict k d
    (coordinate k i * coordinate k j) (coordinate k l)
    (coordinate_mem_degreeOne k l)
    (tripleCoordinate k d i l j)
    (by ring) hHom (awayFraction k d i j)]
  change
    Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayIK k d i l j) =
      E.hom (E.inv
        (Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayIK k d i l j)))
  exact (E.inv_hom_id_apply _).symm

/-- Rebracketing and rotating the three standard opens changes the
base-chart presentation of the same ambient triple intersection. -/
lemma chartTripleOpen_fromL_eq
    (i l j : Fin (d + 1)) :
    standardChart k l ⊓
        (standardChart k j ⊓ standardChart k i) =
      standardChart k j ⊓
        (standardChart k i ⊓ standardChart k l) := by
  ac_rfl

/-- Inclusion of the common triple intersection into the `l,i`
pairwise intersection. -/
lemma chartTriple_le_pairLI
    (i l j : Fin (d + 1)) :
    standardChart k j ⊓
          (standardChart k i ⊓ standardChart k l) ≤
      standardChart k l ⊓ standardChart k i :=
  le_inf (inf_le_right.trans inf_le_right)
    (inf_le_right.trans inf_le_left)

/-- A scalar transported from chart `l`, re-expressed on the ambient
triple intersection whose base presentation is chart `j`. -/
def chartScalarFromLOnTriple
    (i l j : Fin (d + 1))
    (r : chartRing k d l) :
    Γ(scheme k d, standardChart k j ⊓
      (standardChart k i ⊓ standardChart k l)) :=
  (eqToIso (congrArg (fun U => Γ(scheme k d, U))
    (chartTripleOpen_fromL_eq k d i l j))).hom
      (chartScalarOnTriple k d j i l r)

/-- Transporting a scalar from chart `l` to the common triple overlap
is the same as transporting it to the `l,i` pairwise overlap and then
restricting. -/
theorem chartScalarFromLOnTriple_eq_restrict_pairLI
    (i l j : Fin (d + 1))
    (r : chartRing k d l) :
    chartScalarFromLOnTriple k d i l j r =
      (scheme k d).presheaf.map
        (homOfLE (chartTriple_le_pairLI k d i l j)).op
        (chartScalarOnPair k d i l r) := by
  rw [chartScalarFromLOnTriple,
    chartScalarOnTriple_eq_restrict_pairJL]
  let hRotate := chartTripleOpen_fromL_eq k d i l j
  let hNative := chartTriple_le_pairJL k d j i l
  let hCommon := chartTriple_le_pairLI k d i l j
  exact
    presheaf_map_eqToIso_apply (scheme k d).presheaf
      hRotate
      (rfl :
        standardChart k l ⊓ standardChart k i =
          standardChart k l ⊓ standardChart k i)
      hNative hCommon
      (chartScalarOnPair k d i l r)

/-- The chart-`l` scalar `Xᵢ/Xₗ`, transported to the common ambient
triple overlap, is the `IJ` homogeneous fraction. -/
theorem chartScalarFromLOnTriple_chartRatio_il
    (i l j : Fin (d + 1)) :
    chartScalarFromLOnTriple k d i l j
        (chartRatioElement k d i l) =
      chartTripleAwayIJ k d i l j := by
  rw [chartScalarFromLOnTriple,
    chartScalarOnTriple_eq_restrict_pairJL,
    chartScalarOnPair_chartRatio]
  let hRotate := chartTripleOpen_fromL_eq k d i l j
  let hNative := chartTriple_le_pairJL k d j i l
  let hCommon := chartTriple_le_pairLI k d i l j
  let hT := chartTripleOpen_eq_tripleOpen k d i l j
  let hB := standardChart_inf_eq_productBasicOpen k d i l
  let hHom := tripleOpen_le_ij k d i l j
  let E :=
    eqToIso (congrArg (fun U => Γ(scheme k d, U)) hT)
  have hrotate :
      (eqToIso (congrArg
        (fun U => Γ(scheme k d, U)) hRotate)).hom
          ((scheme k d).presheaf.map
            (homOfLE hNative).op
            (chartPairAwaySection k d i l)) =
        (scheme k d).presheaf.map
          (homOfLE hCommon).op
          (chartPairAwaySection k d i l) := by
    have h :=
      presheaf_map_eqToIso_apply (scheme k d).presheaf
        hRotate (rfl :
          standardChart k l ⊓ standardChart k i =
            standardChart k l ⊓ standardChart k i)
        hNative hCommon
        (chartPairAwaySection k d i l)
    simpa using h
  rw [hrotate]
  apply E.commRingCatIsoToRingEquiv.injective
  have ht :=
    presheaf_map_eqToIso_apply (scheme k d).presheaf
      hT hB hCommon hHom
      (chartPairAwaySection k d i l)
  rw [chartPairAwaySection,
    Iso.inv_hom_id_apply] at ht
  change
    E.hom
        ((scheme k d).presheaf.map
          (homOfLE hCommon).op
          ((eqToIso (congrArg
            (fun U => Γ(scheme k d, U)) hB)).inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k i * coordinate k l)
              (awayFraction k d i l)))) =
      E.hom
        ((eqToIso (congrArg
          (fun U => Γ(scheme k d, U)) hT)).inv
          (Proj.awayToSection (homogeneousGrading k d)
            (tripleCoordinate k d i l j)
            (tripleAwayIJ k d i l j)))
  rw [ht]
  rw [ambientAwaySection_restrict k d
    (coordinate k i * coordinate k l) (coordinate k j)
    (coordinate_mem_degreeOne k j)
    (tripleCoordinate k d i l j)
    rfl hHom (awayFraction k d i l)]
  change
    Proj.awayToSection (homogeneousGrading k d)
        (tripleCoordinate k d i l j)
        (tripleAwayIJ k d i l j) =
      E.hom (E.inv
        (Proj.awayToSection (homogeneousGrading k d)
          (tripleCoordinate k d i l j)
          (tripleAwayIJ k d i l j)))
  exact (E.inv_hom_id_apply _).symm

/-- The three affine ambient scalar sections satisfy the coordinate-ratio
cocycle. -/
theorem chartTripleAway_mul
    (i l j : Fin (d + 1)) :
    chartTripleAwayIJ k d i l j *
        chartTripleAwayJK k d i l j =
      chartTripleAwayIK k d i l j := by
  rw [chartTripleAwayIJ, chartTripleAwayJK,
    chartTripleAwayIK, ← map_mul, ← map_mul,
    tripleAway_mul]

/-- The affine regular functions satisfy
`(Xₗ/Xⱼ) (Xᵢ/Xₗ) = Xᵢ/Xⱼ` after transport to the common triple
overlap. -/
theorem chartScalarOnTriple_cocycle
    (i l j : Fin (d + 1)) :
    chartScalarOnTriple k d i l j
          (chartRatioElement k d l j) *
        chartScalarFromLOnTriple k d i l j
          (chartRatioElement k d i l) =
      chartScalarOnTriple k d i l j
        (chartRatioElement k d i j) := by
  rw [chartScalarOnTriple_chartRatio_lj,
    chartScalarFromLOnTriple_chartRatio_il,
    chartScalarOnTriple_chartRatio_ij,
    mul_comm]
  exact chartTripleAway_mul k d i l j

/-- Transport of chart scalars to a triple overlap preserves powers. -/
theorem chartScalarOnTriple_pow
    (i l j : Fin (d + 1))
    (r : chartRing k d j) (N : ℕ) :
    chartScalarOnTriple k d i l j (r ^ N) =
      chartScalarOnTriple k d i l j r ^ N := by
  dsimp only [chartScalarOnTriple]
  simp only [map_pow]

/-- The cross-base scalar transport from chart `l` preserves powers. -/
theorem chartScalarFromLOnTriple_pow
    (i l j : Fin (d + 1))
    (r : chartRing k d l) (N : ℕ) :
    chartScalarFromLOnTriple k d i l j (r ^ N) =
      chartScalarFromLOnTriple k d i l j r ^ N := by
  rw [chartScalarFromLOnTriple,
    chartScalarFromLOnTriple, chartScalarOnTriple_pow,
    map_pow]

/-- Power form of the affine scalar cocycle, used when a common power
clears every chartwise extension defect. -/
theorem chartScalarOnTriple_cocycle_pow
    (N : ℕ) (i l j : Fin (d + 1)) :
    chartScalarOnTriple k d i l j
          (chartRatioElement k d l j) ^ N *
        chartScalarFromLOnTriple k d i l j
          (chartRatioElement k d i l) ^ N =
      chartScalarOnTriple k d i l j
        (chartRatioElement k d i j) ^ N := by
  rw [← mul_pow, chartScalarOnTriple_cocycle]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
