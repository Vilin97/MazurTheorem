/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCubicChartDensity
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Relative dimension of a smooth Weierstrass cubic

This file proves directly from the two explicit affine charts that the structure morphism of a
smooth projective Weierstrass cubic over a field has relative dimension one.  Each chart is a
plane hypersurface.  Its two partial derivatives generate the unit ideal because geometric
nonsingularity rules out a common zero over every residue-field extension.  Localizing at either
derivative gives an explicit standard-smooth presentation of relative dimension one, and the two
chart calculations glue over the canonical covering open cover.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

variable {K : Type u} [Field K]

private abbrev HypersurfaceIdeal
    (R : Type u) [CommRing R] (f : MvPolynomial (Fin 2) R) :=
  Ideal.span (Set.range fun _ : Unit ↦ f)

private abbrev HypersurfaceRing
    (R : Type u) [CommRing R] (f : MvPolynomial (Fin 2) R) :=
  MvPolynomial (Fin 2) R ⧸ HypersurfaceIdeal R f

private noncomputable def hypersurfacePrePresentation
    (R : Type u) [CommRing R] (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    Algebra.PreSubmersivePresentation R (HypersurfaceRing R f) (Fin 2) Unit :=
  Algebra.PreSubmersivePresentation.naive
    (v := fun _ : Unit ↦ f) (fun _ ↦ i)
      (fun {_ _} _ ↦ Subsingleton.elim _ _)

private lemma hypersurfacePrePresentation_jacobian
    (R : Type u) [CommRing R] (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    (hypersurfacePrePresentation R f i).jacobian =
      Ideal.Quotient.mk (HypersurfaceIdeal R f) (MvPolynomial.pderiv i f) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    hypersurfacePrePresentation]
  rfl

private lemma localized_hypersurface_isStandardSmoothOfRelativeDimension
    (R : Type u) [CommRing R] (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    let S := HypersurfaceRing R f
    let d : S := Ideal.Quotient.mk (HypersurfaceIdeal R f) (MvPolynomial.pderiv i f)
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((algebraMap S (Localization.Away d)).comp (algebraMap R S)) := by
  dsimp only
  let S := HypersurfaceRing R f
  let d : S := Ideal.Quotient.mk (HypersurfaceIdeal R f) (MvPolynomial.pderiv i f)
  let T := Localization.Away d
  let P := hypersurfacePrePresentation R f i
  let Q := Algebra.PreSubmersivePresentation.localizationAway T d
  let PQ := Q.comp P
  let SP : Algebra.SubmersivePresentation R T (Unit ⊕ Fin 2) (Unit ⊕ Unit) :=
    { toPreSubmersivePresentation := PQ
      jacobian_isUnit := by
        dsimp only [PQ, Q, P]
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          hypersurfacePrePresentation_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian]
        rw [Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have hA : Algebra.IsStandardSmoothOfRelativeDimension 1 R T :=
    SP.isStandardSmoothOfRelativeDimension (by
      change Nat.card (Unit ⊕ Fin 2) - Nat.card (Unit ⊕ Unit) = 1
      simp)
  have hRing : RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap R T) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr hA
  simpa only [IsScalarTower.algebraMap_eq R S T] using hRing

private lemma hypersurface_locally_isStandardSmoothOfRelativeDimension_one
    (R : Type u) [CommRing R] (f : MvPolynomial (Fin 2) R)
    (hspan : Ideal.span (Set.range fun i : Fin 2 ↦
      Ideal.Quotient.mk (HypersurfaceIdeal R f) (MvPolynomial.pderiv i f)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (HypersurfaceRing R f)) := by
  refine ⟨Set.range (fun i : Fin 2 ↦
    Ideal.Quotient.mk (HypersurfaceIdeal R f) (MvPolynomial.pderiv i f)), hspan, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact localized_hypersurface_isStandardSmoothOfRelativeDimension R f i

private lemma hypersurface_derivatives_span_top_of_geometric_nonsingular
    (R : Type u) [Field R] (f : MvPolynomial (Fin 2) R)
    (h : ∀ (L : Type u) [Field L] (g : R →+* L) (x : Fin 2 → L),
      MvPolynomial.eval₂ g x f = 0 →
        ∃ i : Fin 2, MvPolynomial.eval₂ g x (MvPolynomial.pderiv i f) ≠ 0) :
    Ideal.span (Set.range fun i : Fin 2 ↦
      Ideal.Quotient.mk (HypersurfaceIdeal R f) (MvPolynomial.pderiv i f)) = ⊤ := by
  by_contra htop
  let S := HypersurfaceRing R f
  let J : Ideal S := Ideal.span (Set.range fun i : Fin 2 ↦
    Ideal.Quotient.mk (HypersurfaceIdeal R f) (MvPolynomial.pderiv i f))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J htop
  let L := S ⧸ M
  letI : Field L := Ideal.Quotient.field M
  let q₁ : MvPolynomial (Fin 2) R →+* S := Ideal.Quotient.mk (HypersurfaceIdeal R f)
  let q₂ : S →+* L := Ideal.Quotient.mk M
  let g : R →+* L := q₂.comp (q₁.comp (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R))
  let x : Fin 2 → L := fun i ↦ q₂ (q₁ (MvPolynomial.X i))
  have heval : MvPolynomial.eval₂Hom g x = q₂.comp q₁ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [g, q₁, q₂]
    · intro i
      simp [x]
  have hfzero : MvPolynomial.eval₂ g x f = 0 := by
    change (MvPolynomial.eval₂Hom g x) f = 0
    rw [heval]
    change q₂ (q₁ f) = 0
    have hfmem : f ∈ HypersurfaceIdeal R f :=
      Ideal.subset_span ⟨(), rfl⟩
    rw [show q₁ f = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hfmem, map_zero]
  obtain ⟨i, hi⟩ := h L g x hfzero
  apply hi
  change (MvPolynomial.eval₂Hom g x) (MvPolynomial.pderiv i f) = 0
  rw [heval]
  change q₂ (q₁ (MvPolynomial.pderiv i f)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hJM
  exact Ideal.subset_span ⟨i, rfl⟩

private def affineChartMvEquation (W : WeierstrassCurve K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 +
    MvPolynomial.C W.a₁ * MvPolynomial.X 1 * MvPolynomial.X 0 +
    MvPolynomial.C W.a₃ * MvPolynomial.X 0 -
    (MvPolynomial.X 1 ^ 3 +
      MvPolynomial.C W.a₂ * MvPolynomial.X 1 ^ 2 +
      MvPolynomial.C W.a₄ * MvPolynomial.X 1 + MvPolynomial.C W.a₆)

private lemma affineChartMvEquation_geometrically_nonsingular
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∀ (L : Type u) [Field L] (g : K →+* L) (x : Fin 2 → L),
      MvPolynomial.eval₂ g x (affineChartMvEquation W) = 0 →
        ∃ i : Fin 2,
          MvPolynomial.eval₂ g x
            (MvPolynomial.pderiv i (affineChartMvEquation W)) ≠ 0 := by
  intro L _ g x heq
  have hEquation : (W.map g).toAffine.Equation (x 1) (x 0) := by
    rw [WeierstrassCurve.Affine.equation_iff']
    simpa [affineChartMvEquation] using heq
  have hns := ((W.map g).toAffine.equation_iff_nonsingular).mp hEquation
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  rcases hns.2 with hx | hy
  · refine ⟨1, ?_⟩
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄] at hx
    simp [affineChartMvEquation]
    intro hzero
    apply hx
    linear_combination hzero
  · refine ⟨0, ?_⟩
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at hy
    simpa [affineChartMvEquation] using hy

private def infinityChartMvEquation (W : WeierstrassCurve K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 +
    MvPolynomial.C W.a₁ * MvPolynomial.X 1 * MvPolynomial.X 0 +
    MvPolynomial.C W.a₃ * MvPolynomial.X 0 ^ 2 -
    (MvPolynomial.X 1 ^ 3 +
      MvPolynomial.C W.a₂ * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 0 +
      MvPolynomial.C W.a₄ * MvPolynomial.X 1 * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C W.a₆ * MvPolynomial.X 0 ^ 3)

private lemma infinityChartMvEquation_geometrically_nonsingular
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∀ (L : Type u) [Field L] (g : K →+* L) (x : Fin 2 → L),
      MvPolynomial.eval₂ g x (infinityChartMvEquation W) = 0 →
        ∃ i : Fin 2,
          MvPolynomial.eval₂ g x
            (MvPolynomial.pderiv i (infinityChartMvEquation W)) ≠ 0 := by
  intro L _ g x heq
  let P : Fin 3 → L := ![x 1, 1, x 0]
  have hEquation : (W.map g).toProjective.Equation P := by
    rw [WeierstrassCurve.Projective.equation_iff]
    simpa [P, infinityChartMvEquation] using heq
  have hns : (W.map g).toProjective.Nonsingular P := by
    by_cases hz : P 2 = 0
    · have hx : P 0 = 0 :=
        WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero hEquation hz
      have hP : P = ![0, 1, 0] := by
        funext i
        fin_cases i
        · exact hx
        · rfl
        · exact hz
      rw [hP]
      exact WeierstrassCurve.Projective.nonsingular_zero
    · rw [WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hz]
      exact (W.map g).toAffine.equation_iff_nonsingular.mp
        (WeierstrassCurve.Projective.equation_of_Z_ne_zero hz |>.mp hEquation)
  by_cases hx : MvPolynomial.eval P (W.map g).toProjective.polynomialX ≠ 0
  · refine ⟨1, ?_⟩
    simp only [WeierstrassCurve.Projective.eval_polynomialX] at hx
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄] at hx
    simp [infinityChartMvEquation]
    simp [P] at hx
    intro hzero
    apply hx
    linear_combination hzero
  by_cases hz : MvPolynomial.eval P (W.map g).toProjective.polynomialZ ≠ 0
  · refine ⟨0, ?_⟩
    simp only [WeierstrassCurve.Projective.eval_polynomialZ] at hz
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] at hz
    simp [infinityChartMvEquation]
    simp [P] at hz
    intro hzero
    apply hz
    linear_combination hzero
  have hderivs :
      MvPolynomial.eval P (W.map g).toProjective.polynomialX ≠ 0 ∨
      MvPolynomial.eval P (W.map g).toProjective.polynomialY ≠ 0 ∨
      MvPolynomial.eval P (W.map g).toProjective.polynomialZ ≠ 0 := hns.2
  rcases hderivs with hbad | hbad | hbad
  · exact (hx hbad).elim
  · have hrel := (W.map g).toProjective.polynomial_relation P
    have hfzero : MvPolynomial.eval P (W.map g).toProjective.polynomial = 0 := hEquation
    have hxzero : MvPolynomial.eval P (W.map g).toProjective.polynomialX = 0 :=
      not_ne_iff.mp hx
    have hzzero : MvPolynomial.eval P (W.map g).toProjective.polynomialZ = 0 :=
      not_ne_iff.mp hz
    rw [hfzero, hxzero, hzzero] at hrel
    have hyzero : MvPolynomial.eval P (W.map g).toProjective.polynomialY = 0 := by
      simpa [P] using hrel.symm
    exact (hbad hyzero).elim
  · exact (hz hbad).elim

private def coveringChartMvEquation (W : WeierstrassCurve K) :
    Bool → MvPolynomial (Fin 2) K
  | false => infinityChartMvEquation W
  | true => affineChartMvEquation W

private noncomputable def coveringChartPolynomialRingEquiv (b : Bool) :
    MvPolynomial (Fin 2) K ≃+* coveringChartRing K b :=
  coordinateChartPolynomialEquiv (K := K) (coveringCoordinate b)

private lemma coveringChartPolynomialAlgEquiv_equation
    (W : WeierstrassCurve K) (b : Bool) :
    coveringChartPolynomialRingEquiv (K := K) b (coveringChartMvEquation W b) =
      coveringChartEquation W b := by
  cases b
  · change coordinateChartPolynomialEquiv (K := K) 1 (infinityChartMvEquation W) =
      infinityLocalizedEquation W
    rw [infinityLocalizedEquation_explicit]
    simp [infinityChartMvEquation, Equiv.swap_apply_def]
  · change coordinateChartPolynomialEquiv (K := K) 2 (affineChartMvEquation W) =
      standardChartEquation W
    rw [standardChartEquation_eq_affineToStandardChart]
    simp [affineChartMvEquation, WeierstrassCurve.Affine.polynomial]
    ring

private noncomputable def coveringChartQuotientRingEquiv
    (W : WeierstrassCurve K) (b : Bool) :
    HypersurfaceRing K (coveringChartMvEquation W b) ≃+*
      coveringChartCoordinateRing W b :=
  Ideal.quotientEquiv
    (HypersurfaceIdeal K (coveringChartMvEquation W b))
    (coveringChartIdeal W b) (coveringChartPolynomialRingEquiv (K := K) b) (by
      rw [HypersurfaceIdeal, coveringChartIdeal, Ideal.map_span]
      simp only [Set.range_const, Set.image_singleton]
      exact congrArg (fun z ↦ Ideal.span {z})
        (coveringChartPolynomialAlgEquiv_equation W b).symm)

private theorem coveringChartQuotientRingEquiv_comp_algebraMap
    (W : WeierstrassCurve K) (b : Bool) :
    (coveringChartQuotientRingEquiv W b).toRingHom.comp
        (algebraMap K (HypersurfaceRing K (coveringChartMvEquation W b))) =
      coveringChartStructureRingHom W b := by
  ext a
  simp [coveringChartQuotientRingEquiv, coveringChartStructureRingHom,
    coveringChartPolynomialRingEquiv]

private lemma coveringChartStructureRingHom_locally_relativeDimension_one
    (W : WeierstrassCurve K) [W.IsElliptic] (b : Bool) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (coveringChartStructureRingHom W b) := by
  let f := coveringChartMvEquation W b
  have hgeom : ∀ (L : Type u) [Field L] (g : K →+* L) (x : Fin 2 → L),
      MvPolynomial.eval₂ g x f = 0 →
        ∃ i : Fin 2, MvPolynomial.eval₂ g x (MvPolynomial.pderiv i f) ≠ 0 := by
    cases b
    · exact infinityChartMvEquation_geometrically_nonsingular W
    · exact affineChartMvEquation_geometrically_nonsingular W
  have hspan :=
    hypersurface_derivatives_span_top_of_geometric_nonsingular K f hgeom
  have hlocal :=
    hypersurface_locally_isStandardSmoothOfRelativeDimension_one K f hspan
  have htransport :=
    (RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).1
        (algebraMap K (HypersurfaceRing K f))
        (coveringChartQuotientRingEquiv W b) hlocal
  rw [coveringChartQuotientRingEquiv_comp_algebraMap] at htransport
  exact htransport

private lemma coveringChart_comp_structureMap_relativeDimension_one
    (W : WeierstrassCurve K) [W.IsElliptic] (b : Bool) :
    SmoothOfRelativeDimension 1 (coveringChartMap W b ≫ structureMap W) := by
  rw [coveringChartMap_comp_structureMap]
  exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
    (coveringChartStructureRingHom_locally_relativeDimension_one W b)

/-- The structure morphism of a smooth projective Weierstrass cubic over a field is smooth of
relative dimension one. -/
instance structureMap_smoothOfRelativeDimension_one
    (W : WeierstrassCurve K) [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (structureMap W) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover
    (P := @SmoothOfRelativeDimension 1) (coveringChartsOpenCover W)]
  intro b
  exact coveringChart_comp_structureMap_relativeDimension_one W b

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
