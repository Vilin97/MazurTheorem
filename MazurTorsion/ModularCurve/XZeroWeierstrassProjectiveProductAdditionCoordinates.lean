/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductUniversalPoints
import MazurTorsion.ModularCurve.XZeroWeierstrassRelativeDimension
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Homogeneous addition coordinates on projective Weierstrass pair charts

This file evaluates the homogeneous Weierstrass addition polynomials on the
universal inputs of every projective-pair chart.  It first proves that the
tensor-product chart rings are domains for an elliptic Weierstrass curve, then
uses the fraction field to verify that the universal addition triple satisfies
the homogeneous cubic equation.

The resulting triple is allowed to vanish on its base locus.  Later local
addition charts must prove a selected output coordinate invertible (or replace
the triple by a compatible doubling formula) before turning these coordinates
into a scheme morphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped WeierstrassCurve.Projective

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- For an elliptic cubic, every affine member of the projective-pair atlas has
an integral-domain coordinate ring. -/
noncomputable instance projectivePairChartCoordinateRing_isDomain
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    IsDomain (projectivePairChartCoordinateRing W ij) := by
  apply (affine_isIntegral_iff
    (.of (projectivePairChartCoordinateRing W ij))).mp
  letI : IsIntegral (scheme W) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (structureMap W)
  letI : Flat (structureMap W) := by infer_instance
  letI : UniversallyOpen (structureMap W) := by infer_instance
  letI : LocallyOfFiniteType (structureMap W) := by infer_instance
  letI : IsLocallyNoetherian (scheme W) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap W)
  letI : IsIntegral (projectivePair W) := by infer_instance
  letI : Nonempty (projectivePairChartScheme W ij) := by infer_instance
  letI : IsIntegral (projectivePairChartScheme W ij) :=
    isIntegral_of_isOpenImmersion (projectivePairChartMap W ij)
  exact IsIntegral.of_isIso (projectivePairChartIsoSpecTensor W ij).hom

private lemma nonsingular_of_equation_of_ne_zero
    {F : Type u} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
    {P : Fin 3 → F} (hP : W.toProjective.Equation P) (hP0 : P ≠ 0) :
    W.toProjective.Nonsingular P := by
  by_cases hPz : P (2 : Fin 3) = 0
  · have hPx : P (0 : Fin 3) = 0 :=
      W.toProjective.X_eq_zero_of_Z_eq_zero hP hPz
    have hPy : P (1 : Fin 3) ≠ 0 := by
      intro hPy
      apply hP0
      funext i
      fin_cases i
      · simpa using hPx
      · simpa using hPy
      · simpa using hPz
    rw [W.toProjective.nonsingular_of_Z_eq_zero hPz]
    refine ⟨hP, Or.inr ?_⟩
    simpa [hPx] using pow_ne_zero 2 hPy
  · rw [W.toProjective.nonsingular_of_Z_ne_zero hPz,
      ← W.toAffine.equation_iff_nonsingular,
      ← W.toProjective.equation_of_Z_ne_zero hPz]
    exact hP

private theorem addXYZ_equation_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    {P Q : Fin 3 → R}
    (hP : W.toProjective.Equation P) (hQ : W.toProjective.Equation Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    W.toProjective.Equation (W.toProjective.addXYZ P Q) := by
  let F := FractionRing R
  let ι : R →+* F := algebraMap R F
  let PF : Fin 3 → F := ι ∘ P
  let QF : Fin 3 → F := ι ∘ Q
  have hι : Function.Injective ι := IsFractionRing.injective R F
  have hPF0 : PF ≠ 0 := by
    intro h
    apply hP0
    funext i
    apply hι
    simpa [PF, Function.comp_apply] using congrFun h i
  have hQF0 : QF ≠ 0 := by
    intro h
    apply hQ0
    funext i
    apply hι
    simpa [QF, Function.comp_apply] using congrFun h i
  have hPF : (W.map ι).toProjective.Equation PF := by
    simpa [PF] using hP.map ι
  have hQF : (W.map ι).toProjective.Equation QF := by
    simpa [QF] using hQ.map ι
  have hPFns : (W.map ι).toProjective.Nonsingular PF :=
    nonsingular_of_equation_of_ne_zero (W.map ι) hPF hPF0
  have hQFns : (W.map ι).toProjective.Nonsingular QF :=
    nonsingular_of_equation_of_ne_zero (W.map ι) hQF hQF0
  have haddF : (W.map ι).toProjective.Equation
      ((W.map ι).toProjective.addXYZ PF QF) := by
    by_cases hPQ : PF ≈ QF
    · rcases hPQ with ⟨v, hv⟩
      simp only [Units.smul_def] at hv
      rw [← hv]
      have hformula := (W.map ι).toProjective.addXYZ_smul
        QF QF (v : F) (1 : F)
      simp only [one_smul, mul_one] at hformula
      rw [hformula, WeierstrassCurve.Projective.addXYZ_self]
      simp [WeierstrassCurve.Projective.equation_iff]
    · have hadd := WeierstrassCurve.Projective.nonsingular_add hPFns hQFns
      rw [WeierstrassCurve.Projective.add_of_not_equiv hPQ] at hadd
      exact hadd.1
  have hmapped : (W.map ι).toProjective.Equation
      (ι ∘ W.toProjective.addXYZ P Q) := by
    rw [← WeierstrassCurve.Projective.map_addXYZ]
    exact haddF
  exact (W.toProjective.map_equation hι
    (W.toProjective.addXYZ P Q)).mp hmapped

private theorem dblXYZ_equation_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    {P : Fin 3 → R} (hP : W.toProjective.Equation P) (hP0 : P ≠ 0) :
    W.toProjective.Equation (W.toProjective.dblXYZ P) := by
  let F := FractionRing R
  let ι : R →+* F := algebraMap R F
  let PF : Fin 3 → F := ι ∘ P
  have hι : Function.Injective ι := IsFractionRing.injective R F
  have hPF0 : PF ≠ 0 := by
    intro h
    apply hP0
    funext i
    apply hι
    simpa [PF, Function.comp_apply] using congrFun h i
  have hPF : (W.map ι).toProjective.Equation PF := by
    simpa [PF] using hP.map ι
  have hPFns : (W.map ι).toProjective.Nonsingular PF :=
    nonsingular_of_equation_of_ne_zero (W.map ι) hPF hPF0
  have hdblF : (W.map ι).toProjective.Equation
      ((W.map ι).toProjective.dblXYZ PF) := by
    have hsum := WeierstrassCurve.Projective.nonsingular_add hPFns hPFns
    rw [WeierstrassCurve.Projective.add_self] at hsum
    exact hsum.1
  have hmapped : (W.map ι).toProjective.Equation
      (ι ∘ W.toProjective.dblXYZ P) := by
    rw [← WeierstrassCurve.Projective.map_dblXYZ]
    exact hdblF
  exact (W.toProjective.map_equation hι
    (W.toProjective.dblXYZ P)).mp hmapped

/-- The elliptic curve after extending scalars to a projective-pair chart
ring. -/
abbrev projectivePairChartMappedCurve
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    WeierstrassCurve (projectivePairChartCoordinateRing W ij) :=
  W.map (algebraMap K (projectivePairChartCoordinateRing W ij))

/-- The normalized first universal input is nonzero over every elliptic pair
chart. -/
theorem projectivePairChartFirstUniversalPoint_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    projectivePairChartFirstUniversalPoint W ij ≠ 0 := by
  letI : Nontrivial (projectivePairChartCoordinateRing W ij) :=
    (projectivePairChartCoordinateRing_isDomain W ij).toNontrivial
  intro h
  have hz : projectivePairChartFirstUniversalPoint W ij
      (coveringCoordinate ij.1) = 0 := congrFun h (coveringCoordinate ij.1)
  have hone : (1 : projectivePairChartCoordinateRing W ij) = 0 :=
    (projectivePairChartFirstUniversalPoint_normalized W ij).symm.trans hz
  exact one_ne_zero hone

/-- The normalized second universal input is nonzero over every elliptic pair
chart. -/
theorem projectivePairChartSecondUniversalPoint_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    projectivePairChartSecondUniversalPoint W ij ≠ 0 := by
  letI : Nontrivial (projectivePairChartCoordinateRing W ij) :=
    (projectivePairChartCoordinateRing_isDomain W ij).toNontrivial
  intro h
  have hz : projectivePairChartSecondUniversalPoint W ij
      (coveringCoordinate ij.2) = 0 := congrFun h (coveringCoordinate ij.2)
  have hone : (1 : projectivePairChartCoordinateRing W ij) = 0 :=
    (projectivePairChartSecondUniversalPoint_normalized W ij).symm.trans hz
  exact one_ne_zero hone

/-- The raw homogeneous secant-addition triple evaluated on the two universal
inputs of a projective-pair chart.  This is the polynomial design boundary;
the equation and denominator identities below are its first downstream
consumers. -/
noncomputable def projectivePairChartAdditionCoordinates
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Fin 3 → projectivePairChartCoordinateRing W ij :=
  (projectivePairChartMappedCurve W ij).toProjective.addXYZ
    (projectivePairChartFirstUniversalPoint W ij)
    (projectivePairChartSecondUniversalPoint W ij)

@[simp]
theorem projectivePairChartAdditionCoordinates_X
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartAdditionCoordinates W ij (0 : Fin 3) =
      (projectivePairChartMappedCurve W ij).toProjective.addX
        (projectivePairChartFirstUniversalPoint W ij)
        (projectivePairChartSecondUniversalPoint W ij) :=
  rfl

@[simp]
theorem projectivePairChartAdditionCoordinates_Y
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartAdditionCoordinates W ij (1 : Fin 3) =
      (projectivePairChartMappedCurve W ij).toProjective.addY
        (projectivePairChartFirstUniversalPoint W ij)
        (projectivePairChartSecondUniversalPoint W ij) :=
  rfl

@[simp]
theorem projectivePairChartAdditionCoordinates_Z
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartAdditionCoordinates W ij (2 : Fin 3) =
      (projectivePairChartMappedCurve W ij).toProjective.addZ
        (projectivePairChartFirstUniversalPoint W ij)
        (projectivePairChartSecondUniversalPoint W ij) :=
  rfl

/-- The evaluated secant-addition triple satisfies the mapped homogeneous
cubic equation.  It may still be the zero triple along the diagonal base
locus. -/
theorem projectivePairChartAdditionCoordinates_equation
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    (projectivePairChartMappedCurve W ij).toProjective.Equation
      (projectivePairChartAdditionCoordinates W ij) := by
  apply addXYZ_equation_of_isDomain
  · exact projectivePairChartFirstUniversalPoint_equation W ij
  · exact projectivePairChartSecondUniversalPoint_equation W ij
  · exact projectivePairChartFirstUniversalPoint_ne_zero W ij
  · exact projectivePairChartSecondUniversalPoint_ne_zero W ij

/-- The output `Z` polynomial times the two input `Z` coordinates is the cube
of the cross-multiplied difference of the two input `X` coordinates.  This is
the denominator identity used by the future secant principal-open chart. -/
theorem projectivePairChartAdditionCoordinates_Z_mul_input_Z
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
        (projectivePairChartFirstUniversalPoint W ij (2 : Fin 3) *
          projectivePairChartSecondUniversalPoint W ij (2 : Fin 3)) =
      (projectivePairChartFirstUniversalPoint W ij (0 : Fin 3) *
          projectivePairChartSecondUniversalPoint W ij (2 : Fin 3) -
        projectivePairChartSecondUniversalPoint W ij (0 : Fin 3) *
          projectivePairChartFirstUniversalPoint W ij (2 : Fin 3)) ^ 3 := by
  rw [projectivePairChartAdditionCoordinates_Z]
  exact (projectivePairChartMappedCurve W ij).toProjective.addZ_eq'
    (projectivePairChartFirstUniversalPoint_equation W ij)
    (projectivePairChartSecondUniversalPoint_equation W ij)

/-- The homogeneous doubling triple of the first universal input.  It is the
polynomial replacement for the secant triple on the diagonal base locus. -/
noncomputable def projectivePairChartFirstDoublingCoordinates
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Fin 3 → projectivePairChartCoordinateRing W ij :=
  (projectivePairChartMappedCurve W ij).toProjective.dblXYZ
    (projectivePairChartFirstUniversalPoint W ij)

/-- The first universal doubling triple also satisfies the mapped cubic
equation. -/
theorem projectivePairChartFirstDoublingCoordinates_equation
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    (projectivePairChartMappedCurve W ij).toProjective.Equation
      (projectivePairChartFirstDoublingCoordinates W ij) := by
  apply dblXYZ_equation_of_isDomain
  · exact projectivePairChartFirstUniversalPoint_equation W ij
  · exact projectivePairChartFirstUniversalPoint_ne_zero W ij

/-- The homogeneous doubling triple of the second universal input. -/
noncomputable def projectivePairChartSecondDoublingCoordinates
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Fin 3 → projectivePairChartCoordinateRing W ij :=
  (projectivePairChartMappedCurve W ij).toProjective.dblXYZ
    (projectivePairChartSecondUniversalPoint W ij)

/-- The second universal doubling triple also satisfies the mapped cubic
equation. -/
theorem projectivePairChartSecondDoublingCoordinates_equation
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    (projectivePairChartMappedCurve W ij).toProjective.Equation
      (projectivePairChartSecondDoublingCoordinates W ij) := by
  apply dblXYZ_equation_of_isDomain
  · exact projectivePairChartSecondUniversalPoint_equation W ij
  · exact projectivePairChartSecondUniversalPoint_ne_zero W ij

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
