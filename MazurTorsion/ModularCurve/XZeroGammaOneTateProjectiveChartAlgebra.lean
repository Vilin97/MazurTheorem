/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, AINTLIB ModularCurves contributors,
  OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveChartCover
import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveProper
import MazurTorsion.Upstream.AINTLIB.ForMathlib.ProjPrincipalQuotientChart

/-!
# Coordinate rings of the projective Tate-family charts

Each coordinate away chart of the homogeneous Weierstrass quotient is the
polynomial ring in the other two coordinates modulo the dehomogenized cubic.
The resulting equivalence is compatible with the coefficient-ring map through
the degree-zero part of the homogeneous quotient.

The proof is adapted from the clean chart-coordinate slice of AINTLIB's
`EllipticCurve/WeierstrassModel.lean`, exact source blob
`0cea4fbbcd8f0976b8cb0949755ecacec6e58b26` at its Apache-2.0 licensed
default commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`; full provenance is
recorded in `PORTING.md`. No point dictionary, smoothness, or group law is
asserted here.
-/

noncomputable section

open AlgebraicGeometry MvPolynomial
open HomogeneousIdeal HomogeneousLocalization

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A]

/-- A coordinate chart of the projective Weierstrass model is the affine
plane modulo the dehomogenized cubic. -/
noncomputable def chartCoordEquiv (W : WeierstrassCurve A) (i : Fin 3) :
    (MvPolynomial {j : Fin 3 // j ≠ i} A ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux A i
        W.toProjective.polynomial}) ≃+*
    Away (quotientGrading (ideal W))
      ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) :=
  MvPolynomial.principalQuotientChartEquiv A (ideal W)
    W.toProjective.polynomial (polynomial_isHomogeneous W)
    (ideal_toIdeal W) i

@[simp]
theorem chartCoordEquiv_mk (W : WeierstrassCurve A) (i : Fin 3)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} A) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux A i
          W.toProjective.polynomial}) p) =
      Away.map (quotientGradingHom (ideal W))
        (MvPolynomial.X i) (MvPolynomial.homogenizeAt A i p) := by
  unfold chartCoordEquiv
  unfold MvPolynomial.principalQuotientChartEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_symm_mk]
  unfold HomogeneousIdeal.principalAwayQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ _

/-- The coefficient map into a quotient chart agrees with the polynomial-chart
coefficient map under the degree-zero identification. -/
theorem chartBaseMap_eq (W : WeierstrassCurve A) (i : Fin 3) :
    (algebraMap (↥(quotientGrading (ideal W) 0))
        (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : A →+* ↥(quotientGrading (ideal W) 0)) =
      ((Away.map (quotientGradingHom (ideal W))
          (MvPolynomial.X i)).comp
        ((MvPolynomial.chartRingEquiv A i).symm :
          MvPolynomial {j : Fin 3 // j ≠ i} A →+*
            Away (MvPolynomial.homogeneousSubmodule (Fin 3) A)
              (MvPolynomial.X i))).comp
        (algebraMap A (MvPolynomial {j : Fin 3 // j ≠ i} A)) := by
  refine RingHom.ext fun a => ?_
  have hconst : ((MvPolynomial.chartRingEquiv A i).symm :
      MvPolynomial {j : Fin 3 // j ≠ i} A →+* _)
        (algebraMap A (MvPolynomial {j : Fin 3 // j ≠ i} A) a) =
      MvPolynomial.awayConst A i a := by
    change MvPolynomial.homogenizeAt A i
      (algebraMap A (MvPolynomial {j : Fin 3 // j ≠ i} A) a) = _
    rw [show algebraMap A (MvPolynomial {j : Fin 3 // j ≠ i} A) a =
      MvPolynomial.C a from rfl, MvPolynomial.homogenizeAt,
      MvPolynomial.eval₂Hom_C]
    rfl
  apply val_injective
  have hval : (Away.map (quotientGradingHom (ideal W))
      (MvPolynomial.X i) (MvPolynomial.awayConst A i a)).val =
      Localization.mk
        ((quotientGradingHom (ideal W)) (MvPolynomial.C a)) 1 := by
    rw [MvPolynomial.awayConst, Away.map_mk, Away.val_mk]
    exact congrArg _ (Subtype.ext (pow_zero _))
  simp only [RingHom.comp_apply]
  rw [hconst, hval, HomogeneousLocalization.algebraMap_eq]
  change Localization.mk
    ((gradeZeroRingEquiv W a : ↥(quotientGrading (ideal W) 0)) :
      coordinateRing W) 1 = _
  have hcoeff :
      ((gradeZeroRingEquiv W a : ↥(quotientGrading (ideal W) 0)) :
        coordinateRing W) =
        Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.C a) := by
    change algebraMap A (coordinateRing W) a = _
    rw [IsScalarTower.algebraMap_eq A (MvPolynomial (Fin 3) A)
      (coordinateRing W), RingHom.comp_apply, Ideal.Quotient.algebraMap_eq,
      MvPolynomial.algebraMap_eq]
  rw [hcoeff]
  rfl

/-- The chart-coordinate equivalence preserves coefficients. -/
theorem chartCoordEquiv_mk_C (W : WeierstrassCurve A) (i : Fin 3) (a : A) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux A i
          W.toProjective.polynomial}) (MvPolynomial.C a)) =
      (algebraMap (↥(quotientGrading (ideal W) 0))
        (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i))))
        (gradeZeroRingEquiv W a) := by
  rw [chartCoordEquiv_mk]
  exact (RingHom.congr_fun (chartBaseMap_eq W i) a).symm

/-- The structural map of a quotient chart factors through its affine-plane
coordinate presentation. -/
theorem algebraMap_chart_eq (W : WeierstrassCurve A) (i : Fin 3) :
    ((algebraMap (↥(quotientGrading (ideal W) 0))
      (Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : A →+* ↥(quotientGrading (ideal W) 0))) =
      ((chartCoordEquiv W i).toRingHom).comp
        (algebraMap A (MvPolynomial {j : Fin 3 // j ≠ i} A ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux A i
            W.toProjective.polynomial})) := by
  refine RingHom.ext fun a => ?_
  change _ = chartCoordEquiv W i (algebraMap A _ a)
  rw [show (algebraMap A (MvPolynomial {j : Fin 3 // j ≠ i} A ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux A i
        W.toProjective.polynomial})) a =
      Ideal.Quotient.mk _ (MvPolynomial.C a) from by
    rw [IsScalarTower.algebraMap_apply A
      (MvPolynomial {j : Fin 3 // j ≠ i} A) _,
      Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]]
  exact (chartCoordEquiv_mk_C W i a).symm

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
