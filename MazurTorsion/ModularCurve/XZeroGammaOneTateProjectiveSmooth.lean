/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, AINTLIB ModularCurves contributors,
  OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveChartAlgebra
import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveJacobian
import MazurTorsion.Upstream.AINTLIB.ForMathlib.StandardSmoothHypersurface
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness of the projective Tate family

For an elliptic Weierstrass equation, each standard coordinate chart of its
projective cubic is a two-variable hypersurface.  The two partial derivatives
cover that hypersurface by the Jacobian comaximality theorem, and localization
at either partial derivative is standard smooth of relative dimension one.
The three coordinate charts cover the projective model, so its projection to
the coefficient spectrum is smooth of relative dimension one.

The chartwise argument is adapted from the smoothness slice of AINTLIB's
`EllipticCurve/WeierstrassModel.lean`, exact source blob
`0cea4fbbcd8f0976b8cb0949755ecacec6e58b26` at its Apache-2.0 licensed
default commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`; full provenance is
recorded in `PORTING.md`.  The global proof is reorganized to work directly
with the coefficient-ring projection.  This avoids the source's two
backward-definitional-equality option wrappers while retaining the same
geometric conclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdeal HomogeneousLocalization

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A]

/-- The coefficient map into each standard coordinate chart is locally
standard smooth of relative dimension one. -/
theorem locally_isStandardSmooth_projection_chart
    (W : WeierstrassCurve A) [W.IsElliptic] (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      ((algebraMap (↥(quotientGrading (ideal W) 0))
        (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : A →+* ↥(quotientGrading (ideal W) 0))) := by
  rw [algebraMap_chart_eq]
  refine (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).1 _
    (chartCoordEquiv W i) ?_
  have hcard : Fintype.card {j : Fin 3 // j ≠ i} = 2 := by
    simp [Fintype.card_subtype_compl]
  have hstep : ∀ j : {j : Fin 3 // j ≠ i},
      RingHom.IsStandardSmoothOfRelativeDimension 1
        ((algebraMap (MvPolynomial {j : Fin 3 // j ≠ i} A ⧸
            Ideal.span {MvPolynomial.dehomogenizeAux A i
              W.toProjective.polynomial})
          (Localization.Away (Ideal.Quotient.mk
            (Ideal.span {MvPolynomial.dehomogenizeAux A i
              W.toProjective.polynomial})
            (MvPolynomial.pderiv j
              (MvPolynomial.dehomogenizeAux A i
                W.toProjective.polynomial))))).comp
          (algebraMap A _)) := by
    intro j
    rw [← IsScalarTower.algebraMap_eq A _ (Localization.Away _),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    have h := ModularCurves.isStandardSmoothOfRelativeDimension_away_pderiv
      (MvPolynomial.dehomogenizeAux A i W.toProjective.polynomial) j
    rwa [hcard] at h
  fin_cases i
  · refine ⟨{Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux A 0 W.toProjective.polynomial)),
      Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux A 0 W.toProjective.polynomial))}, ?_, ?_⟩
    · have h := congrArg (Ideal.map (Ideal.Quotient.mk
          (Ideal.span {MvPolynomial.dehomogenizeAux A 0
            W.toProjective.polynomial})))
          (span_dehomog_jacobian_eq_top_zero W)
      rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq,
        Set.image_insert_eq, Set.image_singleton,
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton_self _),
        Ideal.span_insert_zero] at h
      exact h
    · intro t ht
      simp only at ht
      rcases ht with rfl | rfl
      · exact hstep ⟨1, by decide⟩
      · exact hstep ⟨2, by decide⟩
  · refine ⟨{Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux A 1 W.toProjective.polynomial)),
      Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux A 1 W.toProjective.polynomial))}, ?_, ?_⟩
    · have h := congrArg (Ideal.map (Ideal.Quotient.mk
          (Ideal.span {MvPolynomial.dehomogenizeAux A 1
            W.toProjective.polynomial})))
          (span_dehomog_jacobian_eq_top_one W)
      rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq,
        Set.image_insert_eq, Set.image_singleton,
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton_self _),
        Ideal.span_insert_zero] at h
      exact h
    · intro t ht
      simp only at ht
      rcases ht with rfl | rfl
      · exact hstep ⟨0, by decide⟩
      · exact hstep ⟨2, by decide⟩
  · refine ⟨{Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux A 2 W.toProjective.polynomial)),
      Ideal.Quotient.mk _ (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux A 2 W.toProjective.polynomial))}, ?_, ?_⟩
    · have h := congrArg (Ideal.map (Ideal.Quotient.mk
          (Ideal.span {MvPolynomial.dehomogenizeAux A 2
            W.toProjective.polynomial})))
          (span_dehomog_jacobian_eq_top W)
      rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq,
        Set.image_insert_eq, Set.image_singleton,
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton_self _),
        Ideal.span_insert_zero] at h
      exact h
    · intro t ht
      simp only at ht
      rcases ht with rfl | rfl
      · exact hstep ⟨0, by decide⟩
      · exact hstep ⟨1, by decide⟩

/-- The projective Weierstrass hypersurface of an elliptic equation is smooth
of relative dimension one over its coefficient ring. -/
theorem projection_smoothOfRelativeDimension
    (W : WeierstrassCurve A) [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (projection W) := by
  letI : HasRingHomProperty (@SmoothOfRelativeDimension 1)
      (RingHom.Locally
        (RingHom.IsStandardSmoothOfRelativeDimension 1)) :=
    inferInstance
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  letI : MorphismProperty.RespectsIso
      (@SmoothOfRelativeDimension 1) := by
    rw [HasRingHomProperty.eq_affineLocally
      (@SmoothOfRelativeDimension 1)]
    exact affineLocally_respectsIso _
      (RingHom.locally_respectsIso
        RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
  have hcover : ⨆ i : Fin 3,
      Proj.basicOpen (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) = ⊤ := by
    simpa only [quotientGradingHom_apply] using
      iSup_coordinateBasicOpen_eq_top W
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
    (P := @SmoothOfRelativeDimension 1) _ hcover]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension 1)
    (Proj.basicOpenIsoSpec (quotientGrading (ideal W))
      ((quotientGradingHom (ideal W)) (MvPolynomial.X i))
      (coordinateClass_mem_degreeOne W i) one_pos).inv,
    ← Category.assoc, ← Proj.awayι]
  unfold projection
  rw [← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locally_isStandardSmooth_projection_chart W i

section UniversalTate

variable (R : CommRingCat.{u})

/-- The actual universal projective Tate family is smooth of relative
dimension one over the Tate parameter base. -/
instance familyProjection_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (familyProjection R) := by
  unfold familyProjection
  exact projection_smoothOfRelativeDimension (tateCurveLocOver R)

/-- Public theorem form of the universal Tate-family smoothness instance. -/
theorem familyProjection_isSmoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (familyProjection R) :=
  inferInstance

end UniversalTate

section BaseChange

variable (R : CommRingCat.{u}) {T : Scheme.{u}} (t : T ⟶ tateBase R)

/-- Smooth relative dimension one is preserved by every scheme-theoretic base
change of the universal Tate family. -/
instance baseChangeProjection_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (baseChangeProjection R t) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (baseChange_isPullback R t)
    (familyProjection_isSmoothOfRelativeDimension R)

/-- Public theorem form of arbitrary-base-change smoothness. -/
theorem baseChangeProjection_isSmoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (baseChangeProjection R t) :=
  inferInstance

end BaseChange

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
