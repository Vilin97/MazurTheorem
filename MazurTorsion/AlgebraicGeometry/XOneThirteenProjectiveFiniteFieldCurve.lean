/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.XOneThirteenFiniteFieldCurve
import MazurTorsion.AlgebraicGeometry.XOneThirteenHyperellipticMap
import MazurTorsion.AlgebraicGeometry.XOneThirteenProjectivePoints
import Mathlib.Algebra.Field.ZMod

/-!
# Finite-field points of the glued order-thirteen curve

This file connects the checked affine point certificates to literal points
of the glued projective curve.  A point over a field factors through the
ordinary chart or, if it does not, uniquely through the reciprocal chart
away from the overlap.  The latter boundary is exactly `z = 0`.
-/

noncomputable section

namespace MazurTorsion.XOneThirteenProjectiveFiniteFieldCurve

open CategoryTheory
open _root_.AlgebraicGeometry
open _root_.MazurTorsion.XOneThirteenHyperellipticMap

universe u

variable (K : Type u) [Field K]

/-- Literal `K`-points of the glued order-thirteen curve. -/
abbrev SchemePoint :=
  Spec (.of K) ⟶ XOneThirteenProjectiveCurve.curveScheme K

/-- Literal `K`-points of the reciprocal affine chart. -/
abbrev ReciprocalSchemePoint :=
  Spec (.of K) ⟶ XOneThirteenProjectiveCurve.reciprocalScheme K

private noncomputable abbrev reciprocalOverlapOpen :
    (XOneThirteenProjectiveCurve.reciprocalScheme K).Opens :=
  PrimeSpectrum.basicOpen
    (XOneThirteenProjectiveCurve.zCoordinate K)

private theorem reciprocalChart_preimage_ordinary :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      reciprocalOverlapOpen K :=
  reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen K

/-- Reciprocal-chart points outside the overlap with the ordinary chart. -/
private def ReciprocalBoundaryPoint :=
  {q : ReciprocalSchemePoint K //
    q default ∉ reciprocalOverlapOpen K}

private theorem range_subset_of_default_mem
    {Y : Scheme} (p : Spec (.of K) ⟶ Y) (U : Y.Opens)
    (h : p default ∈ U) : Set.range p ⊆ U := by
  rintro _ ⟨x, rfl⟩
  change p x ∈ U
  rw [Subsingleton.elim x default]
  exact h

private theorem mem_reciprocal_of_not_mem_ordinary
    (p : SchemePoint K)
    (h : p default ∉
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) :
    p default ∈
      (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
  obtain ⟨i, x, hx⟩ :=
    (XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective
      (p default)
  rcases i with (_ | _)
  · exact (h ⟨x, hx⟩).elim
  · exact ⟨x, hx⟩

private noncomputable def ordinaryLift
    (p : SchemePoint K)
    (h : p default ∈
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) :
    XOneThirteenAffineCurve.SchemePoint K :=
  IsOpenImmersion.lift
    (XOneThirteenProjectiveCurve.ordinaryChartMap K) p
    (range_subset_of_default_mem K p _ h)

private noncomputable def reciprocalLift
    (p : SchemePoint K)
    (h : p default ∉
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) :
    ReciprocalSchemePoint K :=
  IsOpenImmersion.lift
    (XOneThirteenProjectiveCurve.reciprocalChartMap K) p
    (range_subset_of_default_mem K p _
      (mem_reciprocal_of_not_mem_ordinary K p h))

private theorem reciprocalLift_not_mem_basicOpen
    (p : SchemePoint K)
    (h : p default ∉
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) :
    reciprocalLift K p h default ∉
      reciprocalOverlapOpen K := by
  intro hz
  apply h
  have hz' :
      (XOneThirteenProjectiveCurve.reciprocalChartMap K)
          (reciprocalLift K p h default) ∈
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
    change reciprocalLift K p h default ∈
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange
    rw [reciprocalChart_preimage_ordinary]
    exact hz
  rw [← IsOpenImmersion.lift_fac
    (XOneThirteenProjectiveCurve.reciprocalChartMap K) p
    (range_subset_of_default_mem K p _
      (mem_reciprocal_of_not_mem_ordinary K p h))]
  exact hz'

/-- A literal point of the glued curve is either a point of the ordinary
chart, or a unique reciprocal-chart point on the boundary `z = 0`. -/
private noncomputable def schemePointEquivChartSum :
    SchemePoint K ≃
      XOneThirteenAffineCurve.SchemePoint K ⊕
        ReciprocalBoundaryPoint K := by
  classical
  exact
    { toFun p := if h : p default ∈
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange then
        Sum.inl (ordinaryLift K p h)
      else
        Sum.inr ⟨reciprocalLift K p h,
          reciprocalLift_not_mem_basicOpen K p h⟩
      invFun p := match p with
        | .inl q => q ≫ XOneThirteenProjectiveCurve.ordinaryChartMap K
        | .inr q => q.1 ≫ XOneThirteenProjectiveCurve.reciprocalChartMap K
      left_inv p := by
        by_cases h : p default ∈
            (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange
        · simp only [dif_pos h]
          exact IsOpenImmersion.lift_fac
            (XOneThirteenProjectiveCurve.ordinaryChartMap K) p
            (range_subset_of_default_mem K p _ h)
        · simp only [dif_neg h]
          exact IsOpenImmersion.lift_fac
            (XOneThirteenProjectiveCurve.reciprocalChartMap K) p
            (range_subset_of_default_mem K p _
              (mem_reciprocal_of_not_mem_ordinary K p h))
      right_inv p := by
        rcases p with q | q
        · have h :
              (q ≫ XOneThirteenProjectiveCurve.ordinaryChartMap K) default ∈
                (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
            exact ⟨q default, rfl⟩
          simp only [dif_pos h]
          congr 1
          exact (IsOpenImmersion.lift_uniq
            (XOneThirteenProjectiveCurve.ordinaryChartMap K)
            (q ≫ XOneThirteenProjectiveCurve.ordinaryChartMap K)
            (range_subset_of_default_mem K _ _ h) q rfl).symm
        · have h :
              (q.1 ≫ XOneThirteenProjectiveCurve.reciprocalChartMap K) default ∉
                (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
            intro hmem
            have hpre : q.1 default ∈
                XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
                  (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
              change (XOneThirteenProjectiveCurve.reciprocalChartMap K)
                (q.1 default) ∈
                  (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange
              simpa only [Scheme.Hom.comp_apply] using hmem
            have hb : q.1 default ∈ reciprocalOverlapOpen K := by
              simpa only [reciprocalChart_preimage_ordinary]
                using hpre
            exact q.2 hb
          simp only [dif_neg h]
          congr 1
          apply Subtype.ext
          exact (IsOpenImmersion.lift_uniq
            (XOneThirteenProjectiveCurve.reciprocalChartMap K)
            (q.1 ≫ XOneThirteenProjectiveCurve.reciprocalChartMap K)
            (range_subset_of_default_mem K _ _
              (mem_reciprocal_of_not_mem_ordinary K _ h)) q.1 rfl).symm }

/-- Solutions on the reciprocal boundary have reciprocal coordinate zero. -/
private def ReciprocalBoundarySolution :=
  {s : XOneThirteenProjectivePoints.ReciprocalSolution K K // s.1.1 = 0}

private theorem reciprocalSolution_point_not_mem_overlap
    [Subsingleton (K →+* K)]
    (s : XOneThirteenProjectivePoints.ReciprocalSolution K K) :
    XOneThirteenProjectivePoints.reciprocalSolutionEquivSchemePoint K s
        default ∉ reciprocalOverlapOpen K ↔
      s.1.1 = 0 := by
  change Spec.map (CommRingCat.ofHom
      (XOneThirteenProjectivePoints.reciprocalSolutionToAlgHom K s).toRingHom)
        default ∉ PrimeSpectrum.basicOpen
          (XOneThirteenProjectiveCurve.zCoordinate K) ↔
    s.1.1 = 0
  change default ∉
      Spec.map (CommRingCat.ofHom
        (XOneThirteenProjectivePoints.reciprocalSolutionToAlgHom K s).toRingHom) ⁻¹ᵁ
        PrimeSpectrum.basicOpen
          (XOneThirteenProjectiveCurve.zCoordinate K) ↔
    s.1.1 = 0
  rw [SpecMap_preimage_basicOpen]
  have hdefault : (default : Spec (.of K)) =
      (⊥ : PrimeSpectrum K) := Subsingleton.elim _ _
  rw [hdefault]
  change (⊥ : PrimeSpectrum K) ∉
      PrimeSpectrum.basicOpen
        ((XOneThirteenProjectivePoints.reciprocalSolutionToAlgHom K s)
          (XOneThirteenProjectiveCurve.zCoordinate K)) ↔
    s.1.1 = 0
  rw [XOneThirteenProjectivePoints.reciprocalSolutionToAlgHom_z]
  simp [PrimeSpectrum.mem_basicOpen]

/-- The reciprocal boundary equation, expressed only in its ordinate. -/
private def SquareRootOne := {w : K // w ^ 2 = 1}

/-- Setting `z = 0` identifies reciprocal boundary solutions with square
roots of one. -/
private noncomputable def reciprocalBoundarySolutionEquivSquareRootOne :
    ReciprocalBoundarySolution K ≃ SquareRootOne K where
  toFun s := ⟨s.1.1.2, by
    simpa [s.2, XOneThirteenProjectiveCurve.reciprocalPolynomial,
      Polynomial.aeval_def] using s.1.2⟩
  invFun w := ⟨⟨(0, w.1), by
    simpa [XOneThirteenProjectiveCurve.reciprocalPolynomial,
      Polynomial.aeval_def] using w.2⟩, rfl⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    ext
    · exact s.2.symm
    · rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- Reciprocal boundary solutions are literal reciprocal boundary points. -/
private noncomputable def reciprocalBoundarySolutionEquivPoint
    [Subsingleton (K →+* K)] :
    ReciprocalBoundarySolution K ≃ ReciprocalBoundaryPoint K :=
  Equiv.subtypeEquiv
    (XOneThirteenProjectivePoints.reciprocalSolutionEquivSchemePoint K) fun s ↦
      (reciprocalSolution_point_not_mem_overlap K s).symm

/-- Square roots of one parametrize the literal reciprocal boundary. -/
private noncomputable def squareRootOneEquivReciprocalBoundaryPoint
    [Subsingleton (K →+* K)] :
    SquareRootOne K ≃ ReciprocalBoundaryPoint K :=
  (reciprocalBoundarySolutionEquivSquareRootOne K).symm.trans
    (reciprocalBoundarySolutionEquivPoint K)

abbrev F3 := _root_.MazurTorsion.XOneThirteenFiniteField.F3
abbrev F5 := _root_.MazurTorsion.XOneThirteenFiniteField.F5

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private noncomputable def squareRootOneEquivInfinityDirectionF3 :
    SquareRootOne F3 ≃
      _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirection := by
  unfold SquareRootOne
    _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirection
  exact Equiv.refl _

private noncomputable def squareRootOneEquivInfinityDirectionF5 :
    SquareRootOne F5 ≃
      _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirectionF5 := by
  unfold SquareRootOne
    _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirectionF5
  exact Equiv.refl _

private noncomputable instance : Fintype (SquareRootOne F3) :=
  Fintype.ofEquiv
    _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirection
    squareRootOneEquivInfinityDirectionF3.symm

private noncomputable instance : Fintype (SquareRootOne F5) :=
  Fintype.ofEquiv
    _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirectionF5
    squareRootOneEquivInfinityDirectionF5.symm

private noncomputable instance : Fintype (ReciprocalBoundaryPoint F3) :=
  Fintype.ofEquiv (SquareRootOne F3)
    (squareRootOneEquivReciprocalBoundaryPoint F3)

private noncomputable instance : Fintype (ReciprocalBoundaryPoint F5) :=
  Fintype.ofEquiv (SquareRootOne F5)
    (squareRootOneEquivReciprocalBoundaryPoint F5)

noncomputable instance schemePointFintypeF3 : Fintype (SchemePoint F3) :=
  Fintype.ofEquiv
    (XOneThirteenAffineCurve.SchemePoint F3 ⊕
      ReciprocalBoundaryPoint F3)
    (schemePointEquivChartSum F3).symm

noncomputable instance schemePointFintypeF5 : Fintype (SchemePoint F5) :=
  Fintype.ofEquiv
    (XOneThirteenAffineCurve.SchemePoint F5 ⊕
      ReciprocalBoundaryPoint F5)
    (schemePointEquivChartSum F5).symm

/-- The six-element `𝔽₃` certificate is canonically equivalent to the
literal points of the glued projective curve. -/
noncomputable def pointCertificateEquivSchemePointF3 :
    _root_.MazurTorsion.XOneThirteenFiniteField.PointCertificate ≃
      SchemePoint F3 := by
  change (_root_.MazurTorsion.XOneThirteenFiniteField.AffineSolution ⊕
      _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirection) ≃
    SchemePoint F3
  exact (Equiv.sumCongr
    XOneThirteenFiniteFieldCurve.Curve.affineSolutionEquivSchemePointF3
    (squareRootOneEquivInfinityDirectionF3.symm.trans
      (squareRootOneEquivReciprocalBoundaryPoint F3))).trans
        (schemePointEquivChartSum F3).symm

/-- The six-element `𝔽₅` certificate is canonically equivalent to the
literal points of the glued projective curve. -/
noncomputable def pointCertificateEquivSchemePointF5 :
    _root_.MazurTorsion.XOneThirteenFiniteField.PointCertificateF5 ≃
      SchemePoint F5 := by
  change (_root_.MazurTorsion.XOneThirteenFiniteField.AffineSolutionF5 ⊕
      _root_.MazurTorsion.XOneThirteenFiniteField.InfinityDirectionF5) ≃
    SchemePoint F5
  exact (Equiv.sumCongr
    XOneThirteenFiniteFieldCurve.Curve.affineSolutionEquivSchemePointF5
    (squareRootOneEquivInfinityDirectionF5.symm.trans
      (squareRootOneEquivReciprocalBoundaryPoint F5))).trans
        (schemePointEquivChartSum F5).symm

/-- The actual reciprocal boundary has two `𝔽₃`-points. -/
private theorem card_reciprocalBoundaryPoint_F3 :
    Fintype.card (ReciprocalBoundaryPoint F3) = 2 := by
  rw [← Fintype.card_congr
    (squareRootOneEquivReciprocalBoundaryPoint F3)]
  rw [Fintype.card_congr squareRootOneEquivInfinityDirectionF3]
  exact _root_.MazurTorsion.XOneThirteenFiniteField.card_infinityDirection

/-- The actual reciprocal boundary has two `𝔽₅`-points. -/
private theorem card_reciprocalBoundaryPoint_F5 :
    Fintype.card (ReciprocalBoundaryPoint F5) = 2 := by
  rw [← Fintype.card_congr
    (squareRootOneEquivReciprocalBoundaryPoint F5)]
  rw [Fintype.card_congr squareRootOneEquivInfinityDirectionF5]
  exact _root_.MazurTorsion.XOneThirteenFiniteField.card_infinityDirectionF5

/-- The actual glued projective curve has six `𝔽₃`-points. -/
theorem card_schemePoint_F3 : Fintype.card (SchemePoint F3) = 6 := by
  rw [Fintype.card_congr (schemePointEquivChartSum F3),
    Fintype.card_sum,
    XOneThirteenFiniteFieldCurve.Curve.card_affineSchemePointF3,
    card_reciprocalBoundaryPoint_F3]

/-- The actual glued projective curve has six `𝔽₅`-points. -/
theorem card_schemePoint_F5 : Fintype.card (SchemePoint F5) = 6 := by
  rw [Fintype.card_congr (schemePointEquivChartSum F5),
    Fintype.card_sum,
    XOneThirteenFiniteFieldCurve.Curve.card_affineSchemePointF5,
    card_reciprocalBoundaryPoint_F5]

end MazurTorsion.XOneThirteenProjectiveFiniteFieldCurve
