/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalScheme
import MazurTorsion.Kubert.OrderTwentyFiveCanonicalSmooth
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Smoothness of the represented order-25 canonical curve

The two affine pieces of the represented canonical curve are codimension-two
complete intersections in affine three-space. This file constructs explicit
pre-submersive presentations for their three Jacobian minors. The checked
normalized equations show that those minors have no common geometric zero in
characteristic zero, so they generate the unit ideal in each coordinate ring.
Localizing at a minor therefore gives a standard-smooth presentation of
relative dimension one.

The chartwise result is transported to the represented coordinate rings and
glued over the two-member open cover. The public instance
`curveToBase_smoothOfRelativeDimension_one` is the downstream geometric
consumer. Integrality and properness remain separate boundaries.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial

namespace MazurTorsion.Kubert
namespace OrderTwentyFiveCanonicalSchemeSmooth

open OrderTwentyFiveCanonicalAffineCharts
open OrderTwentyFiveCanonicalScheme

universe u

private def completeIntersectionEquations
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) : Fin 2 → MvPolynomial (Fin 3) R :=
  ![f, g]

private abbrev CompleteIntersectionIdeal
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) :=
  Ideal.span (Set.range (completeIntersectionEquations R f g))

private abbrev CompleteIntersectionRing
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) :=
  MvPolynomial (Fin 3) R ⧸ CompleteIntersectionIdeal R f g

private def minorColumns : Fin 3 → Fin 2 → Fin 3 :=
  ![![0, 1], ![0, 2], ![1, 2]]

private theorem minorColumns_injective (k : Fin 3) :
    Function.Injective (minorColumns k) := by
  intro i j hij
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [minorColumns] at hij ⊢

private def completeIntersectionMinor
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) (k : Fin 3) :
    MvPolynomial (Fin 3) R :=
  MvPolynomial.pderiv (minorColumns k 0) f *
      MvPolynomial.pderiv (minorColumns k 1) g -
    MvPolynomial.pderiv (minorColumns k 0) g *
      MvPolynomial.pderiv (minorColumns k 1) f

private noncomputable def completeIntersectionPrePresentation
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) (k : Fin 3) :
    Algebra.PreSubmersivePresentation R
      (CompleteIntersectionRing R f g) (Fin 3) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive
    (v := completeIntersectionEquations R f g)
      (minorColumns k) (minorColumns_injective k)

private lemma completeIntersectionPrePresentation_jacobian
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) (k : Fin 3) :
    (completeIntersectionPrePresentation R f g k).jacobian =
      Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
        (completeIntersectionMinor R f g k) := by
  let P := completeIntersectionPrePresentation R f g k
  change P.jacobian = _
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Matrix.det_fin_two]
  have hentry (i j : Fin 2) :
      P.jacobiMatrix i j =
        MvPolynomial.pderiv (minorColumns k i)
          (completeIntersectionEquations R f g j) := by
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    rfl
  rw [hentry, hentry, hentry, hentry]
  rfl

private lemma localized_completeIntersection_isStandardSmoothOfRelativeDimension_one
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) (k : Fin 3) :
    let S := CompleteIntersectionRing R f g
    let d : S := Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
      (completeIntersectionMinor R f g k)
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((algebraMap S (Localization.Away d)).comp (algebraMap R S)) := by
  dsimp only
  let S := CompleteIntersectionRing R f g
  let d : S := Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
    (completeIntersectionMinor R f g k)
  let T := Localization.Away d
  let P := completeIntersectionPrePresentation R f g k
  let Q := Algebra.PreSubmersivePresentation.localizationAway T d
  let PQ := Q.comp P
  let SP : Algebra.SubmersivePresentation R T
      (Unit ⊕ Fin 3) (Unit ⊕ Fin 2) :=
    { toPreSubmersivePresentation := PQ
      jacobian_isUnit := by
        dsimp only [PQ, Q, P]
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          completeIntersectionPrePresentation_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian]
        rw [Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have hA : Algebra.IsStandardSmoothOfRelativeDimension 1 R T :=
    SP.isStandardSmoothOfRelativeDimension (by
      change Nat.card (Unit ⊕ Fin 3) - Nat.card (Unit ⊕ Fin 2) = 1
      simp)
  have hRing : RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap R T) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr hA
  simpa only [IsScalarTower.algebraMap_eq R S T] using hRing

private lemma completeIntersection_locally_isStandardSmoothOfRelativeDimension_one
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R)
    (hspan : Ideal.span (Set.range fun k : Fin 3 ↦
      Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
        (completeIntersectionMinor R f g k)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (CompleteIntersectionRing R f g)) := by
  refine ⟨Set.range (fun k : Fin 3 ↦
    Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
      (completeIntersectionMinor R f g k)), hspan, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact localized_completeIntersection_isStandardSmoothOfRelativeDimension_one R f g k

private lemma completeIntersection_minors_span_top_of_geometric_nonsingular
    (R : Type u) [Field R]
    (f g : MvPolynomial (Fin 3) R)
    (h : ∀ (L : Type u) [Field L] (φ : R →+* L) (x : Fin 3 → L),
      MvPolynomial.eval₂ φ x f = 0 →
      MvPolynomial.eval₂ φ x g = 0 →
        ∃ k : Fin 3,
          MvPolynomial.eval₂ φ x (completeIntersectionMinor R f g k) ≠ 0) :
    Ideal.span (Set.range fun k : Fin 3 ↦
      Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
        (completeIntersectionMinor R f g k)) = ⊤ := by
  by_contra htop
  let S := CompleteIntersectionRing R f g
  let J : Ideal S := Ideal.span (Set.range fun k : Fin 3 ↦
    Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
      (completeIntersectionMinor R f g k))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J htop
  let L := S ⧸ M
  letI : Field L := Ideal.Quotient.field M
  let q₁ : MvPolynomial (Fin 3) R →+* S :=
    Ideal.Quotient.mk (CompleteIntersectionIdeal R f g)
  let q₂ : S →+* L := Ideal.Quotient.mk M
  let φ : R →+* L :=
    q₂.comp (q₁.comp (MvPolynomial.C : R →+* MvPolynomial (Fin 3) R))
  let x : Fin 3 → L := fun i ↦ q₂ (q₁ (MvPolynomial.X i))
  have heval : MvPolynomial.eval₂Hom φ x = q₂.comp q₁ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [φ, q₁, q₂]
    · intro i
      simp [x]
  have hfzero : MvPolynomial.eval₂ φ x f = 0 := by
    change (MvPolynomial.eval₂Hom φ x) f = 0
    rw [heval]
    change q₂ (q₁ f) = 0
    have hfmem : f ∈ CompleteIntersectionIdeal R f g :=
      Ideal.subset_span ⟨0, rfl⟩
    rw [show q₁ f = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hfmem, map_zero]
  have hgzero : MvPolynomial.eval₂ φ x g = 0 := by
    change (MvPolynomial.eval₂Hom φ x) g = 0
    rw [heval]
    change q₂ (q₁ g) = 0
    have hgmem : g ∈ CompleteIntersectionIdeal R f g :=
      Ideal.subset_span ⟨1, rfl⟩
    rw [show q₁ g = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hgmem, map_zero]
  obtain ⟨k, hk⟩ := h L φ x hfzero hgzero
  apply hk
  change (MvPolynomial.eval₂Hom φ x)
      (completeIntersectionMinor R f g k) = 0
  rw [heval]
  change q₂ (q₁ (completeIntersectionMinor R f g k)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hJM
  exact Ideal.subset_span ⟨k, rfl⟩

private theorem leftChart_explicit_minors_ne_zero
    {L : Type u} [Field L] [CharZero L] (x y w : L)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y (1 - x) w) :
    let qx := 2*x - y - 2*w - 1
    let qy := 2*y + 1 - x
    let qw := 1 - 2*x
    let cx := y - 2*x*y + 6*x*w - 2*y*w - 3*w + w^2
    let cy := x - x^2 + w - 2*x*w
    let cw := 3*x^2 - 2*x*y - 3*x + y + 1 - 2*w + 2*x*w
    qx*cy-qy*cx ≠ 0 ∨ qx*cw-qw*cx ≠ 0 ∨ qy*cw-qw*cy ≠ 0 := by
  dsimp
  by_contra h
  simp only [not_or, not_ne_iff] at h
  rcases h with ⟨h01, h02, h12⟩
  rcases hcurve with ⟨hq, hc⟩
  simp only [orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic] at hq hc
  grobner

private theorem rightChart_explicit_minors_ne_zero
    {L : Type u} [Field L] [CharZero L] (x y z : L)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z (1 - x)) :
    let qx := 2*x - 2*z - 1
    let qy := 2*y + z
    let qz := 1 - 2*x + y
    let cx := 2*x - 3*x^2 - y + 2*x*y + z - z^2
    let cy := x^2 - x + z
    let cz := x + y + 2*z - 2*x*z - 1
    qx*cy-qy*cx ≠ 0 ∨ qx*cz-qz*cx ≠ 0 ∨ qy*cz-qz*cy ≠ 0 := by
  dsimp
  by_contra h
  simp only [not_or, not_ne_iff] at h
  rcases h with ⟨h01, h02, h12⟩
  rcases hcurve with ⟨hq, hc⟩
  simp only [orderTwentyFiveCanonicalQuadric,
    orderTwentyFiveCanonicalCubic] at hq hc
  grobner

private lemma leftChart_minors_geometrically_nonsingular
    (K : Type u) [Field K] [CharZero K] :
    ∀ (L : Type u) [Field L] (φ : K →+* L) (p : Fin 3 → L),
      MvPolynomial.eval₂ φ p (leftQuadric K) = 0 →
      MvPolynomial.eval₂ φ p (leftCubic K) = 0 →
        ∃ k : Fin 3, MvPolynomial.eval₂ φ p
          (completeIntersectionMinor K (leftQuadric K) (leftCubic K) k) ≠ 0 := by
  intro L _ φ p hq hc
  letI : CharZero L := charZero_of_injective_ringHom φ.injective
  have hcurve : OrderTwentyFiveCanonicalOnCurve
      (p 0) (p 1) (1 - p 0) (p 2) := by
    constructor
    · simpa [eval_leftQuadric] using hq
    · simpa [eval_leftCubic] using hc
  rcases leftChart_explicit_minors_ne_zero (p 0) (p 1) (p 2) hcurve with
    h01 | h02 | h12
  · refine ⟨0, ?_⟩
    intro hk
    apply h01
    simp [completeIntersectionMinor, minorColumns, leftQuadric,
      orderTwentyFiveCanonicalQuadric, leftCubic,
      orderTwentyFiveCanonicalCubic] at hk
    ring_nf at hk ⊢
    exact hk
  · refine ⟨1, ?_⟩
    intro hk
    apply h02
    simp [completeIntersectionMinor, minorColumns, leftQuadric,
      orderTwentyFiveCanonicalQuadric, leftCubic,
      orderTwentyFiveCanonicalCubic] at hk
    ring_nf at hk ⊢
    exact hk
  · refine ⟨2, ?_⟩
    intro hk
    apply h12
    simp [completeIntersectionMinor, minorColumns, leftQuadric,
      orderTwentyFiveCanonicalQuadric, leftCubic,
      orderTwentyFiveCanonicalCubic] at hk
    ring_nf at hk ⊢
    exact hk

private lemma rightChart_minors_geometrically_nonsingular
    (K : Type u) [Field K] [CharZero K] :
    ∀ (L : Type u) [Field L] (φ : K →+* L) (p : Fin 3 → L),
      MvPolynomial.eval₂ φ p (rightQuadric K) = 0 →
      MvPolynomial.eval₂ φ p (rightCubic K) = 0 →
        ∃ k : Fin 3, MvPolynomial.eval₂ φ p
          (completeIntersectionMinor K (rightQuadric K) (rightCubic K) k) ≠ 0 := by
  intro L _ φ p hq hc
  letI : CharZero L := charZero_of_injective_ringHom φ.injective
  have hcurve : OrderTwentyFiveCanonicalOnCurve
      (p 0) (p 1) (p 2) (1 - p 0) := by
    constructor
    · simpa [eval_rightQuadric] using hq
    · simpa [eval_rightCubic] using hc
  rcases rightChart_explicit_minors_ne_zero (p 0) (p 1) (p 2) hcurve with
    h01 | h02 | h12
  · refine ⟨0, ?_⟩
    intro hk
    apply h01
    simp [completeIntersectionMinor, minorColumns, rightQuadric,
      orderTwentyFiveCanonicalQuadric, rightCubic,
      orderTwentyFiveCanonicalCubic] at hk
    ring_nf at hk ⊢
    exact hk
  · refine ⟨1, ?_⟩
    intro hk
    apply h02
    simp [completeIntersectionMinor, minorColumns, rightQuadric,
      orderTwentyFiveCanonicalQuadric, rightCubic,
      orderTwentyFiveCanonicalCubic] at hk
    ring_nf at hk ⊢
    exact hk
  · refine ⟨2, ?_⟩
    intro hk
    apply h12
    simp [completeIntersectionMinor, minorColumns, rightQuadric,
      orderTwentyFiveCanonicalQuadric, rightCubic,
      orderTwentyFiveCanonicalCubic] at hk
    ring_nf at hk ⊢
    exact hk

private theorem completeIntersectionIdeal_eq_pair
    (R : Type u) [CommRing R]
    (f g : MvPolynomial (Fin 3) R) :
    CompleteIntersectionIdeal R f g = Ideal.span {f, g} := by
  simp [CompleteIntersectionIdeal, completeIntersectionEquations, Set.pair_comm]

private noncomputable def leftCoordinateRingAlgEquiv
    (K : Type u) [CommRing K] :
    CompleteIntersectionRing K (leftQuadric K) (leftCubic K) ≃ₐ[K]
      LeftRing K :=
  Ideal.quotientEquivAlgOfEq K (by
    rw [completeIntersectionIdeal_eq_pair]
    rfl)

private noncomputable def rightCoordinateRingAlgEquiv
    (K : Type u) [CommRing K] :
    CompleteIntersectionRing K (rightQuadric K) (rightCubic K) ≃ₐ[K]
      RightRing K :=
  Ideal.quotientEquivAlgOfEq K (by
    rw [completeIntersectionIdeal_eq_pair]
    rfl)

private lemma leftCoordinateRingAlgEquiv_comp_algebraMap
    (K : Type u) [CommRing K] :
    (leftCoordinateRingAlgEquiv K).toRingEquiv.toRingHom.comp
        (algebraMap K
          (CompleteIntersectionRing K (leftQuadric K) (leftCubic K))) =
      algebraMap K (LeftRing K) := by
  ext a
  exact (leftCoordinateRingAlgEquiv K).commutes a

private lemma rightCoordinateRingAlgEquiv_comp_algebraMap
    (K : Type u) [CommRing K] :
    (rightCoordinateRingAlgEquiv K).toRingEquiv.toRingHom.comp
        (algebraMap K
          (CompleteIntersectionRing K (rightQuadric K) (rightCubic K))) =
      algebraMap K (RightRing K) := by
  ext a
  exact (rightCoordinateRingAlgEquiv K).commutes a

private lemma leftStructureRingHom_locally_relativeDimension_one
    (K : Type u) [Field K] [CharZero K] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K (LeftRing K)) := by
  have hspan :=
    completeIntersection_minors_span_top_of_geometric_nonsingular K
      (leftQuadric K) (leftCubic K)
      (leftChart_minors_geometrically_nonsingular K)
  have hlocal :=
    completeIntersection_locally_isStandardSmoothOfRelativeDimension_one K
      (leftQuadric K) (leftCubic K) hspan
  have htransport :=
    (RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).1
        (algebraMap K
          (CompleteIntersectionRing K (leftQuadric K) (leftCubic K)))
        (leftCoordinateRingAlgEquiv K).toRingEquiv hlocal
  rw [leftCoordinateRingAlgEquiv_comp_algebraMap] at htransport
  exact htransport

private lemma rightStructureRingHom_locally_relativeDimension_one
    (K : Type u) [Field K] [CharZero K] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K (RightRing K)) := by
  have hspan :=
    completeIntersection_minors_span_top_of_geometric_nonsingular K
      (rightQuadric K) (rightCubic K)
      (rightChart_minors_geometrically_nonsingular K)
  have hlocal :=
    completeIntersection_locally_isStandardSmoothOfRelativeDimension_one K
      (rightQuadric K) (rightCubic K) hspan
  have htransport :=
    (RingHom.locally_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1))).1
        (algebraMap K
          (CompleteIntersectionRing K (rightQuadric K) (rightCubic K)))
        (rightCoordinateRingAlgEquiv K).toRingEquiv hlocal
  rw [rightCoordinateRingAlgEquiv_comp_algebraMap] at htransport
  exact htransport

private lemma leftChartToBase_smoothOfRelativeDimension_one
    (K : Type u) [Field K] [CharZero K] :
    SmoothOfRelativeDimension 1 (leftChartToBase K) := by
  unfold leftChartToBase
  exact (HasRingHomProperty.Spec_iff
    (P := @SmoothOfRelativeDimension 1)).mpr
      (leftStructureRingHom_locally_relativeDimension_one K)

private lemma rightChartToBase_smoothOfRelativeDimension_one
    (K : Type u) [Field K] [CharZero K] :
    SmoothOfRelativeDimension 1 (rightChartToBase K) := by
  unfold rightChartToBase
  exact (HasRingHomProperty.Spec_iff
    (P := @SmoothOfRelativeDimension 1)).mpr
      (rightStructureRingHom_locally_relativeDimension_one K)

/-- The represented order-25 canonical curve is smooth of relative
dimension one over every characteristic-zero field. -/
instance curveToBase_smoothOfRelativeDimension_one
    (K : Type u) [Field K] [CharZero K] :
    SmoothOfRelativeDimension 1 (curveToBase K) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover
    (P := @SmoothOfRelativeDimension 1) (openCover K)]
  intro i
  rcases i with (_ | _)
  · change SmoothOfRelativeDimension 1
      (leftChartMap K ≫ curveToBase K)
    rw [leftChartMap_curveToBase]
    exact leftChartToBase_smoothOfRelativeDimension_one K
  · change SmoothOfRelativeDimension 1
      (rightChartMap K ≫ curveToBase K)
    rw [rightChartMap_curveToBase]
    exact rightChartToBase_smoothOfRelativeDimension_one K

end OrderTwentyFiveCanonicalSchemeSmooth
end MazurTorsion.Kubert
