/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.XOneThirteenFiniteFieldCurve
import MazurTorsion.AlgebraicGeometry.XOneThirteenHyperellipticMap
import MazurTorsion.AlgebraicGeometry.XOneThirteenProjectivePoints
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Finite-field points of the glued order-thirteen curve

This file connects the checked finite-field certificates to actual points
of the glued projective curve.  A point over a field factors through the
ordinary chart or, if it does not, uniquely through the reciprocal chart
away from the overlap.  The latter boundary is exactly `z = 0`.  Over the
quadratic extensions, genuine rational points are recorded as sections of
the structure morphism, excluding Frobenius-twisted scheme morphisms.
-/

noncomputable section

namespace MazurTorsion.XOneThirteenProjectiveFiniteFieldCurve

open CategoryTheory
open _root_.AlgebraicGeometry
open Polynomial
open _root_.MazurTorsion.XOneThirteenHyperellipticMap

universe u

variable (K : Type u) [Field K]

/-- Literal morphisms from `Spec K` to the glued order-thirteen curve. -/
abbrev SchemePoint :=
  Spec (.of K) ⟶ XOneThirteenProjectiveCurve.curveScheme K

/-- A genuine `K`-rational point of the glued curve: a section of its
structure morphism over `Spec K`.  This section condition matters over
non-prime finite fields, where an arbitrary scheme morphism may lie over a
nontrivial Frobenius endomorphism of `K`. -/
def CurveSection :=
  {p : SchemePoint K //
    p ≫ XOneThirteenProjectiveCurve.curveToBase K = 𝟙 _}

/-- Literal morphisms from `Spec K` to the reciprocal affine chart. -/
abbrev ReciprocalSchemePoint :=
  Spec (.of K) ⟶ XOneThirteenProjectiveCurve.reciprocalScheme K

private def OrdinarySection :=
  {p : XOneThirteenAffineCurve.SchemePoint K //
    p ≫ XOneThirteenProjectiveCurve.ordinaryChartToBase K = 𝟙 _}

private def ReciprocalSection :=
  {p : ReciprocalSchemePoint K //
    p ≫ XOneThirteenProjectiveCurve.reciprocalChartToBase K = 𝟙 _}

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

private def ReciprocalBoundarySection :=
  {q : ReciprocalBoundaryPoint K //
    q.1 ≫ XOneThirteenProjectiveCurve.reciprocalChartToBase K = 𝟙 _}

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

private noncomputable def ordinaryAlgHomToSection
    (f : XOneThirteenAffineCurve.CoordinateRing K →ₐ[K] K) :
    OrdinarySection K :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    unfold XOneThirteenProjectiveCurve.ordinaryChartToBase
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext k
    exact f.commutes k⟩

private noncomputable def ordinarySectionToAlgHom
    (p : OrdinarySection K) :
    XOneThirteenAffineCurve.CoordinateRing K →ₐ[K] K := by
  let fcat : CommRingCat.of
        (XOneThirteenAffineCurve.CoordinateRing K) ⟶ CommRingCat.of K :=
    (Spec.homEquiv
      (R := .of (XOneThirteenAffineCurve.CoordinateRing K))
      (S := .of K)) p.1
  let f : XOneThirteenAffineCurve.CoordinateRing K →+* K := fcat.hom
  refine { __ := f, commutes' := ?_ }
  intro k
  have hp := p.2
  have hf : Spec.map (CommRingCat.ofHom f) = p.1 := by
    change Spec.map fcat = p.1
    exact (Spec.homEquiv
      (R := .of (XOneThirteenAffineCurve.CoordinateRing K))
      (S := .of K)).symm_apply_apply p.1
  rw [← hf] at hp
  unfold XOneThirteenProjectiveCurve.ordinaryChartToBase at hp
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hp
  exact congrArg
    (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom k) hp

private noncomputable def ordinaryAlgHomEquivSection :
    (XOneThirteenAffineCurve.CoordinateRing K →ₐ[K] K) ≃
      OrdinarySection K where
  toFun := ordinaryAlgHomToSection K
  invFun := ordinarySectionToAlgHom K
  left_inv f := by
    apply AlgHom.coe_ringHom_injective
    change (Spec.homEquiv
      (R := .of (XOneThirteenAffineCurve.CoordinateRing K))
      (S := .of K)
      (Spec.map (CommRingCat.ofHom f.toRingHom))).hom = f.toRingHom
    exact congrArg CommRingCat.Hom.hom
      ((Spec.homEquiv
        (R := .of (XOneThirteenAffineCurve.CoordinateRing K))
        (S := .of K)).apply_symm_apply (CommRingCat.ofHom f.toRingHom))
  right_inv p := by
    apply Subtype.ext
    change Spec.map (Spec.homEquiv p.1) = p.1
    exact (Spec.homEquiv
      (R := .of (XOneThirteenAffineCurve.CoordinateRing K))
      (S := .of K)).symm_apply_apply p.1

private noncomputable def ordinarySolutionEquivSection :
    XOneThirteenAffineCurve.Solution K K ≃ OrdinarySection K :=
  (XOneThirteenAffineCurve.solutionEquivAlgHom K).trans
    (ordinaryAlgHomEquivSection K)

private noncomputable def reciprocalAlgHomToSection
    (f : XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] K) :
    ReciprocalSection K :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    unfold XOneThirteenProjectiveCurve.reciprocalChartToBase
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext k
    exact f.commutes k⟩

private noncomputable def reciprocalSectionToAlgHom
    (p : ReciprocalSection K) :
    XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] K := by
  let fcat : CommRingCat.of
        (XOneThirteenProjectiveCurve.ReciprocalRing K) ⟶ CommRingCat.of K :=
    (Spec.homEquiv
      (R := .of (XOneThirteenProjectiveCurve.ReciprocalRing K))
      (S := .of K)) p.1
  let f : XOneThirteenProjectiveCurve.ReciprocalRing K →+* K := fcat.hom
  refine { __ := f, commutes' := ?_ }
  intro k
  have hp := p.2
  have hf : Spec.map (CommRingCat.ofHom f) = p.1 := by
    change Spec.map fcat = p.1
    exact (Spec.homEquiv
      (R := .of (XOneThirteenProjectiveCurve.ReciprocalRing K))
      (S := .of K)).symm_apply_apply p.1
  rw [← hf] at hp
  unfold XOneThirteenProjectiveCurve.reciprocalChartToBase at hp
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hp
  exact congrArg
    (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom k) hp

private noncomputable def reciprocalAlgHomEquivSection :
    (XOneThirteenProjectiveCurve.ReciprocalRing K →ₐ[K] K) ≃
      ReciprocalSection K where
  toFun := reciprocalAlgHomToSection K
  invFun := reciprocalSectionToAlgHom K
  left_inv f := by
    apply AlgHom.coe_ringHom_injective
    change (Spec.homEquiv
      (R := .of (XOneThirteenProjectiveCurve.ReciprocalRing K))
      (S := .of K)
      (Spec.map (CommRingCat.ofHom f.toRingHom))).hom = f.toRingHom
    exact congrArg CommRingCat.Hom.hom
      ((Spec.homEquiv
        (R := .of (XOneThirteenProjectiveCurve.ReciprocalRing K))
        (S := .of K)).apply_symm_apply (CommRingCat.ofHom f.toRingHom))
  right_inv p := by
    apply Subtype.ext
    change Spec.map (Spec.homEquiv p.1) = p.1
    exact (Spec.homEquiv
      (R := .of (XOneThirteenProjectiveCurve.ReciprocalRing K))
      (S := .of K)).symm_apply_apply p.1

private noncomputable def reciprocalSolutionEquivSection :
    XOneThirteenProjectivePoints.ReciprocalSolution K K ≃
      ReciprocalSection K :=
  (XOneThirteenProjectivePoints.reciprocalSolutionEquivAlgHom K).trans
    (reciprocalAlgHomEquivSection K)

private def chartSectionPredicate
    (s : XOneThirteenAffineCurve.SchemePoint K ⊕
      ReciprocalBoundaryPoint K) : Prop :=
  (schemePointEquivChartSum K).symm s ≫
      XOneThirteenProjectiveCurve.curveToBase K = 𝟙 _

private noncomputable def curveSectionEquivChartSubtype :
    CurveSection K ≃
      {s : XOneThirteenAffineCurve.SchemePoint K ⊕
          ReciprocalBoundaryPoint K // chartSectionPredicate K s} :=
  Equiv.subtypeEquiv (schemePointEquivChartSum K) fun p ↦ by
    unfold chartSectionPredicate
    rw [Equiv.symm_apply_apply]

private noncomputable def ordinaryChartSubtypeEquivSection :
    {p : XOneThirteenAffineCurve.SchemePoint K //
        chartSectionPredicate K (Sum.inl p)} ≃ OrdinarySection K :=
  Equiv.subtypeEquiv (Equiv.refl _) fun p ↦ by
    unfold chartSectionPredicate
    change (p ≫ XOneThirteenProjectiveCurve.ordinaryChartMap K) ≫
        XOneThirteenProjectiveCurve.curveToBase K = 𝟙 _ ↔
      p ≫ XOneThirteenProjectiveCurve.ordinaryChartToBase K = 𝟙 _
    rw [Category.assoc,
      XOneThirteenProjectiveCurve.ordinaryChartMap_curveToBase]

private noncomputable def reciprocalChartSubtypeEquivSection :
    {p : ReciprocalBoundaryPoint K //
        chartSectionPredicate K (Sum.inr p)} ≃
      ReciprocalBoundarySection K :=
  Equiv.subtypeEquiv (Equiv.refl _) fun p ↦ by
    unfold chartSectionPredicate
    change (p.1 ≫ XOneThirteenProjectiveCurve.reciprocalChartMap K) ≫
        XOneThirteenProjectiveCurve.curveToBase K = 𝟙 _ ↔
      p.1 ≫ XOneThirteenProjectiveCurve.reciprocalChartToBase K = 𝟙 _
    rw [Category.assoc,
      XOneThirteenProjectiveCurve.reciprocalChartMap_curveToBase]

private noncomputable def curveSectionEquivChartSum :
    CurveSection K ≃ OrdinarySection K ⊕ ReciprocalBoundarySection K :=
  (curveSectionEquivChartSubtype K).trans <|
    Equiv.subtypeSum.trans <|
      Equiv.sumCongr (ordinaryChartSubtypeEquivSection K)
        (reciprocalChartSubtypeEquivSection K)

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

private theorem reciprocalSolution_section_not_mem_overlap
    (s : XOneThirteenProjectivePoints.ReciprocalSolution K K) :
    (reciprocalSolutionEquivSection K s).1 default ∉
        reciprocalOverlapOpen K ↔
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

private noncomputable def reciprocalSectionBoundaryReassoc :
    {q : ReciprocalSection K //
        q.1 default ∉ reciprocalOverlapOpen K} ≃
      ReciprocalBoundarySection K where
  toFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  invFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def reciprocalBoundarySolutionEquivSection :
    ReciprocalBoundarySolution K ≃ ReciprocalBoundarySection K :=
  (Equiv.subtypeEquiv (reciprocalSolutionEquivSection K) fun s ↦
    (reciprocalSolution_section_not_mem_overlap K s).symm).trans
      (reciprocalSectionBoundaryReassoc K)

private noncomputable def squareRootOneEquivReciprocalBoundarySection :
    SquareRootOne K ≃ ReciprocalBoundarySection K :=
  (reciprocalBoundarySolutionEquivSquareRootOne K).symm.trans
    (reciprocalBoundarySolutionEquivSection K)

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

/-- The checked quadratic extension of `𝔽₃` obtained by adjoining a root of
`T² - 2`. -/
abbrev F9 := QuadraticAlgebra F3 (2 : F3) 0

/-- The checked quadratic extension of `𝔽₅` obtained by adjoining a root of
`T² - 2`. -/
abbrev F25 := QuadraticAlgebra F5 (2 : F5) 0

private noncomputable instance f9Field : Field F9 := by
  letI : Fact (∀ r : F3, r ^ 2 ≠ (2 : F3) + 0 * r) :=
    ⟨by simpa using
      _root_.MazurTorsion.XOneThirteenFiniteField.two_not_square_F3⟩
  infer_instance

private noncomputable instance f25Field : Field F25 := by
  letI : Fact (∀ r : F5, r ^ 2 ≠ (2 : F5) + 0 * r) :=
    ⟨by simpa using
      _root_.MazurTorsion.XOneThirteenFiniteField.two_not_square_F5⟩
  infer_instance

private def quadraticPairEquiv (n : ℕ) (d : ZMod n) :
    _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n ≃
      QuadraticAlgebra (ZMod n) d 0 :=
  (QuadraticAlgebra.equivProd d 0).symm

private theorem quadraticPairEquiv_one (n : ℕ) (d : ZMod n) :
    quadraticPairEquiv n d
        _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairOne = 1 := by
  rfl

private theorem quadraticPairEquiv_add (n : ℕ) (d : ZMod n)
    (u v : _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n) :
    quadraticPairEquiv n d
        (_root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairAdd u v) =
      quadraticPairEquiv n d u + quadraticPairEquiv n d v := by
  rfl

private theorem quadraticPairEquiv_mul (n : ℕ) (d : ZMod n)
    (u v : _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n) :
    quadraticPairEquiv n d
        (_root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairMul d u v) =
      quadraticPairEquiv n d u * quadraticPairEquiv n d v := by
  apply QuadraticAlgebra.ext <;>
    simp [quadraticPairEquiv,
      _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairMul]

private theorem quadraticPairEquiv_natScale (n : ℕ) (d : ZMod n)
    (a : ℕ)
    (u : _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n) :
    quadraticPairEquiv n d
        (_root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairNatScale a u) =
      a * quadraticPairEquiv n d u := by
  apply QuadraticAlgebra.ext <;>
    simp [quadraticPairEquiv,
      _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairNatScale]

private theorem quadraticPairEquiv_pow (n : ℕ) (d : ZMod n)
    (u : _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n)
    (k : ℕ) :
    quadraticPairEquiv n d
        (_root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairPow d u k) =
      quadraticPairEquiv n d u ^ k := by
  induction k with
  | zero => exact quadraticPairEquiv_one n d
  | succ k ih =>
      rw [_root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairPow,
        quadraticPairEquiv_mul, ih, pow_succ]

private theorem quadraticPairEquiv_sexticValue (n : ℕ) (d : ZMod n)
    (u : _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n) :
    quadraticPairEquiv n d
        (_root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairSexticValue d u) =
      aeval (quadraticPairEquiv n d u)
        (XOneThirteenAffineCurve.sexticPolynomial
          (QuadraticAlgebra (ZMod n) d 0)) := by
  simp only [
    _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairSexticValue,
    quadraticPairEquiv_add, quadraticPairEquiv_pow,
    quadraticPairEquiv_natScale, quadraticPairEquiv_one]
  simp [XOneThirteenAffineCurve.sexticPolynomial, Polynomial.aeval_def]
  ring

private theorem quadraticPairAffineEquation_iff (n : ℕ) (d : ZMod n)
    (p : _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n ×
      _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n) :
    _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairMul d p.2 p.2 =
        _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairSexticValue d p.1 ↔
      quadraticPairEquiv n d p.2 ^ 2 =
        aeval (quadraticPairEquiv n d p.1)
          (XOneThirteenAffineCurve.sexticPolynomial
            (QuadraticAlgebra (ZMod n) d 0)) := by
  constructor
  · intro h
    have h' := congrArg (quadraticPairEquiv n d) h
    rw [quadraticPairEquiv_mul,
      quadraticPairEquiv_sexticValue] at h'
    simpa [pow_two] using h'
  · intro h
    apply (quadraticPairEquiv n d).injective
    rw [quadraticPairEquiv_mul,
      quadraticPairEquiv_sexticValue]
    simpa [pow_two] using h

private noncomputable def quadraticPairAffineSolutionEquiv
    (n : ℕ) (d : ZMod n) :
    _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticAffineSolution n d ≃
      XOneThirteenAffineCurve.Solution
        (QuadraticAlgebra (ZMod n) d 0)
        (QuadraticAlgebra (ZMod n) d 0) :=
  Equiv.subtypeEquiv
    (Equiv.prodCongr (quadraticPairEquiv n d) (quadraticPairEquiv n d))
    (quadraticPairAffineEquation_iff n d)

private theorem quadraticPairInfinityEquation_iff (n : ℕ) (d : ZMod n)
    (u : _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticPair n) :
    _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairMul d u u =
        _root_.MazurTorsion.XOneThirteenFiniteField.quadraticPairOne ↔
      quadraticPairEquiv n d u ^ 2 = 1 := by
  constructor
  · intro h
    have h' := congrArg (quadraticPairEquiv n d) h
    rw [quadraticPairEquiv_mul, quadraticPairEquiv_one] at h'
    simpa [pow_two] using h'
  · intro h
    apply (quadraticPairEquiv n d).injective
    rw [quadraticPairEquiv_mul, quadraticPairEquiv_one]
    simpa [pow_two] using h

private noncomputable def quadraticPairInfinityDirectionEquiv
    (n : ℕ) (d : ZMod n) :
    _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticInfinityDirection n d ≃
      {u : QuadraticAlgebra (ZMod n) d 0 // u ^ 2 = 1} :=
  Equiv.subtypeEquiv (quadraticPairEquiv n d)
    (quadraticPairInfinityEquation_iff n d)

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

/-- The checked eight-element quadratic-pair certificate is canonically
equivalent to genuine `𝔽₉`-rational points of the glued curve. -/
noncomputable def pointCertificateEquivCurveSectionF9 :
    _root_.MazurTorsion.XOneThirteenFiniteField.PointCertificateF9 ≃
      CurveSection F9 := by
  change (_root_.MazurTorsion.XOneThirteenFiniteField.QuadraticAffineSolution
      3 (2 : F3) ⊕
    _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticInfinityDirection
      3 (2 : F3)) ≃ CurveSection F9
  exact (Equiv.sumCongr
    ((quadraticPairAffineSolutionEquiv 3 (2 : F3)).trans
      (ordinarySolutionEquivSection F9))
    ((quadraticPairInfinityDirectionEquiv 3 (2 : F3)).trans
      (squareRootOneEquivReciprocalBoundarySection F9))).trans
        (curveSectionEquivChartSum F9).symm

/-- The checked twelve-element quadratic-pair certificate is canonically
equivalent to genuine `𝔽₂₅`-rational points of the glued curve. -/
noncomputable def pointCertificateEquivCurveSectionF25 :
    _root_.MazurTorsion.XOneThirteenFiniteField.PointCertificateF25 ≃
      CurveSection F25 := by
  change (_root_.MazurTorsion.XOneThirteenFiniteField.QuadraticAffineSolution
      5 (2 : F5) ⊕
    _root_.MazurTorsion.XOneThirteenFiniteField.QuadraticInfinityDirection
      5 (2 : F5)) ≃ CurveSection F25
  exact (Equiv.sumCongr
    ((quadraticPairAffineSolutionEquiv 5 (2 : F5)).trans
      (ordinarySolutionEquivSection F25))
    ((quadraticPairInfinityDirectionEquiv 5 (2 : F5)).trans
      (squareRootOneEquivReciprocalBoundarySection F25))).trans
        (curveSectionEquivChartSum F25).symm

noncomputable instance curveSectionFintypeF9 : Fintype (CurveSection F9) :=
  Fintype.ofEquiv
    _root_.MazurTorsion.XOneThirteenFiniteField.PointCertificateF9
    pointCertificateEquivCurveSectionF9

noncomputable instance curveSectionFintypeF25 : Fintype (CurveSection F25) :=
  Fintype.ofEquiv
    _root_.MazurTorsion.XOneThirteenFiniteField.PointCertificateF25
    pointCertificateEquivCurveSectionF25

/-- The actual glued projective curve has eight genuine `𝔽₉`-rational
points. -/
theorem card_curveSection_F9 : Fintype.card (CurveSection F9) = 8 := by
  rw [← Fintype.card_congr pointCertificateEquivCurveSectionF9]
  exact _root_.MazurTorsion.XOneThirteenFiniteField.card_pointCertificateF9

/-- The actual glued projective curve has twelve genuine `𝔽₂₅`-rational
points. -/
theorem card_curveSection_F25 : Fintype.card (CurveSection F25) = 12 := by
  rw [← Fintype.card_congr pointCertificateEquivCurveSectionF25]
  exact _root_.MazurTorsion.XOneThirteenFiniteField.card_pointCertificateF25

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
