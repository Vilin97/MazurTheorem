/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassGeometricIntegrality
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Coefficient extension on the projective Weierstrass ambient plane

For a field extension `K → L`, this file constructs the graded coefficient map on
`K[X,Y,Z]`, verifies the irrelevant-ideal hypothesis for `Proj` from the coordinate generators,
and obtains the resulting projection `P²_L ⟶ P²_K`.  It fixes all three coordinates, sends the
Weierstrass cubic to the coefficient-extended cubic.  After normalizing all three coordinate
charts as polynomial rings, it proves their affine coefficient squares are pushouts, glues the
dual chart squares, and constructs the canonical isomorphism
`P²_K ×_{Spec K} Spec L ≅ P²_L` with both projection compatibilities.

The final declarations record two honest consumers needed by the geometric-integrality lane.  The
underlying `Proj` point map carries the coefficient-extended cubic zero locus exactly to the
original cubic zero locus, including after transport through the canonical projective-plane
pullback isomorphism.  An explicitly ambient-compatible `StandardChartComparison` identifies its
canonical open range with the pullback of the mapped cubic's `D₊(Z)` open.  A cubic base-change
isomorphism or scheme-level restriction of the ambient projection is not claimed here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped DirectSum

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Extend coefficients from `K` to `L` in the homogeneous coordinate ring of projective
two-space. -/
noncomputable def projectiveCoefficientMap :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) L :=
  MvPolynomial.map (algebraMap K L)

@[simp]
theorem projectiveCoefficientMap_C (a : K) :
    projectiveCoefficientMap (K := K) (L := L) (MvPolynomial.C a) =
      MvPolynomial.C (algebraMap K L a) := by
  simp [projectiveCoefficientMap]

@[simp]
theorem projectiveCoefficientMap_X (i : Fin 3) :
    projectiveCoefficientMap (K := K) (L := L) (MvPolynomial.X i) =
      MvPolynomial.X i := by
  simp [projectiveCoefficientMap]

/-- Coefficient extension preserves every homogeneous degree. -/
noncomputable def projectiveGradedCoefficientMap :
    homogeneousPieces K →+*ᵍ homogeneousPieces L where
  __ := projectiveCoefficientMap (K := K) (L := L)
  map_mem := fun h ↦ MvPolynomial.IsHomogeneous.map h (algebraMap K L)

@[simp]
theorem projectiveGradedCoefficientMap_X (i : Fin 3) :
    projectiveGradedCoefficientMap (K := K) (L := L) (MvPolynomial.X i) =
      MvPolynomial.X i :=
  projectiveCoefficientMap_X i

@[simp]
theorem projectiveGradedCoefficientMap_C (a : K) :
    projectiveGradedCoefficientMap (K := K) (L := L) (MvPolynomial.C a) =
      MvPolynomial.C (algebraMap K L a) :=
  projectiveCoefficientMap_C a

/-- Coefficient extension takes the actual homogeneous Weierstrass equation to the equation of
the mapped Weierstrass curve. -/
@[simp]
theorem projectiveCoefficientMap_polynomial (W : WeierstrassCurve K) :
    projectiveCoefficientMap (K := K) (L := L) W.toProjective.polynomial =
      (W.map (algebraMap K L)).toProjective.polynomial := by
  simp [projectiveCoefficientMap, WeierstrassCurve.Projective.polynomial]

@[simp]
theorem projectiveGradedCoefficientMap_polynomial (W : WeierstrassCurve K) :
    projectiveGradedCoefficientMap (K := K) (L := L) W.toProjective.polynomial =
      (W.map (algebraMap K L)).toProjective.polynomial :=
  projectiveCoefficientMap_polynomial W

/-- For the standard polynomial grading, the irrelevant ideal is contained in the ideal generated
by the coordinate variables.  The converse is not needed for `Proj.map`. -/
private theorem irrelevant_toIdeal_le_idealOfVars
    (F : Type u) [Field F] :
    (HomogeneousIdeal.irrelevant (homogeneousPieces F)).toIdeal ≤
      MvPolynomial.idealOfVars (Fin 3) F := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  change p ∈ MvPolynomial.idealOfVars (Fin 3) F
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 3) F),
    MvPolynomial.mem_pow_idealOfVars_iff']
  intro m hm
  by_contra hcoeff
  have hdegree : Finsupp.degree m = i := by
    rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
    exact hp hcoeff
  omega

/-- The irrelevant ideal after coefficient extension is covered by the mapped source irrelevant
ideal.  This is the exact hypothesis required by `Proj.map`, proved from the three coordinates
rather than postulated. -/
theorem projectiveGradedCoefficientMap_irrelevant_le :
    HomogeneousIdeal.irrelevant (homogeneousPieces L) ≤
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).map
        (projectiveGradedCoefficientMap (K := K) (L := L)) := by
  change (HomogeneousIdeal.irrelevant (homogeneousPieces L)).toIdeal ≤
    Ideal.map (projectiveGradedCoefficientMap (K := K) (L := L))
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal
  refine (irrelevant_toIdeal_le_idealOfVars L).trans ?_
  apply Ideal.span_le.2
  rintro _ ⟨i, rfl⟩
  rw [← projectiveCoefficientMap_X (K := K) (L := L) i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousPieces K) (by omega)
      (MvPolynomial.isHomogeneous_X K i))

/-- The projective-plane projection induced by extension of homogeneous-coordinate
coefficients. -/
noncomputable def projectivePlaneBaseChangeProjection :
    projectivePlane L ⟶ projectivePlane K :=
  Proj.map (projectiveGradedCoefficientMap (K := K) (L := L))
    (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L))

/-- The projective-plane projection pulls a coordinate basic open back to the same coordinate
basic open. -/
theorem projectivePlaneBaseChangeProjection_preimage_basicOpen (i : Fin 3) :
    projectivePlaneBaseChangeProjection (K := K) (L := L) ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i) =
      Proj.basicOpen (homogeneousPieces L) (MvPolynomial.X i) := by
  simpa only [projectivePlaneBaseChangeProjection,
    projectiveGradedCoefficientMap_X] using
      (Proj.map_preimage_basicOpen
        (projectiveGradedCoefficientMap (K := K) (L := L))
        (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L))
        (MvPolynomial.X i))

/-- Mathlib's degree-zero localized coefficient map gives the canonical commutative square on
the `i`th coordinate chart.  The `i = 2` specialization is the standard `D₊(Z)` square. -/
@[reassoc]
theorem coordinateAway_comp_projectivePlaneBaseChangeProjection (i : Fin 3) :
    Proj.awayι (homogeneousPieces L)
          (projectiveGradedCoefficientMap (K := K) (L := L) (MvPolynomial.X i))
          ((projectiveGradedCoefficientMap (K := K) (L := L)).map_mem
            (MvPolynomial.isHomogeneous_X K i)) (by omega) ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map
            (projectiveGradedCoefficientMap (K := K) (L := L))
            (MvPolynomial.X i))) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X K i) (by omega) := by
  exact Proj.awayι_comp_map
    (projectiveGradedCoefficientMap (K := K) (L := L))
    (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L))
    (by omega) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i)

/-- Swap the `i`th homogeneous coordinate with `Z`, preserving the standard grading. -/
noncomputable def projectiveCoordinateSwap (i : Fin 3) :
    homogeneousPieces K →+*ᵍ homogeneousPieces K where
  __ := (MvPolynomial.renameEquiv K (Equiv.swap i 2)).toRingHom
  map_mem := fun h ↦ h.rename_isHomogeneous

@[simp]
theorem projectiveCoordinateSwap_X (i j : Fin 3) :
    projectiveCoordinateSwap (K := K) i (MvPolynomial.X j) =
      MvPolynomial.X (Equiv.swap i 2 j) := by
  simp [projectiveCoordinateSwap, MvPolynomial.renameEquiv]

@[simp]
theorem projectiveCoordinateSwap_C (i : Fin 3) (a : K) :
    projectiveCoordinateSwap (K := K) i (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [projectiveCoordinateSwap, MvPolynomial.renameEquiv]

@[simp]
theorem projectiveCoordinateSwap_X_left (i : Fin 3) :
    projectiveCoordinateSwap (K := K) i (MvPolynomial.X i) = MvPolynomial.X 2 := by
  rw [projectiveCoordinateSwap_X, Equiv.swap_apply_left]

@[simp]
theorem projectiveCoordinateSwap_X_two (i : Fin 3) :
    projectiveCoordinateSwap (K := K) i (MvPolynomial.X 2) = MvPolynomial.X i := by
  rw [projectiveCoordinateSwap_X, Equiv.swap_apply_right]

theorem projectiveCoordinateSwap_involutive (i : Fin 3)
    (q : MvPolynomial (Fin 3) K) :
    projectiveCoordinateSwap i (projectiveCoordinateSwap i q) = q := by
  change MvPolynomial.rename (Equiv.swap i 2)
      (MvPolynomial.rename (Equiv.swap i 2) q) = q
  rw [MvPolynomial.rename_rename]
  rw [show (⇑(Equiv.swap i 2) ∘ ⇑(Equiv.swap i 2)) = id by
    funext x
    exact Equiv.swap_apply_self i 2 x]
  simp

/-- Rename the standard `Z ≠ 0` chart to the chart `X i ≠ 0`. -/
noncomputable def standardToCoordinateChart (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2) →+*
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) :=
  (projectiveCoordinateSwap_X_two (K := K) i) ▸
    HomogeneousLocalization.Away.map (projectiveCoordinateSwap (K := K) i)
      (MvPolynomial.X (2 : Fin 3))

/-- Rename the chart `X i ≠ 0` back to the standard `Z ≠ 0` chart. -/
noncomputable def coordinateToStandardChart (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) →+*
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2) :=
  (projectiveCoordinateSwap_X_left (K := K) i) ▸
    HomogeneousLocalization.Away.map (projectiveCoordinateSwap (K := K) i)
      (MvPolynomial.X i)

private theorem projectiveCoordinateSwap_awayMap_mk
    (i : Fin 3) (f f' : MvPolynomial (Fin 3) K)
    (hf : f ∈ homogeneousPieces K 1) (hf' : f' ∈ homogeneousPieces K 1)
    (hff : projectiveCoordinateSwap i f = f') {n : ℕ}
    (q : MvPolynomial (Fin 3) K) (hq : q ∈ homogeneousPieces K n) :
    ((hff ▸ HomogeneousLocalization.Away.map (projectiveCoordinateSwap i) f) :
      HomogeneousLocalization.Away (homogeneousPieces K) f →+*
        HomogeneousLocalization.Away (homogeneousPieces K) f')
        (HomogeneousLocalization.Away.mk (homogeneousPieces K) hf n q
          (by simpa using hq)) =
      HomogeneousLocalization.Away.mk (homogeneousPieces K) hf' n
        (projectiveCoordinateSwap i q)
        (by simpa using (projectiveCoordinateSwap i).map_mem hq) := by
  cases hff
  rw [show hf' = (projectiveCoordinateSwap i).map_mem hf from Subsingleton.elim _ _]
  simpa only using HomogeneousLocalization.Away.map_mk
    (projectiveCoordinateSwap i) f hf n q (by simpa using hq)

@[simp]
theorem standardToCoordinateChart_ratio (i j : Fin 3) :
    standardToCoordinateChart (K := K) i (coordinateChartRatio 2 j) =
      coordinateChartRatio i (Equiv.swap i 2 j) := by
  rw [coordinateChartRatio, coordinateChartRatio]
  change (((projectiveCoordinateSwap_X_two (K := K) i) ▸
      HomogeneousLocalization.Away.map (projectiveCoordinateSwap (K := K) i)
        (MvPolynomial.X (2 : Fin 3))) :
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2) →+*
        HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i))
    (HomogeneousLocalization.Away.mk _ _ 1 (MvPolynomial.X j) _) = _
  simpa only [projectiveCoordinateSwap_X] using
    projectiveCoordinateSwap_awayMap_mk (K := K) i (MvPolynomial.X 2)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K 2)
      (MvPolynomial.isHomogeneous_X K i) (projectiveCoordinateSwap_X_two i)
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)

@[simp]
theorem coordinateToStandardChart_ratio (i j : Fin 3) :
    coordinateToStandardChart (K := K) i (coordinateChartRatio i j) =
      coordinateChartRatio 2 (Equiv.swap i 2 j) := by
  rw [coordinateChartRatio, coordinateChartRatio]
  change (((projectiveCoordinateSwap_X_left (K := K) i) ▸
      HomogeneousLocalization.Away.map (projectiveCoordinateSwap (K := K) i)
        (MvPolynomial.X i)) :
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) →+*
        HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2))
    (HomogeneousLocalization.Away.mk _ _ 1 (MvPolynomial.X j) _) = _
  simpa only [projectiveCoordinateSwap_X] using
    projectiveCoordinateSwap_awayMap_mk (K := K) i (MvPolynomial.X i)
      (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X K i)
      (MvPolynomial.isHomogeneous_X K 2) (projectiveCoordinateSwap_X_left i)
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)

@[simp]
theorem standardToCoordinateChart_constant (i : Fin 3) (a : K) :
    standardToCoordinateChart (K := K) i (coordinateChartConstantHom 2 a) =
      coordinateChartConstantHom i a := by
  rw [coordinateChartConstantHom_apply, coordinateChartConstantHom_apply]
  change (((projectiveCoordinateSwap_X_two (K := K) i) ▸
      HomogeneousLocalization.Away.map (projectiveCoordinateSwap (K := K) i)
        (MvPolynomial.X (2 : Fin 3))) :
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2) →+*
        HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i))
    (HomogeneousLocalization.Away.mk _ _ 0 (MvPolynomial.C a) _) = _
  simpa only [map_zero, zero_smul, projectiveCoordinateSwap_C] using
    projectiveCoordinateSwap_awayMap_mk (K := K) i (MvPolynomial.X 2)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K 2)
      (MvPolynomial.isHomogeneous_X K i) (projectiveCoordinateSwap_X_two i)
      (MvPolynomial.C a) (MvPolynomial.isHomogeneous_C (R := K) (σ := Fin 3) a)

@[simp]
theorem coordinateToStandardChart_constant (i : Fin 3) (a : K) :
    coordinateToStandardChart (K := K) i (coordinateChartConstantHom i a) =
      coordinateChartConstantHom 2 a := by
  rw [coordinateChartConstantHom_apply, coordinateChartConstantHom_apply]
  change (((projectiveCoordinateSwap_X_left (K := K) i) ▸
      HomogeneousLocalization.Away.map (projectiveCoordinateSwap (K := K) i)
        (MvPolynomial.X i)) :
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) →+*
        HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2))
    (HomogeneousLocalization.Away.mk _ _ 0 (MvPolynomial.C a) _) = _
  simpa only [map_zero, zero_smul, projectiveCoordinateSwap_C] using
    projectiveCoordinateSwap_awayMap_mk (K := K) i (MvPolynomial.X i)
      (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X K i)
      (MvPolynomial.isHomogeneous_X K 2) (projectiveCoordinateSwap_X_left i)
      (MvPolynomial.C a) (MvPolynomial.isHomogeneous_C (R := K) (σ := Fin 3) a)

theorem coordinateToStandardChart_comp_standardToCoordinateChart (i : Fin 3) :
    (coordinateToStandardChart (K := K) i).comp (standardToCoordinateChart i) =
      RingHom.id _ := by
  apply chartRingHom_ext 2
  · ext a
    simp
  · intro j
    simp only [RingHom.coe_comp, Function.comp_apply, standardToCoordinateChart_ratio,
      coordinateToStandardChart_ratio, Equiv.swap_apply_self, RingHom.id_apply]

theorem standardToCoordinateChart_comp_coordinateToStandardChart (i : Fin 3) :
    (standardToCoordinateChart (K := K) i).comp (coordinateToStandardChart i) =
      RingHom.id _ := by
  apply chartRingHom_ext i
  · ext a
    simp
  · intro j
    simp only [RingHom.coe_comp, Function.comp_apply, coordinateToStandardChart_ratio,
      standardToCoordinateChart_ratio, Equiv.swap_apply_self, RingHom.id_apply]

/-- Coordinate permutation identifies every projective coordinate chart with `D₊(Z)`. -/
noncomputable def standardCoordinateChartRingEquiv (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2) ≃+*
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) where
  toFun := standardToCoordinateChart i
  invFun := coordinateToStandardChart i
  left_inv := DFunLike.congr_fun
    (coordinateToStandardChart_comp_standardToCoordinateChart i)
  right_inv := DFunLike.congr_fun
    (standardToCoordinateChart_comp_coordinateToStandardChart i)
  map_add' := map_add (standardToCoordinateChart i)
  map_mul' := map_mul (standardToCoordinateChart i)

@[simp]
theorem standardCoordinateChartRingEquiv_apply (i : Fin 3)
    (z : HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 2)) :
    standardCoordinateChartRingEquiv i z = standardToCoordinateChart i z := rfl

/-- Two-variable polynomials as Mathlib's nested bivariate polynomial ring. -/
noncomputable def twoVariablePolynomialEquiv :
    MvPolynomial (Fin 2) K ≃+* Polynomial (Polynomial K) :=
  (MvPolynomial.finSuccEquiv K 1).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)

@[simp]
theorem twoVariablePolynomialEquiv_C (a : K) :
    twoVariablePolynomialEquiv (K := K) (MvPolynomial.C a) =
      Polynomial.C (Polynomial.C a) := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      ((MvPolynomial.finSuccEquiv K 1) (MvPolynomial.C a)) = _
  rw [show (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) by
    simpa using (MvPolynomial.finSuccEquiv K 1).commutes a]
  rw [Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp]
theorem twoVariablePolynomialEquiv_X_zero :
    twoVariablePolynomialEquiv (K := K) (MvPolynomial.X 0) = Polynomial.X := by
  simp [twoVariablePolynomialEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp]
theorem twoVariablePolynomialEquiv_X_one :
    twoVariablePolynomialEquiv (K := K) (MvPolynomial.X 1) =
      Polynomial.C Polynomial.X := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      ((MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X 1)) = _
  rw [show (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) by
    simpa using
      (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1) (j := (0 : Fin 1)))]
  rw [Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

/-- A polynomial presentation of the `i`th projective coordinate chart. -/
noncomputable def coordinateChartPolynomialEquiv (i : Fin 3) :
    MvPolynomial (Fin 2) K ≃+*
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) :=
  twoVariablePolynomialEquiv (K := K) |>.trans
    (standardChartRingEquiv (K := K)) |>.trans
      (standardCoordinateChartRingEquiv i)

@[simp]
theorem coordinateChartPolynomialEquiv_C (i : Fin 3) (a : K) :
    coordinateChartPolynomialEquiv i (MvPolynomial.C a) =
      coordinateChartConstantHom i a := by
  simp [coordinateChartPolynomialEquiv, standardChartRingEquiv]

@[simp]
theorem coordinateChartPolynomialEquiv_X_zero (i : Fin 3) :
    coordinateChartPolynomialEquiv (K := K) i (MvPolynomial.X 0) =
      coordinateChartRatio i (Equiv.swap i 2 1) := by
  simp [coordinateChartPolynomialEquiv, standardChartRingEquiv]

@[simp]
theorem coordinateChartPolynomialEquiv_X_one (i : Fin 3) :
    coordinateChartPolynomialEquiv (K := K) i (MvPolynomial.X 1) =
      coordinateChartRatio i (Equiv.swap i 2 0) := by
  simp [coordinateChartPolynomialEquiv, standardChartRingEquiv]

/-- Coefficient extension on the normalized `i`th coordinate chart. -/
noncomputable def coordinateChartBaseChangeMap (i : Fin 3) :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) →+*
      HomogeneousLocalization.Away (homogeneousPieces L) (MvPolynomial.X i) :=
  (projectiveGradedCoefficientMap_X (K := K) (L := L) i) ▸
    HomogeneousLocalization.Away.map
      (projectiveGradedCoefficientMap (K := K) (L := L)) (MvPolynomial.X i)

private theorem projectiveCoefficient_awayMap_mk
    (f : MvPolynomial (Fin 3) K) (f' : MvPolynomial (Fin 3) L)
    (hf : f ∈ homogeneousPieces K 1) (hf' : f' ∈ homogeneousPieces L 1)
    (hff : projectiveGradedCoefficientMap f = f') {n : ℕ}
    (q : MvPolynomial (Fin 3) K) (hq : q ∈ homogeneousPieces K n) :
    ((hff ▸ HomogeneousLocalization.Away.map
        (projectiveGradedCoefficientMap (K := K) (L := L)) f) :
      HomogeneousLocalization.Away (homogeneousPieces K) f →+*
        HomogeneousLocalization.Away (homogeneousPieces L) f')
        (HomogeneousLocalization.Away.mk (homogeneousPieces K) hf n q
          (by simpa using hq)) =
      HomogeneousLocalization.Away.mk (homogeneousPieces L) hf' n
        (projectiveGradedCoefficientMap q)
        (by simpa using (projectiveGradedCoefficientMap (K := K) (L := L)).map_mem hq) := by
  cases hff
  rw [show hf' = (projectiveGradedCoefficientMap (K := K) (L := L)).map_mem hf from
    Subsingleton.elim _ _]
  simpa only using HomogeneousLocalization.Away.map_mk
    (projectiveGradedCoefficientMap (K := K) (L := L)) f hf n q (by simpa using hq)

@[simp]
theorem coordinateChartBaseChangeMap_ratio (i j : Fin 3) :
    coordinateChartBaseChangeMap (K := K) (L := L) i
        (coordinateChartRatio (K := K) i j) = coordinateChartRatio (K := L) i j := by
  rw [coordinateChartRatio, coordinateChartRatio]
  change (((projectiveGradedCoefficientMap_X (K := K) (L := L) i) ▸
      HomogeneousLocalization.Away.map
        (projectiveGradedCoefficientMap (K := K) (L := L)) (MvPolynomial.X i)) :
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) →+*
        HomogeneousLocalization.Away (homogeneousPieces L) (MvPolynomial.X i))
    (HomogeneousLocalization.Away.mk _ _ 1 (MvPolynomial.X j) _) = _
  simpa only [projectiveGradedCoefficientMap_X] using
    projectiveCoefficient_awayMap_mk (K := K) (L := L) (MvPolynomial.X i)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i)
      (MvPolynomial.isHomogeneous_X L i) (projectiveGradedCoefficientMap_X i)
      (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)

@[simp]
theorem coordinateChartBaseChangeMap_constant (i : Fin 3) (a : K) :
    coordinateChartBaseChangeMap (K := K) (L := L) i
        (coordinateChartConstantHom i a) =
      coordinateChartConstantHom i (algebraMap K L a) := by
  rw [coordinateChartConstantHom_apply, coordinateChartConstantHom_apply]
  change (((projectiveGradedCoefficientMap_X (K := K) (L := L) i) ▸
      HomogeneousLocalization.Away.map
        (projectiveGradedCoefficientMap (K := K) (L := L)) (MvPolynomial.X i)) :
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) →+*
        HomogeneousLocalization.Away (homogeneousPieces L) (MvPolynomial.X i))
    (HomogeneousLocalization.Away.mk _ _ 0 (MvPolynomial.C a) _) = _
  simpa only [map_zero, zero_smul, projectiveGradedCoefficientMap_C] using
    projectiveCoefficient_awayMap_mk (K := K) (L := L) (MvPolynomial.X i)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i)
      (MvPolynomial.isHomogeneous_X L i) (projectiveGradedCoefficientMap_X i)
      (MvPolynomial.C a) (MvPolynomial.isHomogeneous_C (R := K) (σ := Fin 3) a)

/-- The polynomial presentation commutes with extension of field coefficients. -/
theorem coordinateChartPolynomialEquiv_naturality (i : Fin 3) :
    (coordinateChartBaseChangeMap (K := K) (L := L) i).comp
        (coordinateChartPolynomialEquiv (K := K) i).toRingHom =
      (coordinateChartPolynomialEquiv (K := L) i).toRingHom.comp
        (MvPolynomial.map (algebraMap K L)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    fin_cases j <;> simp

/-- The normalized coordinate chart after coefficient extension is the affine ring pushout. -/
theorem coordinateChart_isPushout (i : Fin 3) :
    IsPushout
      (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (coordinateChartConstantHom (K := K) i))
      (CommRingCat.ofHom (coordinateChartConstantHom (K := L) i))
      (CommRingCat.ofHom (coordinateChartBaseChangeMap (K := K) (L := L) i)) := by
  letI : Algebra (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) L) :=
    MvPolynomial.algebraMvPolynomial
  let hpoly : IsPushout
      (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 2) K)))
      (CommRingCat.ofHom (algebraMap L (MvPolynomial (Fin 2) L)))
      (CommRingCat.ofHom (algebraMap
        (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) L))) :=
    CommRingCat.isPushout_iff_isPushout.mpr
      (inferInstance : Algebra.IsPushout K L
        (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) L))
  refine hpoly.of_iso (Iso.refl _) (Iso.refl _)
    (coordinateChartPolynomialEquiv (K := K) i).toCommRingCatIso
    (coordinateChartPolynomialEquiv (K := L) i).toCommRingCatIso
    (by simp) ?_ ?_ ?_
  · ext a
    simp
  · ext a
    simp
  · apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact (coordinateChartPolynomialEquiv_naturality
      (K := K) (L := L) i).symm

/-- Contravariantly, the affine coordinate-chart coefficient square is a scheme pullback. -/
theorem coordinateChart_isPullback (i : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (coordinateChartBaseChangeMap (K := K) (L := L) i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartConstantHom (K := L) i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartConstantHom (K := K) i)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  let h := (coordinateChart_isPushout (K := K) (L := L) i).op.map Scheme.Spec
  change IsPullback
      (Spec.map (CommRingCat.ofHom
        (coordinateChartBaseChangeMap (K := K) (L := L) i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartConstantHom (K := L) i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartConstantHom (K := K) i)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) at h
  exact h

/-- The three coordinate basic opens form an affine cover of projective two-space. -/
@[simps! X f]
noncomputable def coordinateAffineOpenCover (F : Type u) [Field F] :
    (projectivePlane F).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (homogeneousPieces F)
    (fun i : Fin 3 ↦ MvPolynomial.X i)
    (fun i ↦ MvPolynomial.isHomogeneous_X F i) (fun _ ↦ by omega)
    (irrelevant_toIdeal_le_idealOfVars F)

/-- The named chart map is the restriction of the ambient coefficient-extension projection. -/
private theorem coordinateAway_comp_projectivePlaneBaseChangeProjection_of_eq
    (i : Fin 3) (x : MvPolynomial (Fin 3) L) (hx : x ∈ homogeneousPieces L 1)
    (hXi : projectiveGradedCoefficientMap (K := K) (L := L) (MvPolynomial.X i) = x) :
    Proj.awayι (homogeneousPieces L) x hx (by omega) ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      Spec.map (CommRingCat.ofHom
          (hXi ▸ HomogeneousLocalization.Away.map
            (projectiveGradedCoefficientMap (K := K) (L := L)) (MvPolynomial.X i))) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X K i) (by omega) := by
  cases hXi
  rw [show hx = (projectiveGradedCoefficientMap (K := K) (L := L)).map_mem
    (MvPolynomial.isHomogeneous_X K i) from Subsingleton.elim _ _]
  simpa only using
    coordinateAway_comp_projectivePlaneBaseChangeProjection (K := K) (L := L) i

/-- The named chart map is the restriction of the ambient coefficient-extension projection. -/
@[reassoc]
theorem coordinateAway_comp_projectivePlaneBaseChangeProjection' (i : Fin 3) :
    Proj.awayι (homogeneousPieces L) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X L i) (by omega) ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      Spec.map (CommRingCat.ofHom
          (coordinateChartBaseChangeMap (K := K) (L := L) i)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X K i) (by omega) := by
  exact coordinateAway_comp_projectivePlaneBaseChangeProjection_of_eq
    (K := K) (L := L) i (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X L i)
      (projectiveGradedCoefficientMap_X i)

/-- Each coordinate-away square is the actual pullback of its open immersion. -/
theorem coordinateAway_isPullback (i : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (coordinateChartBaseChangeMap (K := K) (L := L) i)))
      (Proj.awayι (homogeneousPieces L) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X L i) (by omega))
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i) (by omega))
      (projectivePlaneBaseChangeProjection (K := K) (L := L)) := by
  letI : IsOpenImmersion
      (Proj.awayι (homogeneousPieces L) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X L i) (by omega)) := by
    dsimp only [Proj.awayι]
    infer_instance
  letI : IsOpenImmersion
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i) (by omega)) := by
    dsimp only [Proj.awayι]
    infer_instance
  apply IsOpenImmersion.isPullback
  · exact coordinateAway_comp_projectivePlaneBaseChangeProjection'
      (K := K) (L := L) i
  · have hpos : 0 < (1 : ℕ) := by omega
    calc
      projectivePlaneBaseChangeProjection (K := K) (L := L) ⁻¹ᵁ
          (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X K i) hpos).opensRange =
        projectivePlaneBaseChangeProjection (K := K) (L := L) ⁻¹ᵁ
          Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i) := congrArg _
            (Proj.opensRange_awayι (homogeneousPieces K) (MvPolynomial.X i)
              (MvPolynomial.isHomogeneous_X K i) hpos)
      _ = Proj.basicOpen (homogeneousPieces L) (MvPolynomial.X i) :=
        projectivePlaneBaseChangeProjection_preimage_basicOpen (K := K) (L := L) i
      _ = (Proj.awayι (homogeneousPieces L) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X L i) hpos).opensRange :=
        (Proj.opensRange_awayι (homogeneousPieces L) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X L i) hpos).symm

/-- The ambient projective plane is compatible with extension of the ground field: its
coefficient-extension square is an actual pullback.  The proof is local on the three standard
coordinate charts.  On each chart, `coordinateAway_isPullback` identifies the canonical open
pullback with the normalized affine chart, and `coordinateChart_isPullback` supplies the affine
base-change square. -/
theorem projectivePlaneBaseChange_isPullback :
    IsPullback
      (projectivePlaneBaseChangeProjection (K := K) (L := L))
      (projectivePlaneStructureMap L)
      (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _
    (coordinateAffineOpenCover K).openCover
  intro i
  change Fin 3 at i
  let hOpen := (coordinateAway_isPullback (K := K) (L := L) i).flip
  let hCanonical := IsPullback.of_hasPullback
    (projectivePlaneBaseChangeProjection (K := K) (L := L))
    ((coordinateAffineOpenCover K).openCover.f i)
  let e := hOpen.isoIsPullback _ _ hCanonical
  let hChart := coordinateChart_isPullback (K := K) (L := L) i
  refine hChart.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom]
    change Spec.map (CommRingCat.ofHom
        (coordinateChartBaseChangeMap (K := K) (L := L) i)) =
      e.hom ≫ pullback.snd _ _
    exact (hOpen.isoIsPullback_hom_snd _ _ hCanonical).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change _ = e.hom ≫ pullback.fst _ _ ≫ projectivePlaneStructureMap L
    rw [← Category.assoc, hOpen.isoIsPullback_hom_fst _ _ hCanonical]
    exact (awayι_comp_projectivePlaneStructureMap (K := L) i).symm
  · change Spec.map (CommRingCat.ofHom (coordinateChartConstantHom (K := K) i)) =
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i) (by omega) ≫
          projectivePlaneStructureMap K
    exact (awayι_comp_projectivePlaneStructureMap (K := K) i).symm
  · simp

/-- The canonical pullback of `P²_K` to `Spec L` is isomorphic to the concrete `P²_L` built from
`L[X,Y,Z]`. -/
noncomputable def projectivePlanePullbackIso :
    pullback
        (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅
      projectivePlane L :=
  (projectivePlaneBaseChange_isPullback (K := K) (L := L)).isoPullback.symm

/-- Under the projective-plane base-change isomorphism, the canonical first projection is the
homogeneous-coordinate coefficient-extension projection. -/
@[reassoc (attr := simp)]
theorem projectivePlanePullbackIso_hom_comp_projection :
    (projectivePlanePullbackIso (K := K) (L := L)).hom ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      pullback.fst
        (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (projectivePlaneBaseChange_isPullback (K := K) (L := L)).isoPullback_inv_fst

/-- Under the projective-plane base-change isomorphism, the structure map to `Spec L` is the
canonical second projection. -/
@[reassoc (attr := simp)]
theorem projectivePlanePullbackIso_hom_comp_structureMap :
    (projectivePlanePullbackIso (K := K) (L := L)).hom ≫
        projectivePlaneStructureMap L =
      pullback.snd
        (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (projectivePlaneBaseChange_isPullback (K := K) (L := L)).isoPullback_inv_snd

/-- The named standard `D₊(Z)` instance of the coordinate-away square. -/
@[reassoc]
theorem standardAway_comp_projectivePlaneBaseChangeProjection :
    Proj.awayι (homogeneousPieces L)
          (projectiveGradedCoefficientMap (K := K) (L := L)
            (MvPolynomial.X (2 : Fin 3)))
          ((projectiveGradedCoefficientMap (K := K) (L := L)).map_mem
            (MvPolynomial.isHomogeneous_X K 2)) (by omega) ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map
            (projectiveGradedCoefficientMap (K := K) (L := L))
            (MvPolynomial.X (2 : Fin 3)))) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X (2 : Fin 3))
          (MvPolynomial.isHomogeneous_X K 2) (by omega) :=
  coordinateAway_comp_projectivePlaneBaseChangeProjection (K := K) (L := L) 2

/-- On underlying projective-spectrum points, coefficient extension carries the mapped cubic zero
locus exactly into the original cubic zero locus.  This is the point-level content of the ambient
projection preserving the equation; it does not install a morphism between the reduced induced
cubic schemes. -/
theorem projectiveSpectrum_comap_mem_weierstrassZeroLocus_iff
    (W : WeierstrassCurve K) (p : ProjectiveSpectrum (homogeneousPieces L)) :
    ProjectiveSpectrum.comap
          (projectiveGradedCoefficientMap (K := K) (L := L))
          (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L)) p ∈
        ProjectiveSpectrum.zeroLocus (homogeneousPieces K)
          {W.toProjective.polynomial} ↔
      p ∈ ProjectiveSpectrum.zeroLocus (homogeneousPieces L)
        {(W.map (algebraMap K L)).toProjective.polynomial} := by
  rw [ProjectiveSpectrum.mem_zeroLocus, ProjectiveSpectrum.mem_zeroLocus]
  simp only [Set.singleton_subset_iff]
  change W.toProjective.polynomial ∈
      ((ProjectiveSpectrum.comap
          (projectiveGradedCoefficientMap (K := K) (L := L))
          (projectiveGradedCoefficientMap_irrelevant_le (K := K) (L := L)) p).1 :
        Set (MvPolynomial (Fin 3) K)) ↔
    (W.map (algebraMap K L)).toProjective.polynomial ∈
      (p.asHomogeneousIdeal : Set (MvPolynomial (Fin 3) L))
  change projectiveGradedCoefficientMap (K := K) (L := L)
      W.toProjective.polynomial ∈
        (p.asHomogeneousIdeal : Set (MvPolynomial (Fin 3) L)) ↔ _
  rw [projectiveGradedCoefficientMap_polynomial]

/-- The actual projective-plane pullback isomorphism transports the coefficient-extended
Weierstrass zero locus to the inverse image of the original zero locus under the canonical first
projection.  This is a downstream cubic consumer of both the global ambient isomorphism and its
projection compatibility; it remains deliberately at the underlying closed-set level. -/
theorem projectivePlanePullbackIso_mem_mappedWeierstrassZeroLocus_iff
    (W : WeierstrassCurve K)
    (q : (pullback
      (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme)) :
    (projectivePlanePullbackIso (K := K) (L := L)).hom q ∈
        ProjectiveSpectrum.zeroLocus (homogeneousPieces L)
          {(W.map (algebraMap K L)).toProjective.polynomial} ↔
      (pullback.fst
        (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) q ∈
        ProjectiveSpectrum.zeroLocus (homogeneousPieces K)
          {W.toProjective.polynomial} := by
  rw [← projectivePlanePullbackIso_hom_comp_projection (K := K) (L := L)]
  exact (projectiveSpectrum_comap_mem_weierstrassZeroLocus_iff
    (K := K) (L := L) W
      ((projectivePlanePullbackIso (K := K) (L := L)).hom q)).symm

/-- Extra compatibility required of a projective base-change comparison before it can be used
to transport the canonical coordinate open.  This equality is deliberately separate from
`StandardChartComparison`: neither its target isomorphism nor the ambient equality is constructed
in this file. -/
def StandardChartComparison.IsAmbientCompatible
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (D : StandardChartComparison W L) : Prop :=
  (D.targetBaseChangeIso.hom ≫ inclusion (W.map (algebraMap K L))) ≫
      projectivePlaneBaseChangeProjection (K := K) (L := L) =
    fieldBaseChangeAmbientMap W L

/-- An ambient-compatible comparison identifies the canonical standard open in the actual field
pullback with the inverse image of the mapped cubic's `D₊(Z)` open.  This is the compiled
downstream consumer of `StandardChartComparison.IsAmbientCompatible`; constructing the target
isomorphism and this equality remains explicit work. -/
theorem StandardChartComparison.canonicalStandardOpenMap_opensRange_eq_preimage_mapped
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (D : StandardChartComparison W L) (hD : D.IsAmbientCompatible W L) :
    (canonicalStandardOpenMap W L).opensRange =
      D.targetBaseChangeIso.hom ⁻¹ᵁ
        (inclusion (W.map (algebraMap K L)) ⁻¹ᵁ
          Proj.basicOpen (homogeneousPieces L) (MvPolynomial.X (2 : Fin 3))) := by
  rw [canonicalStandardOpenMap_opensRange_eq_preimage_basicOpen, ← hD]
  simp only [Scheme.Hom.comp_preimage,
    projectivePlaneBaseChangeProjection_preimage_basicOpen]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
