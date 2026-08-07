/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.NonsingularReductionAdditive

/-!
# Canonical nonsingular reduction under integral changes of variables

An admissible change of variables over the completed valuation ring identifies both the formal
kernel and the nonsingular locus of the special fibre.  Consequently it transports the canonical
nonsingular-reduction predicate and subgroup on the generic fibres.

The proof treats the formal-kernel gate separately from affine reduction.  At a pole, adding an
integral translation does not change the valuation of the `x`-coordinate.  Away from the formal
kernel, all coordinates are integral; reducing the integral coordinate formula then turns the
claim into `variableChange_nonsingular` on the special fibre.
-/

noncomputable section

open IsLocalRing

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v

private theorem variableChange_x_pole_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {v : HeightOneSpectrum R}
    (C : WeierstrassCurve.VariableChange (v.adicCompletionIntegers K))
    (x : v.adicCompletion K) :
    let CK := C.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
    exp (2 : ℤ) ≤ Valued.v ((CK.u : v.adicCompletion K) ^ 2 * x + CK.r) ↔
      exp (2 : ℤ) ≤ Valued.v x := by
  let CK := C.map
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
  have hu : Valued.v (CK.u : v.adicCompletion K) = 1 := by
    change Valued.v
      ((C.u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1
    exact adicCompletionIntegers.isUnit_iff_valued_eq_one.mp C.u.isUnit
  have hr : Valued.v CK.r ≤ 1 := by
    change Valued.v
      ((C.r : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1
    exact C.r.2
  have hux : Valued.v ((CK.u : v.adicCompletion K) ^ 2 * x) =
      Valued.v x := by
    rw [map_mul, map_pow, hu]
    simp
  have hone : (1 : ℤᵐ⁰) < exp (2 : ℤ) := by
    rw [← exp_zero]
    exact exp_lt_exp.mpr (by omega)
  constructor
  · intro hX
    by_contra hx
    have hx' : Valued.v x < exp (2 : ℤ) := lt_of_not_ge hx
    have huX : Valued.v ((CK.u : v.adicCompletion K) ^ 2 * x) < exp (2 : ℤ) :=
      hux.trans_lt hx'
    have hr' : Valued.v CK.r < exp (2 : ℤ) := hr.trans_lt hone
    have hsum : Valued.v ((CK.u : v.adicCompletion K) ^ 2 * x + CK.r) <
        exp (2 : ℤ) :=
      (Valued.v.map_add _ _).trans_lt (max_lt huX hr')
    exact (not_lt_of_ge hX) hsum
  · intro hx
    have hlt : Valued.v CK.r <
        Valued.v ((CK.u : v.adicCompletion K) ^ 2 * x) := by
      rw [hux]
      exact lt_of_le_of_lt hr (hone.trans_le hx)
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hux]
    exact hx

private theorem residue_variableChange_x
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {v : HeightOneSpectrum R}
    (C : WeierstrassCurve.VariableChange (v.adicCompletionIntegers K))
    (x : v.adicCompletion K) (hx : Valued.v x ≤ 1)
    (hX : Valued.v
      (((C.map (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K))).u : v.adicCompletion K) ^ 2 * x +
          (C.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))).r) ≤ 1) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
        ⟨((C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).u : v.adicCompletion K) ^ 2 * x +
            (C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).r, hX⟩ =
      (((C.map (IsLocalRing.residue (v.adicCompletionIntegers K))).u :
          ResidueField (v.adicCompletionIntegers K)) ^ 2 *
        IsLocalRing.residue (v.adicCompletionIntegers K) ⟨x, hx⟩ +
        (C.map (IsLocalRing.residue (v.adicCompletionIntegers K))).r) := by
  let xi : v.adicCompletionIntegers K := ⟨x, hx⟩
  have heq :
      (⟨((C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).u : v.adicCompletion K) ^ 2 * x +
            (C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).r, hX⟩ : v.adicCompletionIntegers K) =
        (C.u : v.adicCompletionIntegers K) ^ 2 * xi + C.r := by
    apply Subtype.ext
    rfl
  rw [heq]
  simp [xi]

private theorem residue_variableChange_y
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {v : HeightOneSpectrum R}
    (C : WeierstrassCurve.VariableChange (v.adicCompletionIntegers K))
    (x y : v.adicCompletion K) (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hY : Valued.v
      (((C.map (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K))).u : v.adicCompletion K) ^ 3 * y +
          ((C.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))).u : v.adicCompletion K) ^ 2 *
              (C.map (algebraMap (v.adicCompletionIntegers K)
                (v.adicCompletion K))).s * x +
          (C.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))).t) ≤ 1) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
        ⟨((C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).u : v.adicCompletion K) ^ 3 * y +
            ((C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).u : v.adicCompletion K) ^ 2 *
                (C.map (algebraMap (v.adicCompletionIntegers K)
                  (v.adicCompletion K))).s * x +
            (C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).t, hY⟩ =
      (((C.map (IsLocalRing.residue (v.adicCompletionIntegers K))).u :
          ResidueField (v.adicCompletionIntegers K)) ^ 3 *
        IsLocalRing.residue (v.adicCompletionIntegers K) ⟨y, hy⟩ +
        ((C.map (IsLocalRing.residue (v.adicCompletionIntegers K))).u :
          ResidueField (v.adicCompletionIntegers K)) ^ 2 *
          (C.map (IsLocalRing.residue (v.adicCompletionIntegers K))).s *
          IsLocalRing.residue (v.adicCompletionIntegers K) ⟨x, hx⟩ +
        (C.map (IsLocalRing.residue (v.adicCompletionIntegers K))).t) := by
  let xi : v.adicCompletionIntegers K := ⟨x, hx⟩
  let yi : v.adicCompletionIntegers K := ⟨y, hy⟩
  have heq :
      (⟨((C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))).u : v.adicCompletion K) ^ 3 * y +
            ((C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).u : v.adicCompletion K) ^ 2 *
                (C.map (algebraMap (v.adicCompletionIntegers K)
                  (v.adicCompletion K))).s * x +
            (C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).t, hY⟩ : v.adicCompletionIntegers K) =
        (C.u : v.adicCompletionIntegers K) ^ 3 * yi +
          (C.u : v.adicCompletionIntegers K) ^ 2 * C.s * xi + C.t := by
    apply Subtype.ext
    rfl
  rw [heq]
  simp [xi, yi]

/-- An integral admissible change of variables transports the canonical nonsingular-reduction
predicate.  The displayed generic-fibre equality records that the integral transformed equation
is the model used to define reduction on the transformed point group. -/
theorem hasNonsingularReduction_equivVariableChange_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    (C : WeierstrassCurve.VariableChange (v.adicCompletionIntegers K))
    (hWC : (C • W₀).map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K)) • W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    (P : (C.map (algebraMap (v.adicCompletionIntegers K)
      (v.adicCompletion K)) • W).toAffine.Point) :
    HasNonsingularReduction hWC P ↔
      HasNonsingularReduction hW
        (Point.equivVariableChange W
          (C.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.equivVariableChange_some]
    constructor
    · intro hred hX
      have hx : ¬ exp (2 : ℤ) ≤ Valued.v x := by
        intro hx
        exact hX ((variableChange_x_pole_iff C x).mpr hx)
      have hxy := integral_of_not_mem hWC h.left hx
      have hXY := integral_of_not_mem hW
        ((variableChange_nonsingular W
          (C.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))) x y).mpr h).left hX
      have hspecial :
          ((C.map (IsLocalRing.residue
              (v.adicCompletionIntegers K))) • adicRedCurve W₀).toAffine.Nonsingular
            (IsLocalRing.residue (v.adicCompletionIntegers K)
              ⟨x, hxy.1⟩)
            (IsLocalRing.residue (v.adicCompletionIntegers K)
              ⟨y, hxy.2⟩) := by
        simpa only [WeierstrassCurve.map_variableChange] using hred hx
      have horiginal :=
        (variableChange_nonsingular (adicRedCurve W₀)
          (C.map (IsLocalRing.residue
            (v.adicCompletionIntegers K)))
          (IsLocalRing.residue (v.adicCompletionIntegers K) ⟨x, hxy.1⟩)
          (IsLocalRing.residue (v.adicCompletionIntegers K) ⟨y, hxy.2⟩)).mpr
            hspecial
      rw [residue_variableChange_x C x hxy.1 hXY.1,
        residue_variableChange_y C x y hxy.1 hxy.2 hXY.2]
      exact horiginal
    · intro hred hx
      have hX : ¬ exp (2 : ℤ) ≤ Valued.v
          (((C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).u : v.adicCompletion K) ^ 2 * x +
            (C.map (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K))).r) := by
        intro hX
        exact hx ((variableChange_x_pole_iff C x).mp hX)
      have hxy := integral_of_not_mem hWC h.left hx
      have hXY := integral_of_not_mem hW
        ((variableChange_nonsingular W
          (C.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))) x y).mpr h).left hX
      have horiginal := hred hX
      rw [residue_variableChange_x C x hxy.1 hXY.1,
        residue_variableChange_y C x y hxy.1 hxy.2 hXY.2] at horiginal
      have hspecial :=
        (variableChange_nonsingular (adicRedCurve W₀)
          (C.map (IsLocalRing.residue
            (v.adicCompletionIntegers K)))
          (IsLocalRing.residue (v.adicCompletionIntegers K) ⟨x, hxy.1⟩)
          (IsLocalRing.residue (v.adicCompletionIntegers K) ⟨y, hxy.2⟩)).mp
            horiginal
      simpa only [WeierstrassCurve.map_variableChange] using hspecial

/-- The point-group equivalence from an integral change identifies the two canonical
nonsingular-reduction subgroups. -/
theorem equivVariableChange_mem_nonsingularReductionSubgroup_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    (C : WeierstrassCurve.VariableChange (v.adicCompletionIntegers K))
    (hWC : (C • W₀).map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K)) • W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    (P : (C.map (algebraMap (v.adicCompletionIntegers K)
      (v.adicCompletion K)) • W).toAffine.Point) :
    P ∈ nonsingularReductionSubgroup hWC
        (nonsingularReduction_isAdditive hWC) ↔
      Point.equivVariableChange W
          (C.map (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K))) P ∈
        nonsingularReductionSubgroup hW
          (nonsingularReduction_isAdditive hW) := by
  change HasNonsingularReduction hWC P ↔
    HasNonsingularReduction hW
      (Point.equivVariableChange W
        (C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K))) P)
  exact hasNonsingularReduction_equivVariableChange_iff hW C hWC P

/-- A marked component multiple can be checked before or after an integral admissible change.
This is the downstream form used when a normalized Tate equation is accompanied by the inverse
image of a marked point on the original equation. -/
theorem nsmul_equivVariableChange_symm_mem_nonsingularReductionSubgroup_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    (C : WeierstrassCurve.VariableChange (v.adicCompletionIntegers K))
    (hWC : (C • W₀).map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K)) • W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    (n : ℕ) (P : W.Point) :
    n • (Point.equivVariableChange W
        (C.map (algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K)))).symm P ∈
      nonsingularReductionSubgroup hWC
        (nonsingularReduction_isAdditive hWC) ↔
    n • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  rw [equivVariableChange_mem_nonsingularReductionSubgroup_iff hW C hWC]
  simp

end WeierstrassCurve.Affine
