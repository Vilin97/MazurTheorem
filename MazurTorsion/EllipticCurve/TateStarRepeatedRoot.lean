/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TateStarSimpleRoot

/-!
# The marked repeated-root branch of the exceptional star cubic

For a marked root `r` of `T^3 + A T + B`, vanishing of the derivative gives
`A = -3r^2` and `B = 2r^3` in the residue field.  This file develops the next pointwise branch
on the same selected short equation.  A nonzero repeated marked root forces the twelfth multiple
of the marked point into canonical nonsingular reduction.  The arithmetic consumers therefore
force the marked root to vanish, which increases the displayed coefficient and abscissa depths
without changing the model or the chosen uniformizer.

Only affine group-law and valuation consequences for the marked point are asserted.  No Kodaira
symbol, regular model, component incidence, or global component-group bound is constructed.
-/

noncomputable section

open IsLocalRing

namespace MazurTorsion.EllipticCurve

open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v

/-- An integral affine point whose abscissa is nonzero on the standard cuspidal special fibre
has canonical nonsingular reduction. -/
private theorem hasNonsingularReduction_of_integral_x_residue_ne_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (x y : v.adicCompletionIntegers K)
    (hxy : W.Nonsingular
      ((x : v.adicCompletionIntegers K) : v.adicCompletion K)
      ((y : v.adicCompletionIntegers K) : v.adicCompletion K))
    (hx : residue (v.adicCompletionIntegers K) x ≠ 0) :
    HasNonsingularReduction hW
      (.some ((x : v.adicCompletionIntegers K) : v.adicCompletion K)
        ((y : v.adicCompletionIntegers K) : v.adicCompletion K) hxy) := by
  have heq : W₀.toAffine.Equation x y :=
    equation_integral hW hxy.left x.property y.property
  have heqbar : (cuspidalShortCurve
      (ResidueField (v.adicCompletionIntegers K))).toAffine.Equation
      (residue (v.adicCompletionIntegers K) x)
      (residue (v.adicCompletionIntegers K) y) := by
    have hmap := WeierstrassCurve.Affine.Equation.map
      (residue (v.adicCompletionIntegers K)) heq
    change (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Equation
      (residue (v.adicCompletionIntegers K) x)
      (residue (v.adicCompletionIntegers K) y) at hmap
    rwa [hspecial] at hmap
  letI : Invertible (2 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h2
  letI : Invertible (3 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h3
  have hnonsingular :
      (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Nonsingular
        (residue (v.adicCompletionIntegers K) x)
        (residue (v.adicCompletionIntegers K) y) := by
    rw [hspecial]
    exact cuspidalShortCurve_nonsingular_of_ne_origin heqbar (Or.inl hx)
  intro hxgate
  have hint := integral_of_not_mem hW hxy.left hxgate
  have hxint : (⟨((x : v.adicCompletionIntegers K) : v.adicCompletion K), hint.1⟩ :
      v.adicCompletionIntegers K) = x := Subtype.ext rfl
  have hyint : (⟨((y : v.adicCompletionIntegers K) : v.adicCompletion K), hint.2⟩ :
      v.adicCompletionIntegers K) = y := Subtype.ext rfl
  rw [hxint, hyint]
  exact hnonsingular

/-- At a repeated marked exceptional-cubic root, the two coefficient residues are determined by
that root. -/
theorem markedExceptionalCubic_coefficients_of_derivative_eq_zero
    {O : Type u} {F : Type v} [CommRing O] [IsLocalRing O]
    [Field F] [Algebra O F]
    {W₀ : WeierstrassCurve O} {W : WeierstrassCurve.Affine F} {P : W.Point}
    (D : MarkedExceptionalCubicData W₀ W P)
    (hrepeated : D.derivativeResidue = 0) :
    residue O D.A = -3 * residue O D.X ^ 2 ∧
      residue O D.B = 2 * residue O D.X ^ 3 := by
  have hderivative : 3 * residue O D.X ^ 2 + residue O D.A = 0 := by
    change residue O (3 * D.X ^ 2 + D.A) = 0 at hrepeated
    simpa only [map_add, map_mul, map_pow, map_ofNat] using hrepeated
  constructor
  · linear_combination hderivative
  · have hroot := D.exceptionalCubic_root
    linear_combination hroot - residue O D.X * hderivative

/-- If the repeated marked root is zero, its abscissa and both displayed coefficients gain one
power of the same bundled uniformizer. -/
theorem markedExceptionalCubic_deeper_depths_of_derivative_eq_zero_of_root_eq_zero
    {O : Type u} {F : Type v} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    {W₀ : WeierstrassCurve O} {W : WeierstrassCurve.Affine F} {P : W.Point}
    (D : MarkedExceptionalCubicData W₀ W P)
    (hrepeated : D.derivativeResidue = 0)
    (hroot : residue O D.X = 0) :
    residue O D.A = 0 ∧ residue O D.B = 0 ∧
      D.x ∈ maximalIdeal O ^ 2 ∧
      W₀.a₄ ∈ maximalIdeal O ^ 3 ∧
      W₀.a₆ ∈ maximalIdeal O ^ 4 := by
  have hcoeff := markedExceptionalCubic_coefficients_of_derivative_eq_zero D hrepeated
  have hA : residue O D.A = 0 := by simpa [hroot] using hcoeff.1
  have hB : residue O D.B = 0 := by simpa [hroot] using hcoeff.2
  have hXmem : D.X ∈ maximalIdeal O := (residue_eq_zero_iff D.X).mp hroot
  have hAmem : D.A ∈ maximalIdeal O := (residue_eq_zero_iff D.A).mp hA
  have hBmem : D.B ∈ maximalIdeal O := (residue_eq_zero_iff D.B).mp hB
  have hmax : maximalIdeal O = Ideal.span {D.uniformizer} :=
    D.uniformizer_irreducible.maximalIdeal_eq
  have hXdiv := hXmem
  have hAdiv := hAmem
  have hBdiv := hBmem
  rw [hmax, Ideal.mem_span_singleton] at hXdiv hAdiv hBdiv
  obtain ⟨X₁, hX₁⟩ := hXdiv
  obtain ⟨A₁, hA₁⟩ := hAdiv
  obtain ⟨B₁, hB₁⟩ := hBdiv
  refine ⟨hA, hB, ?_, ?_, ?_⟩
  · rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨X₁, by rw [D.x_eq, hX₁]; ring⟩
  · rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨A₁, by rw [D.a₄_eq, hA₁]; ring⟩
  · rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨B₁, by rw [D.a₆_eq, hB₁]; ring⟩

/-- A nonzero repeated marked root forces the twelfth multiple of the marked point into canonical
nonsingular reduction.  If the tangent slope is nonintegral or a unit, the double is already in
canonical reduction.  Otherwise the double remains at the cusp with marked root `-2r`, which is
simple because its derivative is `3²r²`. -/
theorem twelve_nsmul_mem_nonsingularReductionSubgroup_of_repeatedExceptionalRoot_ne_zero
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hrepeated : D.derivativeResidue = 0)
    (hroot_ne : residue (v.adicCompletionIntegers K) D.X ≠ 0) :
    12 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  let H := nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)
  by_cases hdouble : 2 • P ∈ H
  · have htwelve := H.nsmul_mem hdouble 6
    rw [← mul_nsmul] at htwelve
    norm_num at htwelve
    exact htwelve
  have hcoeff :=
    markedExceptionalCubic_coefficients_of_derivative_eq_zero D hrepeated
  rcases D with ⟨ϖ, hϖ, x₀, y₀, hxy, hpoint, X, A, B,
    hx_eq, ha₄_eq, ha₆_eq, hy_sq, hroot⟩
  change W.Nonsingular (x₀ : v.adicCompletion K)
    (y₀ : v.adicCompletion K) at hxy
  change P = .some (x₀ : v.adicCompletion K)
    (y₀ : v.adicCompletion K) hxy at hpoint
  have hAres : residue (v.adicCompletionIntegers K) A =
      -3 * residue (v.adicCompletionIntegers K) X ^ 2 := hcoeff.1
  have hXres_ne : residue (v.adicCompletionIntegers K) X ≠ 0 := hroot_ne
  have ha₁ : W.a₁ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₁, W₀.a₁_of_isShortNF, map_zero]
  have ha₂ : W.a₂ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₂, W₀.a₂_of_isShortNF, map_zero]
  have ha₃ : W.a₃ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₃, W₀.a₃_of_isShortNF, map_zero]
  have hmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  have hϖmem : ϖ ∈ maximalIdeal (v.adicCompletionIntegers K) := by
    rw [hmax, Ideal.mem_span_singleton]
  have hϖres : residue (v.adicCompletionIntegers K) ϖ = 0 :=
    (residue_eq_zero_iff ϖ).mpr hϖmem
  have hxres : residue (v.adicCompletionIntegers K) x₀ = 0 := by
    rw [hx_eq]
    simp [hϖres]
  have hymax : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) hy_sq
  have hyres : residue (v.adicCompletionIntegers K) y₀ = 0 :=
    (residue_eq_zero_iff y₀).mpr hymax
  rcases eq_or_ne (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (W.negY (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) with
    hyneg | hyneg
  · apply (hdouble ?_).elim
    rw [hpoint, two_nsmul, Point.add_self_of_Y_eq hyneg]
    exact H.zero_mem
  by_cases hslopeint : Valued.v (W.slope
      (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) ≤ 1
  · let L : v.adicCompletionIntegers K :=
      ⟨W.slope
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)), hslopeint⟩
    let X₂ : v.adicCompletionIntegers K := L ^ 2 - 2 * x₀
    let Y₂ : v.adicCompletionIntegers K := L * (x₀ - X₂) - y₀
    have hX₂ : ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        W.addX
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
      change (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
        (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) ^ 2 -
          2 * (x₀ : v.adicCompletion K) = _
      rw [WeierstrassCurve.Affine.addX, ha₁, ha₂]
      ring
    have hY₂ : ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        W.addY
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
      change W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K) *
          ((x₀ : v.adicCompletion K) - (X₂ : v.adicCompletion K)) -
          (y₀ : v.adicCompletion K) = _
      rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY, ha₁, ha₃, hX₂]
      ring
    have hnot : ¬(((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K) ∧
        ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
          W.negY (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) :=
      fun h ↦ hyneg h.2
    have hsum : W.Nonsingular
        (W.addX
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))))
        (W.addY
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)))) :=
      W.nonsingular_add hxy hxy hnot
    have hsum' : W.Nonsingular
        ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
        ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) := by
      rw [hX₂, hY₂]
      exact hsum
    have hdouble_point : 2 • P =
        .some ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
          ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) hsum' := by
      rw [hpoint, two_nsmul, Point.add_some hnot, Point.some.injEq]
      exact ⟨hX₂.symm, hY₂.symm⟩
    by_cases hLmax : L ∈ maximalIdeal (v.adicCompletionIntegers K)
    · have hLdiv := hLmax
      rw [hmax, Ideal.mem_span_singleton] at hLdiv
      obtain ⟨L₁, hL₁⟩ := hLdiv
      let X₂q : v.adicCompletionIntegers K := ϖ * L₁ ^ 2 - 2 * X
      have hX₂eq : X₂ = ϖ * X₂q := by
        simp only [X₂, X₂q]
        rw [hL₁, hx_eq]
        ring
      have hLres : residue (v.adicCompletionIntegers K) L = 0 :=
        (residue_eq_zero_iff L).mpr hLmax
      have hX₂res : residue (v.adicCompletionIntegers K) X₂ = 0 := by
        simp [X₂, hLres, hxres]
      have hY₂res : residue (v.adicCompletionIntegers K) Y₂ = 0 := by
        simp [Y₂, hLres, hxres, hX₂res, hyres]
      have hX₂max : X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
        (residue_eq_zero_iff X₂).mp hX₂res
      have hY₂max : Y₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
        (residue_eq_zero_iff Y₂).mp hY₂res
      have ha₄sq : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
        rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ⟨A, ha₄_eq⟩
      have ha₆cube : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
        rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ⟨B, ha₆_eq⟩
      have heq₂ : W₀.toAffine.Equation X₂ Y₂ :=
        equation_integral hW hsum'.left X₂.property Y₂.property
      let D₂ := markedExceptionalCubicData_of_cusp W₀ W ϖ hϖ heq₂ hsum'
        hX₂max hY₂max ha₄sq ha₆cube hX₂eq ha₄_eq ha₆_eq
      have hX₂qres : residue (v.adicCompletionIntegers K) X₂q =
          -2 * residue (v.adicCompletionIntegers K) X := by
        simp only [X₂q, map_sub, map_mul, map_pow, map_ofNat, hϖres, zero_mul]
        ring
      have hD₂simple : D₂.derivativeResidue ≠ 0 := by
        have hnonzero :
            (3 : ResidueField (v.adicCompletionIntegers K)) ^ 2 *
                residue (v.adicCompletionIntegers K) X ^ 2 ≠ 0 :=
          mul_ne_zero (pow_ne_zero 2 h3) (pow_ne_zero 2 hXres_ne)
        intro hzero
        apply hnonzero
        change residue (v.adicCompletionIntegers K) (3 * X₂q ^ 2 + A) = 0 at hzero
        have hzero' : 3 * residue (v.adicCompletionIntegers K) X₂q ^ 2 +
            residue (v.adicCompletionIntegers K) A = 0 := by
          simpa only [map_add, map_mul, map_pow, map_ofNat] using hzero
        calc
          (3 : ResidueField (v.adicCompletionIntegers K)) ^ 2 *
              residue (v.adicCompletionIntegers K) X ^ 2 =
              3 * (-2 * residue (v.adicCompletionIntegers K) X) ^ 2 +
                (-3 * residue (v.adicCompletionIntegers K) X ^ 2) := by ring
          _ = 3 * residue (v.adicCompletionIntegers K) X₂q ^ 2 +
              residue (v.adicCompletionIntegers K) A := by rw [hX₂qres, hAres]
          _ = 0 := hzero'
      have hfour :=
        two_nsmul_mem_nonsingularReductionSubgroup_of_markedExceptionalCubic_simpleRoot
          hW h2 h3 hspecial D₂ hD₂simple
      have hfour' : 4 • P ∈ H := by
        have hfourDouble : 2 • (2 • P) ∈ H := hdouble_point.symm ▸ hfour
        have hfourMul : (2 * 2) • P ∈ H := by
          rw [mul_nsmul]
          exact hfourDouble
        norm_num at hfourMul
        exact hfourMul
      have htwelve := H.nsmul_mem hfour' 3
      rw [← mul_nsmul] at htwelve
      norm_num at htwelve
      exact htwelve
    · have hLunit : IsUnit L := IsLocalRing.notMem_maximalIdeal.mp hLmax
      have hLres : residue (v.adicCompletionIntegers K) L ≠ 0 :=
        (residue_ne_zero_iff_isUnit L).mpr hLunit
      have hX₂res : residue (v.adicCompletionIntegers K) X₂ =
          residue (v.adicCompletionIntegers K) L ^ 2 := by
        simp [X₂, hxres]
      have hX₂res_ne : residue (v.adicCompletionIntegers K) X₂ ≠ 0 := by
        rw [hX₂res]
        exact pow_ne_zero 2 hLres
      have hred₂ := hasNonsingularReduction_of_integral_x_residue_ne_zero
        hW h2 h3 hspecial X₂ Y₂ hsum' hX₂res_ne
      exact (hdouble (hdouble_point.symm ▸ hred₂)).elim
  · have hslope_ne : W.slope
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≠ 0 := by
      intro hzero
      apply hslopeint
      rw [hzero, map_zero]
      exact bot_le
    obtain ⟨d, hd⟩ : ∃ d : ℤ, Valued.v (W.slope
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) = exp d :=
      ⟨_, (exp_log ((Valued.v).pos_iff.mpr hslope_ne).ne').symm⟩
    have hd_not_le : ¬d ≤ 0 := by
      intro hle
      apply hslopeint
      rw [hd, ← exp_zero, exp_le_exp]
      exact hle
    have hd_one : 1 ≤ d := by omega
    have hslopepole : exp (1 : ℤ) ≤ Valued.v (W.slope
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
      rw [hd, exp_le_exp]
      exact hd_one
    have hformal := add_self_mem_filtration_of_slope hW hxy x₀.property hyneg hslopepole
    apply (hdouble ?_).elim
    rw [hpoint, two_nsmul]
    exact filtration_le_nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) hformal

end MazurTorsion.EllipticCurve
