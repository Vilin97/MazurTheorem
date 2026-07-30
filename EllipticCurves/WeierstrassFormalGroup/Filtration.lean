/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
-/
module

public import EllipticCurves.WeierstrassFormalGroup.Foundations
public import EllipticCurves.IntegralModel
public import EllipticCurves.VariableChange
import all EllipticCurves.WeierstrassFormalGroup.Foundations

@[expose] public section

/-!
# The formal point, the filtration, and the structure of `E(K_v)`

Building on the valuation estimates, this file constructs the point `(t/w(t), -1/w(t))` of
`E(K_v)` attached to an `𝔪`-point of the formal group (`formalPoint`), proves the parametrization
is additive, and defines the filtration `E_{n+1}(K_v)` of points whose `x`-coordinate has a pole
of order at least `2(n+1)`.  It then proves torsion-freeness of the kernel of reduction `E₁(K_v)`
under the standard ramification condition, that every filtration step has finite index, and the
structure theorem: `E(K_v)` has a finite-index subgroup isomorphic to `(𝒪_v, +)`.
-/

open ChabautyColeman IsLocalRing MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
  {t : v.adicCompletionIntegers K}

variable [W.IsElliptic]

include hW in
/-- The parametrized point of the kernel of reduction attached to a parameter `t ∈ 𝔪`,
`t ≠ 0`, is nonsingular. -/
theorem formalPoint_nonsingular
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K)) (ht0 : t ≠ 0) :
    W.Nonsingular ((t : v.adicCompletion K) / (W₀.wEval t : v.adicCompletion K))
      (-1 / (W₀.wEval t : v.adicCompletion K)) := by
  exact W.chord_point_nonsingular (coe_wEval_eq hW ht) (coe_wEval_ne_zero ht ht0)
    W.isUnit_Δ.ne_zero

variable [DecidableEq (v.adicCompletion K)]

/-- The point of the kernel of reduction attached to an `𝔪`-point of the formal group of
the integral model `W₀`: the parameter `t` gives the affine point `(t/w(t), -1/w(t))`,
and `t = 0` gives the point at infinity. -/
noncomputable def formalPoint (z : W₀.formalGroupLaw.Points) : W.Point :=
  if h0 : (z () : v.adicCompletionIntegers K) = 0 then 0
  else .some _ _ (formalPoint_nonsingular hW (z ()).2 h0)

@[simp]
lemma formalPoint_of_param_eq_zero {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) = 0) : formalPoint hW z = 0 :=
  dif_pos h0

lemma formalPoint_of_param_ne_zero {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0) :
    formalPoint hW z = .some _ _ (formalPoint_nonsingular hW (z ()).2 h0) :=
  dif_neg h0

/-- The parametrization of the kernel of reduction is injective. -/
theorem formalPoint_injective : Function.Injective (formalPoint hW) := by
  intro z z' h
  have key : (z () : v.adicCompletionIntegers K) = z' () := by
    rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0 <;>
      rcases eq_or_ne (z' () : v.adicCompletionIntegers K) 0 with h0' | h0'
    · rw [h0, h0']
    · rw [formalPoint_of_param_eq_zero hW h0, formalPoint_of_param_ne_zero hW h0'] at h
      exact absurd h.symm (by simp)
    · rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_eq_zero hW h0'] at h
      exact absurd h (by simp)
    · rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_ne_zero hW h0'] at h
      simp only [Point.some.injEq] at h
      obtain ⟨hX, hY⟩ := h
      have hw0 := coe_wEval_ne_zero (W₀ := W₀) (z ()).2 h0
      have hw0' := coe_wEval_ne_zero (W₀ := W₀) (z' ()).2 h0'
      have hw : ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) =
          ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) := by
        field_simp at hY
        exact (neg_injective hY).symm
      rw [hw, div_eq_div_iff hw0' hw0'] at hX
      exact_mod_cast mul_right_cancel₀ hw0' hX
  funext i
  exact Subtype.ext key

/-- Every affine point with a pole of order at least `2` at `x` comes from a parameter
in `𝔪`. -/
theorem exists_formalPoint_eq_some {x y : v.adicCompletion K} (h : W.Nonsingular x y)
    (hx : exp (2 : ℤ) ≤ Valued.v x) :
    ∃ z : W₀.formalGroupLaw.Points, formalPoint hW z = .some x y h := by
  obtain ⟨hy0, hs, hr⟩ := valued_of_mem hW h.left hx
  have hexp1 : (exp (-1 : ℤ) : ℤᵐ⁰) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]
    lia
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    simp at hx
  set t : v.adicCompletionIntegers K :=
    ⟨-x / y, by rw [mem_adicCompletionIntegers]; exact hs.trans hexp1⟩ with htdef
  set r : v.adicCompletionIntegers K :=
    ⟨-1 / y, by rw [mem_adicCompletionIntegers]; exact hr.trans hexp1⟩ with hrdef
  have htm : t ∈ maximalIdeal (v.adicCompletionIntegers K) := mem_maximalIdeal_iff.mpr hs
  have hrm : r ∈ maximalIdeal (v.adicCompletionIntegers K) := mem_maximalIdeal_iff.mpr hr
  have ht0 : t ≠ 0 := by
    intro hteq
    have h0 : (-x / y : v.adicCompletion K) = 0 := congrArg Subtype.val hteq
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    exact h0.elim hx0 hy0
  -- `-1/y` satisfies the Weierstrass fixed-point equation at the parameter `-x/y`
  have hfixK : (-1 / y : v.adicCompletion K) =
      (-x / y) ^ 3 + W.a₁ * (-x / y) * (-1 / y) + W.a₂ * (-x / y) ^ 2 * (-1 / y) +
        W.a₃ * (-1 / y) ^ 2 + W.a₄ * (-x / y) * (-1 / y) ^ 2 + W.a₆ * (-1 / y) ^ 3 := by
    have heq := (W.equation_iff x y).mp h.left
    field_simp
    linear_combination -heq
  have hfixO : r = W₀.wPoly t r := by
    refine Subtype.coe_injective ?_
    rw [wPoly]
    push_cast
    rw [coe_a₁ hW, coe_a₂ hW, coe_a₃ hW, coe_a₄ hW, coe_a₆ hW]
    exact hfixK
  have huniq : W₀.wEval t = r :=
    W₀.eq_of_wPoly_fixed htm (W₀.wEval_mem htm) hrm (W₀.wEval_eq htm) hfixO
  refine ⟨fun _ ↦ ⟨t, htm⟩, ?_⟩
  rw [formalPoint_of_param_ne_zero hW ht0]
  simp only [Point.some.injEq]
  have hrcoe : ((W₀.wEval t : v.adicCompletionIntegers K) : v.adicCompletion K) = -1 / y := by
    rw [huniq]
  constructor
  · rw [hrcoe]
    change (-x / y) / (-1 / y) = x
    field_simp
  · rw [hrcoe]
    show -1 / (-1 / y) = y
    field_simp

theorem formalPoint_eq_zero_iff {z : W₀.formalGroupLaw.Points} :
    formalPoint hW z = 0 ↔ (z () : v.adicCompletionIntegers K) = 0 := by
  refine ⟨fun h ↦ ?_, formalPoint_of_param_eq_zero hW⟩
  by_contra h0
  rw [formalPoint_of_param_ne_zero hW h0] at h
  exact absurd h (by simp)

include hW in
/-- The parametrization intertwines the formal inverse with negation of points. -/
theorem formalPoint_negPoint (z : W₀.formalGroupLaw.Points) :
    formalPoint hW (W₀.negPoint z) = -formalPoint hW z := by
  rcases eq_or_ne ((z ()) : v.adicCompletionIntegers K) 0 with h0 | h0
  · rw [formalPoint_of_param_eq_zero hW h0, formalPoint_of_param_eq_zero hW
      (by rw [W₀.negPoint_apply_coe, h0, W₀.iotaEval_zero]), neg_zero]
  · have hm := (z ()).2
    have hι0 : W₀.iotaEval (z () : v.adicCompletionIntegers K) ≠ 0 :=
      W₀.iotaEval_ne_zero hm h0
    rw [formalPoint_of_param_ne_zero hW h0,
      formalPoint_of_param_ne_zero hW (by rw [W₀.negPoint_apply_coe]; exact hι0),
      Point.neg_some]
    simp only [Point.some.injEq, W₀.negPoint_apply_coe]
    have hWT0 := coe_wEval_ne_zero (W₀ := W₀) hm h0
    have hDU0 := coe_duEval_ne_zero (W₀ := W₀) hm
    constructor
    · rw [coe_iotaEval_eq hm, coe_wEval_iotaEval hm]
      field_simp
    · rw [coe_wEval_iotaEval hm, Affine.negY]
      field_simp
      linear_combination -coe_uEval_mul_duEval hm +
        ((W₀.duEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) *
          coe_uEval_eq hW hm

include hW in
/-- The chord addition at the level of parameters: for `t₁, t₂ ∈ 𝔪` nonzero with distinct
`x`-coordinates and nonvanishing third root `T`, the sum of the parametrized points is the
point with parameter `ι̂(T)`. -/
private lemma paramPoint_add {t₁ t₂ : v.adicCompletionIntegers K}
    (hm : t₁ ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hm' : t₂ ∈ maximalIdeal (v.adicCompletionIntegers K))
    (h0 : t₁ ≠ 0) (h0' : t₂ ≠ 0)
    (hx : ((t₁ : v.adicCompletion K)) *
        ((W₀.wEval t₂ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠
      ((t₂ : v.adicCompletion K)) *
        ((W₀.wEval t₁ : v.adicCompletionIntegers K) : v.adicCompletion K))
    (hT0 : W₀.thirdRootEval t₁ t₂ ≠ 0)
    (hιm : W₀.iotaEval (W₀.thirdRootEval t₁ t₂) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hι0 : W₀.iotaEval (W₀.thirdRootEval t₁ t₂) ≠ 0) :
    (.some _ _ (formalPoint_nonsingular hW hm h0) : W.Point) +
        .some _ _ (formalPoint_nonsingular hW hm' h0') =
      .some _ _ (formalPoint_nonsingular hW hιm hι0) := by
  have hTm : W₀.thirdRootEval t₁ t₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    W₀.thirdRootEval_mem hm hm'
  -- coerced hypotheses for the field-level chord lemma
  have hslope := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.slopeEval_mul_sub hm hm')
  have hNc := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.interceptEval_eq hm hm')
  have hT₃c := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.thirdRootEval_relation hm hm')
  have hwTc := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K))
    (W₀.wEval_thirdRootEval hm hm')
  push_cast at hslope hNc hT₃c hwTc
  rw [coe_a₁ hW, coe_a₂ hW, coe_a₃ hW, coe_a₄ hW, coe_a₆ hW] at hT₃c
  have hAc := coe_chordCoeff_ne_zero hW (W₀.slopeEval_mem hm hm')
  have hw₁0 := coe_wEval_ne_zero (W₀ := W₀) hm h0
  have hw₂0 := coe_wEval_ne_zero (W₀ := W₀) hm' h0'
  have hwT0 := coe_wEval_ne_zero (W₀ := W₀) hTm hT0
  obtain ⟨h₃, hsum⟩ := W.chord_point_add (coe_wEval_eq hW hm) (coe_wEval_eq hW hm')
    hslope hNc hT₃c hwTc hAc hw₁0 hw₂0 hwT0 (sub_ne_zero.mpr hx)
    (formalPoint_nonsingular hW hm h0) (formalPoint_nonsingular hW hm' h0')
  rw [hsum]
  simp only [Point.some.injEq]
  -- identify the chord point with the parametrized point at `ι̂(T)`
  have hDU0 := coe_duEval_ne_zero (W₀ := W₀) hTm
  constructor
  · rw [coe_iotaEval_eq hTm, coe_wEval_iotaEval hTm]
    field_simp
  · rw [coe_wEval_iotaEval hTm]
    field_simp
    linear_combination coe_uEval_mul_duEval hTm -
      ((W₀.duEval (W₀.thirdRootEval t₁ t₂) : v.adicCompletionIntegers K) :
        v.adicCompletion K) * coe_uEval_eq hW hTm

include hW in
/-- The chord case of additivity: two nonzero parameters whose points have distinct
`x`-coordinates. -/
private lemma formalPoint_add_of_x_ne {z z' : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h0' : (z' () : v.adicCompletionIntegers K) ≠ 0)
    (hx : ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) ≠
      ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K)) :
    formalPoint hW (z + z') = formalPoint hW z + formalPoint hW z' := by
  have hm := (z ()).2
  have hm' := (z' ()).2
  -- the third root does not vanish (else the chord would be vertical)
  have hT0 : W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
      (z' () : v.adicCompletionIntegers K) ≠ 0 :=
    W₀.thirdRootEval_ne_zero hm hm' fun hc ↦ hx (by
      have := congrArg (fun a : v.adicCompletionIntegers K ↦ (a : v.adicCompletion K)) hc
      push_cast at this
      exact this)
  have hTm := W₀.thirdRootEval_mem hm hm'
  have hιm : W₀.iotaEval (W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
      (z' () : v.adicCompletionIntegers K)) ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    W₀.iotaEval_mem hTm
  have hι0 : W₀.iotaEval (W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
      (z' () : v.adicCompletionIntegers K)) ≠ 0 := W₀.iotaEval_ne_zero hTm hT0
  have hpcoe : ((z + z') () : v.adicCompletionIntegers K) =
      W₀.iotaEval (W₀.thirdRootEval (z () : v.adicCompletionIntegers K)
        (z' () : v.adicCompletionIntegers K)) := by
    rw [W₀.add_apply_coe_eq_addEval, W₀.addEval_eq hm hm']
  have hp0 : ((z + z') () : v.adicCompletionIntegers K) ≠ 0 := by
    rw [hpcoe]
    exact hι0
  rw [formalPoint_of_param_ne_zero hW h0, formalPoint_of_param_ne_zero hW h0',
    formalPoint_of_param_ne_zero hW hp0,
    paramPoint_add hW hm hm' h0 h0' hx hT0 hιm hι0]
  simp only [hpcoe]

omit [DecidableEq (v.adicCompletion K)] in
include hW in
/-- Two nonzero parameters whose points share their `x`-coordinate agree up to the formal
inverse. -/
private lemma eq_or_eq_negPoint_of_x_cond {z z' : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h0' : (z' () : v.adicCompletionIntegers K) ≠ 0)
    (hx : ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) *
        ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K)) :
    z' = z ∨ z' = W₀.negPoint z := by
  classical
  have hm := (z ()).2
  have hm' := (z' ()).2
  have hWT0 := coe_wEval_ne_zero (W₀ := W₀) hm h0
  have hWT0' := coe_wEval_ne_zero (W₀ := W₀) hm' h0'
  have hns := formalPoint_nonsingular hW hm h0
  have hns' := formalPoint_nonsingular hW hm' h0'
  have hxeq : ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) /
      ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) /
        ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) := by
    rw [div_eq_div_iff hWT0' hWT0]
    linear_combination -hx
  rcases W.Y_eq_of_X_eq hns'.left hns.left hxeq with hy | hy
  · left
    refine formalPoint_injective hW ?_
    rw [formalPoint_of_param_ne_zero hW h0', formalPoint_of_param_ne_zero hW h0]
    simp only [Point.some.injEq]
    exact ⟨hxeq, hy⟩
  · right
    refine formalPoint_injective hW ?_
    rw [formalPoint_negPoint hW, formalPoint_of_param_ne_zero hW h0',
      formalPoint_of_param_ne_zero hW h0, Point.neg_some]
    simp only [Point.some.injEq]
    exact ⟨hxeq, hy⟩

include hW in
/-- Additivity of the parametrization when the parameters are distinct and not related by
the formal inverse. -/
private lemma formalPoint_add_of_ne {z z' : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h0' : (z' () : v.adicCompletionIntegers K) ≠ 0)
    (hne : z' ≠ z) (hnneg : z' ≠ W₀.negPoint z) :
    formalPoint hW (z + z') = formalPoint hW z + formalPoint hW z' := by
  refine formalPoint_add_of_x_ne hW h0 h0' fun hx ↦ ?_
  rcases eq_or_eq_negPoint_of_x_cond hW h0 h0' hx with h | h
  · exact hne h
  · exact hnneg h

include hW in
/-- If additivity holds for a pair whose second point is not the negative of the first,
the parameter of the sum does not vanish. -/
private lemma add_param_ne_zero {z w : W₀.formalGroupLaw.Points}
    (hc : formalPoint hW (z + w) = formalPoint hW z + formalPoint hW w)
    (hne : w ≠ W₀.negPoint z) :
    ((z + w) () : v.adicCompletionIntegers K) ≠ 0 := by
  intro h
  rw [formalPoint_of_param_eq_zero hW h] at hc
  refine hne (formalPoint_injective hW ?_)
  rw [formalPoint_negPoint hW]
  exact eq_neg_of_add_eq_zero_right hc.symm

variable [CharZero K]

include hW in
/-- The doubling case of additivity, via an auxiliary point of very small valuation
(which turns all needed additions into chord cases). -/
private lemma formalPoint_add_self {z : W₀.formalGroupLaw.Points}
    (h0 : (z () : v.adicCompletionIntegers K) ≠ 0)
    (h2t : (z () : v.adicCompletionIntegers K) ≠ W₀.iotaEval (z ())) :
    formalPoint hW (z + z) = formalPoint hW z + formalPoint hW z := by
  obtain ⟨u, hu0, hune, hunneg, hnune, hnunneg, huιu⟩ := exists_aux_point h0
  have hnu0 : ((W₀.negPoint u) () : v.adicCompletionIntegers K) ≠ 0 := by
    rw [W₀.negPoint_apply_coe]
    exact W₀.iotaEval_ne_zero (u ()).2 hu0
  have c1 : formalPoint hW (z + u) = formalPoint hW z + formalPoint hW u :=
    formalPoint_add_of_ne hW h0 hu0 hune hunneg
  have c2 : formalPoint hW (z + W₀.negPoint u) =
      formalPoint hW z + formalPoint hW (W₀.negPoint u) :=
    formalPoint_add_of_ne hW h0 hnu0 hnune hnunneg
  have hcne : z + W₀.negPoint u ≠ z + u := by
    intro h
    have h' := congrArg (formalPoint hW) h
    rw [c1, c2] at h'
    have h3 := congrArg (fun w ↦ (w () : v.adicCompletionIntegers K))
      (formalPoint_injective hW (add_left_cancel h'))
    rw [W₀.negPoint_apply_coe] at h3
    exact huιu h3.symm
  have hcnneg : z + W₀.negPoint u ≠ W₀.negPoint (z + u) := by
    intro h
    have h' := congrArg (formalPoint hW) h
    simp only [c1, c2, formalPoint_negPoint hW, neg_add] at h'
    have h'' := add_right_cancel h'
    rw [← formalPoint_negPoint hW] at h''
    exact h2t (congrArg (fun w ↦ (w () : v.adicCompletionIntegers K))
      (formalPoint_injective hW h''))
  have c3 : formalPoint hW ((z + u) + (z + W₀.negPoint u)) =
      formalPoint hW (z + u) + formalPoint hW (z + W₀.negPoint u) :=
    formalPoint_add_of_ne hW (add_param_ne_zero hW c1 hunneg)
      (add_param_ne_zero hW c2 hnunneg) hcne hcnneg
  have hkey : (z + u) + (z + W₀.negPoint u) = z + z := by
    rw [add_add_add_comm, W₀.add_negPoint, add_zero]
  rw [← hkey, c3, c1, c2, formalPoint_negPoint hW]
  abel

include hW in
/-- The parametrization of the kernel of reduction is additive. -/
theorem formalPoint_add (z z' : W₀.formalGroupLaw.Points) :
    formalPoint hW (z + z') = formalPoint hW z + formalPoint hW z' := by
  rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0
  · have hz : z = 0 := funext fun _ ↦ Subtype.ext h0
    rw [hz, zero_add, formalPoint_of_param_eq_zero hW (z := 0) (by simp), zero_add]
  rcases eq_or_ne (z' () : v.adicCompletionIntegers K) 0 with h0' | h0'
  · have hz' : z' = 0 := funext fun _ ↦ Subtype.ext h0'
    rw [hz', add_zero, formalPoint_of_param_eq_zero hW (z := 0) (by simp), add_zero]
  rcases eq_or_ne (z' () : v.adicCompletionIntegers K) (W₀.iotaEval (z ())) with hinv | hinv
  · have hz' : z' = W₀.negPoint z := funext fun _ ↦ Subtype.ext hinv
    rw [hz', W₀.add_negPoint, formalPoint_of_param_eq_zero hW (z := 0) (by simp),
      formalPoint_negPoint hW, add_neg_cancel]
  rcases eq_or_ne (z' () : v.adicCompletionIntegers K) (z () : v.adicCompletionIntegers K)
    with heqp | hnep
  · have hz' : z' = z := funext fun _ ↦ Subtype.ext heqp
    rw [hz']
    exact formalPoint_add_self hW h0 fun h ↦ hinv (heqp.trans h)
  · exact formalPoint_add_of_ne hW h0 h0'
      (fun h ↦ hnep (congrArg (fun w ↦ (w () : v.adicCompletionIntegers K)) h))
      (fun h ↦ hinv (congrArg (fun w ↦ (w () : v.adicCompletionIntegers K)) h))

/-- For an elliptic curve `W` over `K_v` with an integral model `W₀` and `n : ℕ`, the
subgroup `E_{n+1}(K_v)` of points `(x, y)` with `exp (2 * (n + 1)) ≤ v(x)` (a pole of order
at least `2(n + 1)` at `x`, together with `0`); this is the kernel of reduction modulo
`𝔪^(n+1)`, isomorphic to the group `Ê(𝔪^(n+1))` of points of the formal group of `W₀`
(Silverman, VII.2.2).  Closure under addition comes from the formal group: both summands
are parametrized by `𝔪^(n+1)`-parameters, and the addition series preserves that level. -/
def filtration (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) (n : ℕ) : AddSubgroup W.Point where
  carrier := {P | match P with
    | .zero => True
    | .some x _ _ => exp (2 * (n + 1) : ℤ) ≤ Valued.v x}
  zero_mem' := trivial
  neg_mem' {P} hP := by
    match P with
    | .zero => exact hP
    | .some x y h => rw [Set.mem_setOf_eq, Point.neg_some]; exact hP
  add_mem' {P Q} hP hQ := by
    match P, Q with
    | .zero, Q =>
      rw [show (Point.zero : W.Point) = 0 from rfl, zero_add]
      exact hQ
    | .some x₁ y₁ h₁, .zero =>
      rw [show (Point.zero : W.Point) = 0 from rfl, add_zero]
      exact hP
    | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
      rw [Set.mem_setOf_eq] at hP hQ
      obtain ⟨z, hz⟩ := exists_formalPoint_eq_some hW h₁
        (le_trans (exp_le_exp.mpr (by lia)) hP)
      obtain ⟨z', hz'⟩ := exists_formalPoint_eq_some hW h₂
        (le_trans (exp_le_exp.mpr (by lia)) hQ)
      have h0 : (z () : v.adicCompletionIntegers K) ≠ 0 := by
        intro h
        rw [formalPoint_of_param_eq_zero hW h] at hz
        exact absurd hz (by simp)
      have h0' : (z' () : v.adicCompletionIntegers K) ≠ 0 := by
        intro h
        rw [formalPoint_of_param_eq_zero hW h] at hz'
        exact absurd hz' (by simp)
      have hx₁ : ((z () : v.adicCompletionIntegers K) : v.adicCompletion K) /
          ((W₀.wEval (z ()) : v.adicCompletionIntegers K) : v.adicCompletion K) = x₁ := by
        have hz2 := hz
        rw [formalPoint_of_param_ne_zero hW h0] at hz2
        simp only [Point.some.injEq] at hz2
        exact hz2.1
      have hx₂ : ((z' () : v.adicCompletionIntegers K) : v.adicCompletion K) /
          ((W₀.wEval (z' ()) : v.adicCompletionIntegers K) : v.adicCompletion K) = x₂ := by
        have hz2 := hz'
        rw [formalPoint_of_param_ne_zero hW h0'] at hz2
        simp only [Point.some.injEq] at hz2
        exact hz2.1
      have hzm : (z () : v.adicCompletionIntegers K) ∈
          maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) :=
        (param_pow_iff (z ()).2 h0 n).mpr (by rw [hx₁]; exact hP)
      have hzm' : (z' () : v.adicCompletionIntegers K) ∈
          maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) :=
        (param_pow_iff (z' ()).2 h0' n).mpr (by rw [hx₂]; exact hQ)
      have hsum : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = formalPoint hW (z + z') := by
        rw [formalPoint_add hW, hz, hz']
      have hsm := add_param_mem_pow hzm hzm'
      rcases eq_or_ne (((z + z') ()) : v.adicCompletionIntegers K) 0 with hs0 | hs0
      · rw [Set.mem_setOf_eq, hsum, formalPoint_of_param_eq_zero hW hs0]
        trivial
      · rw [Set.mem_setOf_eq, hsum, formalPoint_of_param_ne_zero hW hs0]
        exact (param_pow_iff ((z + z') ()).2 hs0 n).mp hsm

variable {hW : W₀.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W}
  {n : ℕ}

@[simp]
lemma zero_mem_filtration : (0 : W.Point) ∈ filtration hW n := trivial

@[simp]
lemma some_mem_filtration {x y : v.adicCompletion K} {h : W.Nonsingular x y} :
    (.some x y h : W.Point) ∈ filtration hW n ↔ exp (2 * (n + 1) : ℤ) ≤ Valued.v x := Iff.rfl

/-- The filtration correspondence: the parameter lies in `𝔪^(n+1)` exactly when the
associated point lies in the filtration step `E_{n+1}(K_v)`. -/
theorem mem_pow_iff_formalPoint_mem_filtration (z : W₀.formalGroupLaw.Points) (n : ℕ) :
    (z () : v.adicCompletionIntegers K) ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
      formalPoint hW z ∈ filtration hW n := by
  rcases eq_or_ne (z () : v.adicCompletionIntegers K) 0 with h0 | h0
  · simp [h0]
  · rw [formalPoint_of_param_ne_zero hW h0, some_mem_filtration]
    exact param_pow_iff (z ()).2 h0 n

/-- Every point of the kernel of reduction comes from a parameter in `𝔪`: the
parametrization by the `𝔪`-points of the formal group is surjective onto
`filtration hW 0`. -/
theorem formalPoint_surjective {P : W.Point} (hP : P ∈ filtration hW 0) :
    ∃ z : W₀.formalGroupLaw.Points, formalPoint hW z = P := by
  match P with
  | .zero => exact ⟨0, formalPoint_of_param_eq_zero hW (z := 0) (by simp)⟩
  | .some x y h =>
    rw [some_mem_filtration] at hP
    exact exists_formalPoint_eq_some hW h (le_trans (exp_le_exp.mpr (by lia)) hP)

/-- The `𝔪`-points of the formal group law of an integral model `W₀` of `W` are the kernel
of reduction `E₁(K_v) = filtration hW 0`, via `z ↦ (x, y)` with `x = z/w(z)`,
`y = -1/w(z)`; the equivalence matches the filtration by valuation on both sides
(Silverman, VII.2.2). -/
theorem exists_points_equiv_filtration :
    ∃ θ : W₀.formalGroupLaw.Points ≃+ filtration hW 0,
      ∀ (z : W₀.formalGroupLaw.Points) (n : ℕ),
        ((z () : v.adicCompletionIntegers K) ∈
            maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) ↔
          ((θ z : filtration hW 0) : W.Point) ∈ filtration hW n) := by
  have hmap : ∀ z : W₀.formalGroupLaw.Points, formalPoint hW z ∈ filtration hW 0 :=
    fun z ↦ (mem_pow_iff_formalPoint_mem_filtration z 0).mp (by
      rw [pow_one]
      exact (z ()).2)
  let f : W₀.formalGroupLaw.Points →+ filtration hW 0 :=
    { toFun := fun z ↦ ⟨formalPoint hW z, hmap z⟩
      map_zero' := Subtype.ext (formalPoint_of_param_eq_zero hW (z := 0) (by simp))
      map_add' := fun z z' ↦ Subtype.ext (formalPoint_add hW z z') }
  refine ⟨AddEquiv.ofBijective f
    ⟨fun z z' h ↦ formalPoint_injective hW (congrArg Subtype.val h), fun P ↦ ?_⟩,
    fun z n ↦ ?_⟩
  · obtain ⟨z, hz⟩ := formalPoint_surjective P.2
    exact ⟨z, Subtype.ext hz⟩
  · exact mem_pow_iff_formalPoint_mem_filtration z n

/-- The filtration is decreasing. -/
theorem filtration_anti {m n : ℕ} (hmn : m ≤ n) : filtration hW n ≤ filtration hW m := by
  intro P hP
  match P with
  | .zero => trivial
  | .some x y h =>
    rw [some_mem_filtration] at hP ⊢
    refine le_trans (exp_le_exp.mpr ?_) hP
    lia

/-- If the chord slope towards the negative of the base point has valuation at least
`exp 1`, the difference of the two (integral) points lies in the kernel of reduction. -/
private lemma sub_mem_filtration_of_slope {x₀ y₀ x y : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (h : W.Nonsingular x y) (hxx : x ≠ x₀)
    (hx₀ : Valued.v x₀ ≤ 1) (hxI : Valued.v x ≤ 1)
    (hs : exp (1 : ℤ) ≤ Valued.v ((y - W.negY x₀ y₀) / (x - x₀))) :
    (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have ha₁ : Valued.v W.a₁ ≤ 1 := valued_a₁ hW
  have ha₂ : Valued.v W.a₂ ≤ 1 := valued_a₂ hW
  rw [sub_eq_add_neg, Point.neg_some,
    Point.add_some (fun hc ↦ hxx hc.1), some_mem_filtration]
  rw [Affine.slope_of_X_ne hxx, Affine.addX]
  set L : v.adicCompletion K := (y - W.negY x₀ y₀) / (x - x₀) with hL
  have hL1 : (1 : ℤᵐ⁰) < Valued.v L :=
    lt_of_lt_of_le (by rw [← exp_zero, exp_lt_exp]; lia) hs
  have hbig : ∀ c : ℤᵐ⁰, c ≤ 1 → c < Valued.v L ^ 2 := fun c hc ↦
    lt_of_le_of_lt hc (by
      calc (1 : ℤᵐ⁰) < Valued.v L := hL1
        _ = Valued.v L ^ 1 := (pow_one _).symm
        _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL1 (by lia))
  have hrest : Valued.v (W.a₁ * L - W.a₂ - x - x₀) < Valued.v L ^ 2 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt
      (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt (Valuation.map_sub _ _ _)
        (max_lt ?_ (hbig _ ha₂))) (hbig _ hxI))) (hbig _ hx₀))
    rw [map_mul]
    calc Valued.v W.a₁ * Valued.v L ≤ 1 * Valued.v L := mul_le_mul' ha₁ le_rfl
      _ = Valued.v L ^ 1 := by rw [one_mul, pow_one]
      _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL1 (by lia)
  rw [show L ^ 2 + W.a₁ * L - W.a₂ - x - x₀ = L ^ 2 + (W.a₁ * L - W.a₂ - x - x₀) by ring,
    Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hrest), map_pow]
  refine le_trans (le_of_eq ?_) (pow_le_pow_left' hs 2)
  rw [← exp_nsmul, nsmul_eq_mul]
  norm_num

/-- The congruence level around a `2`-torsion base point: the chord slope is estimated
through the finite-difference identity, whose second factor is congruent to the partial
derivative in `x` (nonvanishing by nonsingularity). -/
private lemma exists_level_sub_mem_of_two_torsion {x₀ y₀ : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (hx₀ : Valued.v x₀ ≤ 1) (hψ0 : y₀ - W.negY x₀ y₀ = 0) :
    ∃ s : ℕ, ∀ {x y : v.adicCompletion K} (h : W.Nonsingular x y),
      Valued.v (x - x₀) ≤ exp (-(s : ℤ)) → Valued.v (y - y₀) ≤ exp (-(s : ℤ)) →
      (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have hφ0 : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) ≠ 0 := by
    refine ((W.nonsingular_iff' x₀ y₀).mp h₀).2.resolve_right fun hc ↦ hc ?_
    rw [Affine.negY] at hψ0
    linear_combination hψ0
  obtain ⟨c, hc⟩ : ∃ c : ℤ,
      Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = exp c :=
    ⟨_, (exp_log (by simpa using hφ0)).symm⟩
  set s : ℕ := (1 - c).toNat
  refine ⟨s, fun {x y} h hx hy ↦ ?_⟩
  have hsc : 1 - c ≤ (s : ℤ) := Int.self_le_toNat _
  rcases eq_or_ne x x₀ with heq | hxx
  · -- same `x`-coordinate: the points coincide (`ψ = 0` collapses the dichotomy)
    have hy0 : y = y₀ := by
      rcases W.Y_eq_of_X_eq h.left h₀.left heq with hy' | hy'
      · exact hy'
      · rw [hy', ← sub_eq_zero, show W.negY x₀ y₀ - y₀ = -(y₀ - W.negY x₀ y₀) by ring,
          hψ0, neg_zero]
    have hPQ : (.some x y h : W.Point) = .some x₀ y₀ h₀ := by subst heq hy0; rfl
    rw [hPQ, sub_self]
    exact zero_mem _
  · -- distinct `x`-coordinates: the finite-difference identity gives the numerator bound
    have hid : (y - W.negY x₀ y₀) * (y - y₀) = (x - x₀) *
        (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) := by
      rw [Affine.negY]
      linear_combination (W.equation_iff x y).mp h.left - (W.equation_iff x₀ y₀).mp h₀.left
    have hval := congrArg Valued.v hid
    rw [map_mul, map_mul, valued_num_of_two_torsion hW hx₀ hc hsc hx hy] at hval
    exact sub_mem_filtration_of_slope h₀ h hxx hx₀ (valued_le_one_of_sub hx hx₀)
      (exp_one_le_valued_slope hxx hsc hy hval)

/-- The congruence level around a non-`2`-torsion base point: the slope numerator is
dominated by `ψ = y₀ - negY x₀ y₀`. -/
private lemma exists_level_sub_mem_of_ne_negY {x₀ y₀ : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (hx₀ : Valued.v x₀ ≤ 1) (hψ0 : y₀ - W.negY x₀ y₀ ≠ 0) :
    ∃ s : ℕ, ∀ {x y : v.adicCompletion K} (h : W.Nonsingular x y),
      Valued.v (x - x₀) ≤ exp (-(s : ℤ)) → Valued.v (y - y₀) ≤ exp (-(s : ℤ)) →
      (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v (y₀ - W.negY x₀ y₀) = exp c :=
    ⟨_, (exp_log (by simpa using hψ0)).symm⟩
  set s : ℕ := (1 - c).toNat
  refine ⟨s, fun {x y} h hx hy ↦ ?_⟩
  have hsc : 1 - c ≤ (s : ℤ) := Int.self_le_toNat _
  rcases eq_or_ne x x₀ with heq | hxx
  · rcases W.Y_eq_of_X_eq h.left h₀.left heq with hy' | hy'
    · have hPQ : (.some x y h : W.Point) = .some x₀ y₀ h₀ := by subst heq hy'; rfl
      rw [hPQ, sub_self]
      exact zero_mem _
    · -- `y = negY`: excluded, since `y − y₀ = −ψ` is too large
      exfalso
      rw [hy', show W.negY x₀ y₀ - y₀ = -(y₀ - W.negY x₀ y₀) by ring, Valuation.map_neg,
        hc, exp_le_exp] at hy
      lia
  · -- distinct `x`-coordinates: the numerator has valuation `v(ψ)`
    have hnum : Valued.v (y - W.negY x₀ y₀) = exp c := by
      rw [show y - W.negY x₀ y₀ = (y₀ - W.negY x₀ y₀) + (y - y₀) by ring,
        Valuation.map_add_eq_of_lt_left, hc]
      refine lt_of_le_of_lt hy ?_
      rw [hc, exp_lt_exp]
      lia
    refine sub_mem_filtration_of_slope h₀ h hxx hx₀ (valued_le_one_of_sub hx hx₀) ?_
    obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, Valued.v (x - x₀) = exp dx :=
      ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hxx)).symm⟩
    rw [map_div₀, hnum, hdx, ← exp_sub, exp_le_exp]
    have hdx' : dx ≤ -(s : ℤ) := by rwa [hdx, exp_le_exp] at hx
    lia

/-- Around each integral point of the curve there is a congruence level `s` such that
every on-curve point congruent to it modulo `𝔪^s` differs from it by an element of the
kernel of reduction. -/
private lemma exists_level_sub_mem {x₀ y₀ : v.adicCompletion K} (h₀ : W.Nonsingular x₀ y₀)
    (hx₀ : Valued.v x₀ ≤ 1) :
    ∃ s : ℕ, ∀ {x y : v.adicCompletion K} (h : W.Nonsingular x y),
      Valued.v (x - x₀) ≤ exp (-(s : ℤ)) → Valued.v (y - y₀) ≤ exp (-(s : ℤ)) →
      (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  rcases eq_or_ne (y₀ - W.negY x₀ y₀) 0 with hψ0 | hψ0
  · exact exists_level_sub_mem_of_two_torsion h₀ hx₀ hψ0
  · exact exists_level_sub_mem_of_ne_negY h₀ hx₀ hψ0

private lemma sfun_add {n : ℕ} {π : v.adicCompletionIntegers K} (hπ0 : π ≠ 0)
    (θ : W₀.formalGroupLaw.Points ≃+ filtration hW 0) {sfun : filtration hW n →
      v.adicCompletionIntegers K}
    (hsmem : ∀ P, sfun P ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hseq : ∀ P, (θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le) P) () :
      v.adicCompletionIntegers K) = π ^ n * sfun P) (P Q : filtration hW n) :
    sfun (P + Q) = MvPSeries.eval (Sum.elim (fun _ : Unit ↦ sfun P) fun _ : Unit ↦ sfun Q)
      (W₀.formalGroupLaw.scaledFC (π ^ n) ()) := by
  refine mul_left_cancel₀ (pow_ne_zero n hπ0) ?_
  calc π ^ n * sfun (P + Q)
      = (θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le) (P + Q)) () :
          v.adicCompletionIntegers K) := (hseq _).symm
    _ = W₀.addEval (π ^ n * sfun P) (π ^ n * sfun Q) := by
        rw [map_add, map_add, W₀.add_apply_coe_eq_addEval, hseq, hseq]
    _ = π ^ n * MvPSeries.eval (Sum.elim (fun _ : Unit ↦ sfun P) fun _ : Unit ↦ sfun Q)
          (W₀.formalGroupLaw.scaledFC (π ^ n) ()) :=
        ChabautyColeman.eval_F_eq_mul_eval_scaledFC W₀.formalGroupLaw (π ^ n)
          (hsmem P) (hsmem Q)

private lemma sfun_eval_injective {n : ℕ} {π : v.adicCompletionIntegers K}
    (θ : W₀.formalGroupLaw.Points ≃+ filtration hW 0)
    {lhat ehat : MvPowerSeries Unit (v.adicCompletionIntegers K)}
    (hl0 : MvPowerSeries.constantCoeff lhat = 0)
    (hel : MvPowerSeries.subst (fun _ : Unit ↦ lhat) ehat = MvPowerSeries.X ())
    {sfun : filtration hW n → v.adicCompletionIntegers K}
    (hsmem : ∀ P, sfun P ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hseq : ∀ P, (θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le) P) () :
      v.adicCompletionIntegers K) = π ^ n * sfun P) {P Q : filtration hW n}
    (h : MvPSeries.eval (fun _ : Unit ↦ sfun P) lhat
      = MvPSeries.eval (fun _ : Unit ↦ sfun Q) lhat) : P = Q := by
  have h1 := congrArg (fun x ↦ MvPSeries.eval (fun _ : Unit ↦ x) ehat) h
  rw [ChabautyColeman.eval_eval_of_subst_eq_X (hsmem P) hl0 hel,
    ChabautyColeman.eval_eval_of_subst_eq_X (hsmem Q) hl0 hel] at h1
  have h2 : θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le) P)
      = θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le) Q) := by
    funext i
    cases i
    exact Subtype.ext (by rw [hseq P, hseq Q, h1])
  exact AddSubgroup.inclusion_injective _ (θ.symm.injective h2)

private lemma exists_sfun_eval_eq {n : ℕ} {π : v.adicCompletionIntegers K} (hπ0 : π ≠ 0)
    (hmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π})
    (θ : W₀.formalGroupLaw.Points ≃+ filtration hW 0)
    (hθ : ∀ (z : W₀.formalGroupLaw.Points) (m : ℕ),
      ((z () : v.adicCompletionIntegers K) ∈
          maximalIdeal (v.adicCompletionIntegers K) ^ (m + 1) ↔
        ((θ z : filtration hW 0) : W.Point) ∈ filtration hW m))
    {lhat ehat : MvPowerSeries Unit (v.adicCompletionIntegers K)}
    (he0 : MvPowerSeries.constantCoeff ehat = 0)
    (hle : MvPowerSeries.subst (fun _ : Unit ↦ ehat) lhat = MvPowerSeries.X ())
    {sfun : filtration hW n → v.adicCompletionIntegers K}
    (hseq : ∀ P, (θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le) P) () :
      v.adicCompletionIntegers K) = π ^ n * sfun P)
    {w : v.adicCompletionIntegers K} (hw : w ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ∃ P : filtration hW n, MvPSeries.eval (fun _ : Unit ↦ sfun P) lhat = w := by
  have hsw : MvPSeries.eval (fun _ : Unit ↦ w) ehat ∈
      maximalIdeal (v.adicCompletionIntegers K) := ChabautyColeman.eval_unit_mem hw he0
  obtain ⟨z, hzdef⟩ : ∃ z : W₀.formalGroupLaw.Points, z = fun _ ↦
    ⟨π ^ n * MvPSeries.eval (fun _ : Unit ↦ w) ehat, Ideal.mul_mem_left _ _ hsw⟩ := ⟨_, rfl⟩
  have hzpow : (z () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1) := by
    have hz : (z () : v.adicCompletionIntegers K)
        = π ^ n * MvPSeries.eval (fun _ : Unit ↦ w) ehat := by rw [hzdef]
    rw [hz, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp (hmax ▸ hsw)
    exact ⟨u, by rw [hu, pow_succ]; ring⟩
  refine ⟨⟨((θ z : filtration hW 0) : W.Point), (hθ z n).mp hzpow⟩, ?_⟩
  have hP : θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le)
      ⟨((θ z : filtration hW 0) : W.Point), (hθ z n).mp hzpow⟩) = z := by
    rw [show AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le)
      ⟨((θ z : filtration hW 0) : W.Point), (hθ z n).mp hzpow⟩ = θ z from
        Subtype.ext rfl, θ.symm_apply_apply]
  have hsfun : sfun ⟨((θ z : filtration hW 0) : W.Point), (hθ z n).mp hzpow⟩
      = MvPSeries.eval (fun _ : Unit ↦ w) ehat := by
    refine mul_left_cancel₀ (pow_ne_zero n hπ0) ?_
    rw [← hseq, hP, hzdef]
  rw [hsfun]
  exact ChabautyColeman.eval_eval_of_subst_eq_X hw he0 hle

/-- **The kernel of reduction is torsion-free** under the standard ramification condition
(Silverman VII.3.1(b)/VII.3.4): if the residue characteristic `p` satisfies
`(p : 𝒪_v) ∉ 𝔪^(p-1)` — that is, `e < p − 1` for the absolute ramification index `e` —
then `E₁(K_v)` contains no nonzero point of finite order.  Consequently the torsion of
`E(K_v)` (and of any subgroup, such as the image of `E(K)`) injects into the reduction
`E(K_v)/E₁(K_v)`. -/
theorem eq_zero_of_isOfFinAddOrder_of_mem_filtration {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {P : W.Point} (hP : P ∈ filtration hW 0) (hord : IsOfFinAddOrder P) : P = 0 := by
  by_contra hP0
  obtain ⟨q, hq, hqdvd⟩ := (addOrderOf P).exists_prime_and_dvd
    fun h1 ↦ hP0 (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  have hQmem : (addOrderOf P / q) • P ∈ filtration hW 0 :=
    AddSubgroup.nsmul_mem _ hP _
  have hQq : q • ((addOrderOf P / q) • P) = 0 := by
    rw [← mul_nsmul, Nat.div_mul_cancel hqdvd]
    exact addOrderOf_nsmul_eq_zero P
  have hQ0 : (addOrderOf P / q) • P ≠ 0 := by
    intro h
    have hdvd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
    have hnpos : 0 < addOrderOf P := hord.addOrderOf_pos
    have hmul : addOrderOf P = q * (addOrderOf P / q) := (Nat.mul_div_cancel' hqdvd).symm
    have hm0 : addOrderOf P / q ≠ 0 := fun h0 ↦ by rw [h0, mul_zero] at hmul; omega
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
    have h2m := Nat.mul_le_mul_right (addOrderOf P / q) hq.two_le
    omega
  obtain ⟨θ, hθ⟩ := exists_points_equiv_filtration (hW := hW)
  have hz : q • θ.symm ⟨(addOrderOf P / q) • P, hQmem⟩ = 0 := by
    rw [← map_nsmul, show q • (⟨(addOrderOf P / q) • P, hQmem⟩ : filtration hW 0) = 0 from
      Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hQq), map_zero]
  have hzz : θ.symm ⟨(addOrderOf P / q) • P, hQmem⟩ = 0 := by
    rcases eq_or_ne q p with rfl | hqp
    · exact points_eq_zero_of_nsmul_residueChar hp hpmem hpram hz
    · exact points_eq_zero_of_nsmul_prime_ne hp hq hpmem hqp hz
  refine hQ0 ?_
  have h1 := congrArg θ hzz
  rw [θ.apply_symm_apply, map_zero] at h1
  simpa using congrArg Subtype.val h1

/-- Torsion points of `E(K_v)` with the same image modulo the kernel of reduction agree:
the reduction map is injective on torsion under the ramification condition. -/
theorem isOfFinAddOrder.eq_of_sub_mem_filtration {p : ℕ} (hp : p.Prime)
    (hpmem : (p : v.adicCompletionIntegers K) ∈ maximalIdeal (v.adicCompletionIntegers K))
    (hpram : (p : v.adicCompletionIntegers K) ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ (p - 1))
    {P Q : W.Point} (hP : IsOfFinAddOrder P) (hQ : IsOfFinAddOrder Q)
    (h : P - Q ∈ filtration hW 0) : P = Q :=
  sub_eq_zero.mp (eq_zero_of_isOfFinAddOrder_of_mem_filtration hp hpmem hpram h
    (sub_eq_add_neg P Q ▸ hP.add hQ.neg))

variable [Finite (R ⧸ v.asIdeal)]

/-- Each filtration step has finite index in the previous one: the parameter map modulo
`𝔪^(k+2)` is additive on the `k`-th step (the formal group law is `t₁ + t₂` to first
order) with kernel the next step, and it takes values in a finite quotient. -/
private lemma relIndex_filtration_succ_ne_zero (k : ℕ) :
    (filtration hW (k + 1)).relIndex (filtration hW k) ≠ 0 := by
  obtain ⟨θ, hθ⟩ := exists_points_equiv_filtration (hW := hW)
  -- the parameter of a point of the `k`-th filtration step
  obtain ⟨par, hpar⟩ : ∃ par : filtration hW k → W₀.formalGroupLaw.Points,
      par = fun P ↦ θ.symm ⟨P.1, filtration_anti (Nat.zero_le k) P.2⟩ := ⟨_, rfl⟩
  have hθpar (P : filtration hW k) : ((θ (par P) : filtration hW 0) : W.Point) = P.1 := by
    rw [hpar, θ.apply_symm_apply]
  have hparam (P : filtration hW k) : ((par P) () : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ (k + 1) :=
    (hθ _ k).mpr (by rw [hθpar]; exact P.2)
  have hpar_add (P Q : filtration hW k) : par (P + Q) = par P + par Q := by
    simp only [hpar]
    rw [← map_add]
    exact congrArg θ.symm (Subtype.ext rfl)
  -- the parameter map modulo `𝔪^(k+2)` is additive
  have hadd (P Q : filtration hW k) :
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
          ((par (P + Q)) ()) =
        Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
          ((par P) ()) +
        Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))
          ((par Q) ()) := by
    rw [hpar_add]
    exact mk_add_param (hparam P) (hparam Q)
  obtain ⟨f, hf⟩ : ∃ f : filtration hW k →+ v.adicCompletionIntegers K ⧸
      (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2)),
      f = AddMonoidHom.mk'
        (fun P ↦ Ideal.Quotient.mk _ (((par P) ()) : v.adicCompletionIntegers K)) hadd :=
    ⟨_, rfl⟩
  have hker : f.ker = (filtration hW (k + 1)).addSubgroupOf (filtration hW k) := by
    ext P
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hf, AddMonoidHom.mk'_apply,
      Ideal.Quotient.eq_zero_iff_mem, hθ _ (k + 1), hθpar]
  have hfin : Finite (v.adicCompletionIntegers K ⧸
      (maximalIdeal (v.adicCompletionIntegers K) ^ (k + 2))) := finite_quotient_pow (k + 2)
  have hrel : (filtration hW (k + 1)).relIndex (filtration hW k) = f.ker.index :=
    congrArg AddSubgroup.index hker.symm
  rw [hrel, AddSubgroup.index_ker, Nat.card_ne_zero]
  exact ⟨⟨0, 0, map_zero f⟩, Set.Finite.to_subtype (Set.toFinite _)⟩

/-- Finitely many integral points cover the integral locus of the curve up to elements of
the kernel of reduction (by compactness and the local congruence levels). -/
private lemma exists_finite_integral_cover :
    ∃ P : Set W.Point, P.Finite ∧ ∀ {x y : v.adicCompletion K}
      (h : W.Nonsingular x y), Valued.v x ≤ 1 → Valued.v y ≤ 1 →
      ∃ p ∈ P, (.some x y h : W.Point) - p ∈ filtration hW 0 := by
  obtain ⟨Z, hZdef⟩ : ∃ Z : Set ((v.adicCompletion K) × (v.adicCompletion K)),
      Z = {p | W.Equation p.1 p.2 ∧ Valued.v p.1 ≤ 1 ∧ Valued.v p.2 ≤ 1} := ⟨_, rfl⟩
  have hZcpt : IsCompact Z := by
    rw [hZdef]
    exact isCompact_integralPoints
  have hns : ∀ p : ↥Z, W.Nonsingular p.1.1 p.1.2 := fun ⟨q, hq⟩ ↦
    (W.equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp (by
      rw [hZdef] at hq
      exact hq.1)
  have hint : ∀ p : ↥Z, Valued.v p.1.1 ≤ 1 := fun ⟨q, hq⟩ ↦ by
    rw [hZdef] at hq
    exact hq.2.1
  choose sfun hsfun using fun p : ↥Z ↦ exists_level_sub_mem (hns p) (hint p)
  obtain ⟨t, ht⟩ := hZcpt.elim_finite_subcover
    (fun p : ↥Z ↦ {b : v.adicCompletion K | Valued.v (b - p.1.1) ≤ exp (-(sfun p : ℤ))} ×ˢ
      {b : v.adicCompletion K | Valued.v (b - p.1.2) ≤ exp (-(sfun p : ℤ))})
    (fun p ↦ (isOpen_le_ball _ _).prod (isOpen_le_ball _ _))
    (fun q hq ↦ Set.mem_iUnion.mpr ⟨⟨q, hq⟩, by
      refine Set.mem_prod.mpr ⟨?_, ?_⟩ <;>
        · rw [Set.mem_setOf, sub_self, map_zero]
          exact zero_le⟩)
  refine ⟨(fun p : ↥Z ↦ (.some p.1.1 p.1.2 (hns p) : W.Point)) '' t,
    t.finite_toSet.image _, fun {x y} h hxI hyI ↦ ?_⟩
  have hqZ : (x, y) ∈ Z := by
    rw [hZdef]
    exact ⟨h.left, hxI, hyI⟩
  obtain ⟨p, hpt, hpU⟩ := Set.mem_iUnion₂.mp (ht hqZ)
  exact ⟨_, Set.mem_image_of_mem _ hpt,
    hsfun p h (Set.mem_prod.mp hpU).1 (Set.mem_prod.mp hpU).2⟩

/-- The kernel of reduction has finite index in `E(K_v)`: the complement consists of
integral points, which a compactness argument covers by finitely many congruence
neighbourhoods. -/
theorem filtration_zero_finiteIndex (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) : (filtration hW 0).FiniteIndex := by
  rw [AddSubgroup.finiteIndex_iff_finite_quotient]
  obtain ⟨P, hPfin, hP⟩ := exists_finite_integral_cover (hW := hW)
  have := hPfin.to_subtype
  refine Finite.of_surjective (α := Option ↥P)
    (fun o ↦ o.elim (0 : W.Point ⧸ filtration hW 0) fun p ↦ QuotientAddGroup.mk p.1)
    fun c ↦ ?_
  obtain ⟨Q, rfl⟩ := QuotientAddGroup.mk_surjective c
  match Q with
  | .zero => exact ⟨none, rfl⟩
  | .some x y h =>
    by_cases hmem : (.some x y h : W.Point) ∈ filtration hW 0
    · exact ⟨none, ((QuotientAddGroup.eq_zero_iff _).mpr hmem).symm⟩
    · have hxpole : ¬ exp (2 : ℤ) ≤ Valued.v x := fun hc ↦ hmem
        ((some_mem_filtration (hW := hW)).mpr (le_trans (exp_le_exp.mpr (by lia)) hc))
      obtain ⟨hxI, hyI⟩ := integral_of_not_mem hW h.left hxpole
      obtain ⟨p, hpP, hd⟩ := hP h hxI hyI
      exact ⟨some ⟨p, hpP⟩, ((QuotientAddGroup.eq_iff_sub_mem).mpr hd).symm⟩

/-- Each step of the valuation filtration on the points of an elliptic curve over `K_v` has
finite index, by induction: each step has finite index in the previous one
(`relIndex_filtration_succ_ne_zero`), and the `0`-th step has finite index in `E(K_v)`. -/
theorem filtration_finiteIndex (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) (n : ℕ) : (filtration hW n).FiniteIndex := by
  induction n with
  | zero => exact filtration_zero_finiteIndex hW
  | succ k ih =>
    have h1 : (filtration hW (k + 1)).index ≠ 0 := by
      rw [← AddSubgroup.relIndex_mul_index (filtration_anti (hW := hW) (Nat.le_succ k))]
      exact Nat.mul_ne_zero (relIndex_filtration_succ_ne_zero k) ih.index_ne_zero
    exact ⟨h1⟩

/-- Some step of the valuation filtration on the points of an elliptic curve over `K_v` is
isomorphic to the additive group of `𝒪_v`: for `𝔪^k` past the ramification of the residue
characteristic, the scaled formal logarithm identifies `Ê(𝔪^k)` with `(𝔪^k, +) ≅ (𝒪_v, +)`
(Silverman, IV.6.4). -/
theorem exists_filtration_equiv (hW : W₀.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K)) = W) :
    ∃ n, Nonempty (filtration hW n ≃+ v.adicCompletionIntegers K) := by
  obtain ⟨n, π, lhat, ehat, -, hπ0, hmax, hl0, he0, hle, hel, hadd⟩ :=
    exists_scaledLog (v := v) (K := K) W₀.formalGroupLaw
  obtain ⟨θ, hθ⟩ := exists_points_equiv_filtration (hW := hW)
  -- the scaled parameter `s_P` of a point of the `n`-th filtration step
  have hs (P : filtration hW n) : ∃ s ∈ maximalIdeal (v.adicCompletionIntegers K),
      (θ.symm (AddSubgroup.inclusion (filtration_anti (hW := hW) n.zero_le) P) () :
        v.adicCompletionIntegers K) = π ^ n * s := by
    refine exists_pi_pow_factor hmax ((hθ _ n).mpr ?_)
    rw [θ.apply_symm_apply, AddSubgroup.coe_inclusion]
    exact P.2
  choose sfun hsmem hseq using hs
  have hℓmem (P : filtration hW n) : MvPSeries.eval (fun _ : Unit ↦ sfun P) lhat ∈
      maximalIdeal (v.adicCompletionIntegers K) :=
    ChabautyColeman.eval_unit_mem (hsmem P) hl0
  have hbij : Function.Bijective (fun P : filtration hW n ↦
      (⟨MvPSeries.eval (fun _ : Unit ↦ sfun P) lhat, hℓmem P⟩ :
        maximalIdeal (v.adicCompletionIntegers K))) := by
    refine ⟨fun P Q h ↦ sfun_eval_injective θ hl0 hel hsmem hseq ?_, fun ⟨w, hw⟩ ↦ ?_⟩
    · rwa [Subtype.mk.injEq] at h
    · obtain ⟨P, hP⟩ := exists_sfun_eval_eq hπ0 hmax θ hθ he0 hle hseq hw
      exact ⟨P, Subtype.ext hP⟩
  obtain ⟨E2⟩ := maximalIdeal_addEquiv hπ0 hmax
  refine ⟨n, ⟨(AddEquiv.ofBijective (AddMonoidHom.mk' _ fun P Q ↦ Subtype.ext ?_)
    hbij).trans E2⟩⟩
  change MvPSeries.eval (fun _ : Unit ↦ sfun (P + Q)) lhat
    = MvPSeries.eval (fun _ : Unit ↦ sfun P) lhat + MvPSeries.eval (fun _ : Unit ↦ sfun Q) lhat
  rw [sfun_add hπ0 θ hsmem hseq P Q]
  exact ChabautyColeman.eval_scaledFC_add W₀.formalGroupLaw hadd (hsmem P) (hsmem Q)

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R) [DecidableEq (v.adicCompletion K)] [CharZero K]
  [Finite (R ⧸ v.asIdeal)] (W : Affine (v.adicCompletion K)) [W.IsElliptic]

open scoped Classical in
/-- The group of points of an elliptic curve over the completion `K_v` (a characteristic-`0`
local field with finite residue field) has a subgroup of finite index that is isomorphic to
the additive group of the valuation ring `𝒪_v`.

This is the structure theorem coming from the formal group of the curve: pass to an
integral model and take a suitable step of the valuation filtration. -/
theorem exists_finiteIndex_addSubgroup_equiv_adicCompletionIntegers :
    ∃ U : AddSubgroup W.Point, U.FiniteIndex ∧ Nonempty (U ≃+ (v.adicCompletionIntegers K)) := by
  obtain ⟨C, W₀, hW⟩ := exists_variableChange_map_eq v W
  obtain ⟨n, ⟨e⟩⟩ := exists_filtration_equiv hW
  refine ⟨(filtration hW n).map (Point.equivVariableChange W C : _ →+ _), ⟨?_⟩, ?_⟩
  · rw [AddSubgroup.index_map_equiv]
    exact (filtration_finiteIndex hW n).index_ne_zero
  · exact ⟨((AddEquiv.addSubgroupMap (Point.equivVariableChange W C) _).symm.trans e)⟩

end WeierstrassCurve.Affine

end
