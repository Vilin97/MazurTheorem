/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Vasily Ilin
-/

import MazurTorsion.EllipticCurve.NonsingularReduction

/-!
# Additivity of reduction to the nonsingular locus

This file proves that the canonical nonsingular-reduction domain of an integral local
Weierstrass equation is an additive subgroup and that coordinatewise reduction is a
homomorphism on it.  The proof adapts the exact-pinned good-reduction argument from
`EllipticCurves.WeierstrassFormalGroup.Reduction`: wherever that argument used smoothness of the
whole special cubic, we instead use the nonsingularity carried by
`HasNonsingularReduction`.

The two substantive local steps are:

* equal nonsingular coordinate reductions differ by the formal kernel; and
* translation by a formal-kernel point preserves nonsingular coordinate reduction.

Together with the already checked slope calculation away from the reduced anti-diagonal, these
give unconditional additivity on the canonical domain.  No Neron model or good-reduction
hypothesis is used.
-/

noncomputable section

open IsLocalRing

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)

local notation:max "res" x:max =>
  IsLocalRing.residue (v.adicCompletionIntegers K) x

local instance : DecidableEq (ResidueField (v.adicCompletionIntegers K)) :=
  Classical.decEq _

private theorem valued_sub_le
    {a b : v.adicCompletion K} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) :
    Valued.v (a - b) ≤ 1 :=
  (Valued.v.map_sub _ _).trans (max_le ha hb)

private theorem not_exp_two_le_of_le_one
    {a : v.adicCompletion K} (ha : Valued.v a ≤ 1) :
    ¬ exp (2 : ℤ) ≤ Valued.v a := fun hc ↦
  absurd (hc.trans ha) (by rw [not_le, ← exp_zero]; exact exp_lt_exp.mpr (by lia))

private theorem res_sub
    {a b : v.adicCompletion K} (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1)
    (hab : Valued.v (a - b) ≤ 1) :
    res (⟨a - b, hab⟩ : v.adicCompletionIntegers K) =
      res ⟨a, ha⟩ - res ⟨b, hb⟩ := by
  rw [show (⟨a - b, hab⟩ : v.adicCompletionIntegers K) =
      ⟨a, ha⟩ - ⟨b, hb⟩ from Subtype.ext (by push_cast; ring), map_sub]

private theorem mem_maximalIdeal_iff
    {x : v.adicCompletionIntegers K} :
    x ∈ maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v (x : v.adicCompletion K) ≤ exp (-1 : ℤ) := by
  have h := mem_maximalIdeal_pow_iff (K := K) (x := x) (n := 1)
  rwa [pow_one] at h

private theorem valued_le_one_of_sub
    {a b : v.adicCompletion K} {n : ℕ}
    (h : Valued.v (a - b) ≤ exp (-(n : ℤ))) (hb : Valued.v b ≤ 1) :
    Valued.v a ≤ 1 := by
  rw [show a = (a - b) + b by ring]
  refine le_trans (Valued.v.map_add _ _) (max_le (h.trans ?_) hb)
  rw [← exp_zero, exp_le_exp]
  lia

include hW in
private theorem coe_negY
    {x y : v.adicCompletion K} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    W.negY x y =
      ((W₀.toAffine).negY
        (⟨x, hx⟩ : v.adicCompletionIntegers K) ⟨y, hy⟩ : v.adicCompletion K) := by
  conv_lhs => rw [← hW]
  exact (W₀.toAffine).map_negY
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ⟨x, hx⟩ ⟨y, hy⟩

include hW in
private theorem valued_negY_le
    {x y : v.adicCompletion K} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    Valued.v (W.negY x y) ≤ 1 := by
  rw [coe_negY hW hx hy]
  exact ((W₀.toAffine).negY ⟨x, hx⟩ ⟨y, hy⟩).property

include hW in
private theorem redCoord_negY
    {x y : v.adicCompletion K} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hn : Valued.v (W.negY x y) ≤ 1) :
    res ⟨W.negY x y, hn⟩ =
      (adicRedCurve W₀).negY (res ⟨x, hx⟩) (res ⟨y, hy⟩) := by
  have hsub : (⟨W.negY x y, hn⟩ : v.adicCompletionIntegers K) =
      (W₀.toAffine).negY ⟨x, hx⟩ ⟨y, hy⟩ :=
    Subtype.ext (coe_negY hW hx hy)
  rw [hsub]
  exact ((W₀.toAffine).map_negY
    (IsLocalRing.residue (v.adicCompletionIntegers K)) ⟨x, hx⟩ ⟨y, hy⟩).symm

include hW in
private theorem coe_addX
    {x₁ x₂ ℓ : v.adicCompletion K}
    (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1) (hℓ : Valued.v ℓ ≤ 1) :
    W.addX x₁ x₂ ℓ =
      ((W₀.toAffine).addX
        (⟨x₁, h₁⟩ : v.adicCompletionIntegers K) ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩ :
          v.adicCompletion K) := by
  conv_lhs => rw [← hW]
  exact (W₀.toAffine).map_addX
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩

include hW in
private theorem coe_addY
    {x₁ x₂ y₁ ℓ : v.adicCompletion K}
    (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1)
    (hy₁ : Valued.v y₁ ≤ 1) (hℓ : Valued.v ℓ ≤ 1) :
    W.addY x₁ x₂ y₁ ℓ =
      ((W₀.toAffine).addY
        (⟨x₁, h₁⟩ : v.adicCompletionIntegers K) ⟨x₂, h₂⟩ ⟨y₁, hy₁⟩ ⟨ℓ, hℓ⟩ :
          v.adicCompletion K) := by
  conv_lhs => rw [← hW]
  exact (W₀.toAffine).map_addY
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      ⟨x₁, h₁⟩ ⟨y₁, hy₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩

include hW in
private theorem redCoord_addX
    {x₁ x₂ ℓ : v.adicCompletion K}
    (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1) (hℓ : Valued.v ℓ ≤ 1)
    (hs : Valued.v (W.addX x₁ x₂ ℓ) ≤ 1) :
    res ⟨W.addX x₁ x₂ ℓ, hs⟩ =
      (adicRedCurve W₀).addX (res ⟨x₁, h₁⟩) (res ⟨x₂, h₂⟩) (res ⟨ℓ, hℓ⟩) := by
  have hsub : (⟨W.addX x₁ x₂ ℓ, hs⟩ : v.adicCompletionIntegers K) =
      (W₀.toAffine).addX ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩ :=
    Subtype.ext (coe_addX hW h₁ h₂ hℓ)
  rw [hsub]
  exact ((W₀.toAffine).map_addX
    (IsLocalRing.residue (v.adicCompletionIntegers K)) ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩).symm

include hW in
private theorem redCoord_addY
    {x₁ x₂ y₁ ℓ : v.adicCompletion K}
    (h₁ : Valued.v x₁ ≤ 1) (h₂ : Valued.v x₂ ≤ 1)
    (hy₁ : Valued.v y₁ ≤ 1) (hℓ : Valued.v ℓ ≤ 1)
    (hs : Valued.v (W.addY x₁ x₂ y₁ ℓ) ≤ 1) :
    res ⟨W.addY x₁ x₂ y₁ ℓ, hs⟩ =
      (adicRedCurve W₀).addY
        (res ⟨x₁, h₁⟩) (res ⟨x₂, h₂⟩) (res ⟨y₁, hy₁⟩) (res ⟨ℓ, hℓ⟩) := by
  have hsub : (⟨W.addY x₁ x₂ y₁ ℓ, hs⟩ : v.adicCompletionIntegers K) =
      (W₀.toAffine).addY ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ ⟨y₁, hy₁⟩ ⟨ℓ, hℓ⟩ :=
    Subtype.ext (coe_addY hW h₁ h₂ hy₁ hℓ)
  rw [hsub]
  exact ((W₀.toAffine).map_addY
    (IsLocalRing.residue (v.adicCompletionIntegers K)) ⟨x₁, h₁⟩ ⟨y₁, hy₁⟩ ⟨x₂, h₂⟩ ⟨ℓ, hℓ⟩).symm

include hW in
private theorem res_a₁ :
    res ⟨W.a₁, valued_a₁ hW⟩ = (adicRedCurve W₀).a₁ := by
  have ha₁ : W.a₁ = (W₀.a₁ : v.adicCompletion K) :=
    (congrArg (fun E : Affine (v.adicCompletion K) ↦ E.a₁) hW).symm.trans
      (W₀.map_a₁ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)))
  rw [show (⟨W.a₁, valued_a₁ hW⟩ : v.adicCompletionIntegers K) = W₀.a₁ from
    Subtype.ext ha₁]
  exact (W₀.map_a₁ (IsLocalRing.residue (v.adicCompletionIntegers K))).symm

include hW in
private theorem res_a₂ :
    res ⟨W.a₂, valued_a₂ hW⟩ = (adicRedCurve W₀).a₂ := by
  have ha₂ : W.a₂ = (W₀.a₂ : v.adicCompletion K) :=
    (congrArg (fun E : Affine (v.adicCompletion K) ↦ E.a₂) hW).symm.trans
      (W₀.map_a₂ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)))
  rw [show (⟨W.a₂, valued_a₂ hW⟩ : v.adicCompletionIntegers K) = W₀.a₂ from
    Subtype.ext ha₂]
  exact (W₀.map_a₂ (IsLocalRing.residue (v.adicCompletionIntegers K))).symm

include hW in
private theorem res_a₄ :
    res ⟨W.a₄, valued_a₄ hW⟩ = (adicRedCurve W₀).a₄ := by
  have ha₄ : W.a₄ = (W₀.a₄ : v.adicCompletion K) :=
    (congrArg (fun E : Affine (v.adicCompletion K) ↦ E.a₄) hW).symm.trans
      (W₀.map_a₄ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)))
  rw [show (⟨W.a₄, valued_a₄ hW⟩ : v.adicCompletionIntegers K) = W₀.a₄ from
    Subtype.ext ha₄]
  exact (W₀.map_a₄ (IsLocalRing.residue (v.adicCompletionIntegers K))).symm

private theorem valued_eq_one_of_residue_ne
    {a : v.adicCompletion K} (ha : Valued.v a ≤ 1)
    (h : res(⟨a, ha⟩ : v.adicCompletionIntegers K) ≠ 0) :
    Valued.v a = 1 := by
  exact (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp
    ((residue_ne_zero_iff_isUnit
      (⟨a, ha⟩ : v.adicCompletionIntegers K)).mp h)

include hW in
private theorem unit_deriv_of_nonsingular_reduction
    {x₀ y₀ : v.adicCompletion K}
    (hx₀ : Valued.v x₀ ≤ 1) (hy₀ : Valued.v y₀ ≤ 1)
    (hred : (adicRedCurve W₀).Nonsingular (res⟨x₀, hx₀⟩) (res⟨y₀, hy₀⟩)) :
    Valued.v (y₀ - W.negY x₀ y₀) = 1 ∨
      Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = 1 := by
  have hnegYint : Valued.v (W.negY x₀ y₀) ≤ 1 := valued_negY_le hW hx₀ hy₀
  have hψint : Valued.v (y₀ - W.negY x₀ y₀) ≤ 1 :=
    valued_sub_le hy₀ hnegYint
  set φ₀ : v.adicCompletionIntegers K :=
    ⟨W.a₁, valued_a₁ hW⟩ * ⟨y₀, hy₀⟩ -
      (⟨x₀, hx₀⟩ ^ 2 + ⟨x₀, hx₀⟩ ^ 2 + ⟨x₀, hx₀⟩ ^ 2 +
        (⟨W.a₂, valued_a₂ hW⟩ * ⟨x₀, hx₀⟩ +
          ⟨W.a₂, valued_a₂ hW⟩ * ⟨x₀, hx₀⟩) + ⟨W.a₄, valued_a₄ hW⟩)
      with hφ₀
  have hφint :
      Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) ≤ 1 := by
    rw [show W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) =
      (φ₀ : v.adicCompletion K) from by rw [hφ₀]; push_cast; ring]
    exact φ₀.property
  have hresψ : res (⟨y₀ - W.negY x₀ y₀, hψint⟩ : v.adicCompletionIntegers K) =
      res ⟨y₀, hy₀⟩ - (adicRedCurve W₀).negY (res ⟨x₀, hx₀⟩) (res ⟨y₀, hy₀⟩) := by
    rw [res_sub hy₀ hnegYint hψint, redCoord_negY hW hx₀ hy₀ hnegYint]
  have hresφ :
      res (⟨W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄), hφint⟩ :
        v.adicCompletionIntegers K) =
      (adicRedCurve W₀).a₁ * res ⟨y₀, hy₀⟩ -
        (3 * res ⟨x₀, hx₀⟩ ^ 2 +
          2 * (adicRedCurve W₀).a₂ * res ⟨x₀, hx₀⟩ + (adicRedCurve W₀).a₄) := by
    rw [← res_a₁ hW, ← res_a₂ hW, ← res_a₄ hW,
      show (⟨W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄), hφint⟩ :
        v.adicCompletionIntegers K) = φ₀ from
        Subtype.ext (by rw [hφ₀]; push_cast; ring), hφ₀]
    simp only [map_sub, map_add, map_mul, map_pow]
    ring
  rcases nonsingular_deriv_disj hred with hφ | hψ
  · exact Or.inr (valued_eq_one_of_residue_ne hφint (fun h ↦ hφ (hresφ.symm.trans h)))
  · exact Or.inl (valued_eq_one_of_residue_ne hψint (fun h ↦ hψ (hresψ.symm.trans h)))

include hW in
private theorem valued_num_of_two_torsion
    {x₀ y₀ x y : v.adicCompletion K} {c : ℤ} {s : ℕ}
    (hx₀ : Valued.v x₀ ≤ 1)
    (hc : Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = exp c)
    (hsc : 1 - c ≤ (s : ℤ))
    (hx : Valued.v (x - x₀) ≤ exp (-(s : ℤ)))
    (hy : Valued.v (y - y₀) ≤ exp (-(s : ℤ))) :
    Valued.v (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) = exp c := by
  have hdiff :
      Valued.v ((x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
        -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))) ≤ exp (-(s : ℤ)) := by
    rw [show (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
        -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) =
      (x - x₀) * (x + 2 * x₀ + W.a₂) - W.a₁ * (y - y₀) by ring]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · rw [map_mul]
      refine le_trans (mul_le_mul' hx ?_) (by rw [mul_one])
      refine le_trans (Valued.v.map_add _ _) (max_le
        (le_trans (Valued.v.map_add _ _) (max_le (valued_le_one_of_sub hx hx₀) ?_))
        (valued_a₂ hW))
      calc
        Valued.v (2 * x₀) ≤ Valued.v 2 * Valued.v x₀ := le_of_eq (map_mul _ _ _)
        _ ≤ 1 * 1 := mul_le_mul' (show Valued.v (2 : v.adicCompletion K) ≤ 1 by
          change Valued.v ((2 : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1
          exact (2 : v.adicCompletionIntegers K).property) hx₀
        _ = 1 := one_mul 1
    · rw [map_mul]
      exact le_trans (mul_le_mul' (valued_a₁ hW) hy) (by rw [one_mul])
  rw [show x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y =
      -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) +
        ((x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) -
          -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))) by ring,
    Valuation.map_add_eq_of_lt_left, Valuation.map_neg, hc]
  refine lt_of_le_of_lt hdiff ?_
  rw [Valuation.map_neg, hc, exp_lt_exp]
  lia

private theorem exp_one_le_valued_slope
    {x₀ y₀ x y : v.adicCompletion K} {c : ℤ} {s : ℕ}
    (hxx : x ≠ x₀) (hsc : 1 - c ≤ (s : ℤ))
    (hy : Valued.v (y - y₀) ≤ exp (-(s : ℤ)))
    (hprod : Valued.v (y - W.negY x₀ y₀) * Valued.v (y - y₀) =
      Valued.v (x - x₀) * exp c) :
    exp (1 : ℤ) ≤ Valued.v ((y - W.negY x₀ y₀) / (x - x₀)) := by
  obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, Valued.v (x - x₀) = exp dx :=
    ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hxx)).symm⟩
  obtain ⟨dy, hdy⟩ : ∃ dy : ℤ, Valued.v (y - y₀) = exp dy := by
    refine ⟨_, (exp_log fun h₀ ↦ ?_).symm⟩
    rw [h₀, mul_zero, hdx] at hprod
    exact mul_ne_zero exp_ne_zero exp_ne_zero hprod.symm
  obtain ⟨nv, hnv⟩ : ∃ nv : ℤ, Valued.v (y - W.negY x₀ y₀) = exp nv := by
    refine ⟨_, (exp_log fun h₀ ↦ ?_).symm⟩
    rw [h₀, zero_mul, hdx] at hprod
    exact mul_ne_zero exp_ne_zero exp_ne_zero hprod.symm
  rw [hnv, hdy, hdx, ← exp_add, ← exp_add, exp_inj] at hprod
  have hdy' : dy ≤ -(s : ℤ) := by rwa [hdy, exp_le_exp] at hy
  rw [map_div₀, hnv, hdx, ← exp_sub, exp_le_exp]
  lia

include hW in
private theorem not_eq_and_eq_negY_of_reduced
    {x₁ x₂ y₁ y₂ : v.adicCompletion K}
    (hx₁ : Valued.v x₁ ≤ 1) (hx₂ : Valued.v x₂ ≤ 1)
    (hy₁ : Valued.v y₁ ≤ 1) (hy₂ : Valued.v y₂ ≤ 1)
    (hne : ¬ (res (⟨x₁, hx₁⟩ : v.adicCompletionIntegers K) = res ⟨x₂, hx₂⟩ ∧
      res ⟨y₁, hy₁⟩ = (adicRedCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩))) :
    ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
  rintro ⟨hX, hY⟩
  apply hne
  refine ⟨congrArg (IsLocalRing.residue (v.adicCompletionIntegers K))
    (Subtype.ext hX), ?_⟩
  calc
    res (⟨y₁, hy₁⟩ : v.adicCompletionIntegers K) =
        res ⟨W.negY x₂ y₂, valued_negY_le hW hx₂ hy₂⟩ :=
      congrArg (IsLocalRing.residue (v.adicCompletionIntegers K)) (Subtype.ext hY)
    _ = (adicRedCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩) :=
      redCoord_negY hW hx₂ hy₂ (valued_negY_le hW hx₂ hy₂)

variable [W.IsElliptic] [DecidableEq (v.adicCompletion K)]

section

variable [CharZero K]

include hW in
private theorem sub_mem_filtration_of_slope
    {x₀ y₀ x y : v.adicCompletion K}
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
  have hL₁ : (1 : ℤᵐ⁰) < Valued.v L :=
    lt_of_lt_of_le (by rw [← exp_zero, exp_lt_exp]; lia) hs
  have hbig : ∀ c : ℤᵐ⁰, c ≤ 1 → c < Valued.v L ^ 2 := fun c hc ↦
    lt_of_le_of_lt hc (by
      calc
        (1 : ℤᵐ⁰) < Valued.v L := hL₁
        _ = Valued.v L ^ 1 := (pow_one _).symm
        _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL₁ (by lia))
  have hrest : Valued.v (W.a₁ * L - W.a₂ - x - x₀) < Valued.v L ^ 2 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt
      (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt
        (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ (hbig _ ha₂)))
        (hbig _ hxI))) (hbig _ hx₀))
    rw [map_mul]
    calc
      Valued.v W.a₁ * Valued.v L ≤ 1 * Valued.v L := mul_le_mul' ha₁ le_rfl
      _ = Valued.v L ^ 1 := by rw [one_mul, pow_one]
      _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL₁ (by lia)
  rw [show L ^ 2 + W.a₁ * L - W.a₂ - x - x₀ =
      L ^ 2 + (W.a₁ * L - W.a₂ - x - x₀) by ring,
    Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hrest), map_pow]
  refine le_trans (le_of_eq ?_) (pow_le_pow_left' hs 2)
  rw [← exp_nsmul, nsmul_eq_mul]
  norm_num

include hW in
/-- An affine point with integral abscissa whose tangent slope has a pole of order at least one
doubles into the formal kernel.  This valuation-only statement is useful for the marked-point
branches of Tate's algorithm and does not assume that the source has nonsingular reduction. -/
theorem add_self_mem_filtration_of_slope
    {x₀ y₀ : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (hx₀ : Valued.v x₀ ≤ 1)
    (hψ : y₀ ≠ W.negY x₀ y₀)
    (hs : exp (1 : ℤ) ≤ Valued.v (W.slope x₀ x₀ y₀ y₀)) :
    (.some x₀ y₀ h₀ : W.Point) + .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have ha₁ : Valued.v W.a₁ ≤ 1 := valued_a₁ hW
  have ha₂ : Valued.v W.a₂ ≤ 1 := valued_a₂ hW
  rw [Point.add_some (fun hc ↦ hψ hc.2), some_mem_filtration, Affine.addX]
  set L : v.adicCompletion K := W.slope x₀ x₀ y₀ y₀ with hL
  have hL₁ : (1 : ℤᵐ⁰) < Valued.v L :=
    lt_of_lt_of_le (by rw [← exp_zero, exp_lt_exp]; lia) hs
  have hbig : ∀ c : ℤᵐ⁰, c ≤ 1 → c < Valued.v L ^ 2 := fun c hc ↦
    lt_of_le_of_lt hc (by
      calc
        (1 : ℤᵐ⁰) < Valued.v L := hL₁
        _ = Valued.v L ^ 1 := (pow_one _).symm
        _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL₁ (by lia))
  have hrest : Valued.v (W.a₁ * L - W.a₂ - x₀ - x₀) < Valued.v L ^ 2 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt
      (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt
        (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ (hbig _ ha₂)))
        (hbig _ hx₀))) (hbig _ hx₀))
    rw [map_mul]
    calc
      Valued.v W.a₁ * Valued.v L ≤ 1 * Valued.v L := mul_le_mul' ha₁ le_rfl
      _ = Valued.v L ^ 1 := by rw [one_mul, pow_one]
      _ < Valued.v L ^ 2 := pow_lt_pow_right₀ hL₁ (by lia)
  rw [show L ^ 2 + W.a₁ * L - W.a₂ - x₀ - x₀ =
      L ^ 2 + (W.a₁ * L - W.a₂ - x₀ - x₀) by ring,
    Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hrest), map_pow]
  refine le_trans (le_of_eq ?_) (pow_le_pow_left' hs 2)
  rw [← exp_nsmul, nsmul_eq_mul]
  norm_num

include hW in
private theorem add_self_mem_filtration_of_sub_negY_small
    {x₀ y₀ : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (hx₀ : Valued.v x₀ ≤ 1) (hy₀ : Valued.v y₀ ≤ 1)
    (hred : (adicRedCurve W₀).Nonsingular (res⟨x₀, hx₀⟩) (res⟨y₀, hy₀⟩))
    (hψsmall : Valued.v (y₀ - W.negY x₀ y₀) ≤ exp (-1 : ℤ))
    (hψ₀ : y₀ - W.negY x₀ y₀ ≠ 0) :
    (.some x₀ y₀ h₀ : W.Point) + .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  have hφ₁ : Valued.v (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = 1 := by
    rcases unit_deriv_of_nonsingular_reduction hW hx₀ hy₀ hred with hψ₁ | hφ₁
    · exact absurd hψsmall (by rw [hψ₁, ← exp_zero, exp_le_exp]; lia)
    · exact hφ₁
  have hψne : y₀ ≠ W.negY x₀ y₀ := fun hc ↦ hψ₀ (sub_eq_zero.mpr hc)
  refine add_self_mem_filtration_of_slope hW h₀ hx₀ hψne ?_
  rw [W.slope_of_Y_ne rfl hψne, map_div₀]
  obtain ⟨dψ, hdψ⟩ : ∃ dψ : ℤ, Valued.v (y₀ - W.negY x₀ y₀) = exp dψ :=
    ⟨_, (exp_log (by simpa using hψ₀)).symm⟩
  have hnumφ :
      Valued.v (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀) = 1 := by
    rw [show 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ =
      -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) by ring,
      Valuation.map_neg, hφ₁]
  have hdψ' : dψ ≤ -1 := by rwa [hdψ, exp_le_exp] at hψsmall
  rw [hnumφ, hdψ, ← exp_zero, ← exp_sub, exp_le_exp]
  lia

include hW in
private theorem sub_mem_filtration_of_close_of_X_ne
    {x₀ y₀ : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (hx₀ : Valued.v x₀ ≤ 1) (hy₀ : Valued.v y₀ ≤ 1)
    (hred : (adicRedCurve W₀).Nonsingular (res⟨x₀, hx₀⟩) (res⟨y₀, hy₀⟩))
    {x y : v.adicCompletion K} (h : W.Nonsingular x y) (hxx : x ≠ x₀)
    (hx : Valued.v (x - x₀) ≤ exp (-1 : ℤ))
    (hy : Valued.v (y - y₀) ≤ exp (-1 : ℤ)) :
    (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  refine sub_mem_filtration_of_slope hW h₀ h hxx hx₀ (valued_le_one_of_sub hx hx₀) ?_
  rcases unit_deriv_of_nonsingular_reduction hW hx₀ hy₀ hred with hψ₁ | hφ₁
  · have hnum : Valued.v (y - W.negY x₀ y₀) = 1 := by
      rw [show y - W.negY x₀ y₀ = (y₀ - W.negY x₀ y₀) + (y - y₀) by ring,
        Valuation.map_add_eq_of_lt_left, hψ₁]
      refine lt_of_le_of_lt hy ?_
      rw [hψ₁, ← exp_zero, exp_lt_exp]
      lia
    obtain ⟨dx, hdx⟩ : ∃ dx : ℤ, Valued.v (x - x₀) = exp dx :=
      ⟨_, (exp_log (by simpa using sub_ne_zero.mpr hxx)).symm⟩
    have hdx' : dx ≤ -1 := by rwa [hdx, exp_le_exp] at hx
    rw [map_div₀, hnum, hdx, ← exp_zero, ← exp_sub, exp_le_exp]
    lia
  · have hid : (y - W.negY x₀ y₀) * (y - y₀) =
        (x - x₀) * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y) := by
      rw [Affine.negY]
      linear_combination (W.equation_iff x y).mp h.left -
        (W.equation_iff x₀ y₀).mp h₀.left
    have hval := congrArg Valued.v hid
    rw [map_mul, map_mul,
      valued_num_of_two_torsion hW hx₀ (hφ₁.trans exp_zero.symm) (by norm_num) hx hy] at hval
    exact exp_one_le_valued_slope hxx (by norm_num) hy hval

include hW in
private theorem sub_mem_filtration_of_equal_residues
    {x₀ y₀ : v.adicCompletion K}
    (h₀ : W.Nonsingular x₀ y₀) (hx₀ : Valued.v x₀ ≤ 1) (hy₀ : Valued.v y₀ ≤ 1)
    (hred : (adicRedCurve W₀).Nonsingular (res⟨x₀, hx₀⟩) (res⟨y₀, hy₀⟩))
    {x y : v.adicCompletion K} (h : W.Nonsingular x y)
    (hx : Valued.v (x - x₀) ≤ exp (-1 : ℤ))
    (hy : Valued.v (y - y₀) ≤ exp (-1 : ℤ)) :
    (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 := by
  rcases eq_or_ne x x₀ with heq | hxx
  · subst x
    rcases W.Y_eq_of_X_eq h.left h₀.left rfl with hy' | hy'
    · rw [show (.some x₀ y h : W.Point) = .some x₀ y₀ h₀ by subst hy'; rfl, sub_self]
      exact zero_mem _
    · have hψsmall : Valued.v (y₀ - W.negY x₀ y₀) ≤ exp (-1 : ℤ) := by
        rw [show y₀ - W.negY x₀ y₀ = -(y - y₀) by rw [hy']; ring,
          Valuation.map_neg]
        exact hy
      rcases eq_or_ne (y₀ - W.negY x₀ y₀) 0 with hψ₀ | hψ₀
      · rw [show (.some x₀ y h : W.Point) = .some x₀ y₀ h₀ by
          congr 1
          rw [hy', ← sub_eq_zero,
            show W.negY x₀ y₀ - y₀ = -(y₀ - W.negY x₀ y₀) by ring,
            hψ₀, neg_zero], sub_self]
        exact zero_mem _
      · have hP : (.some x₀ y h : W.Point) = -.some x₀ y₀ h₀ := by
          rw [Point.neg_some]
          subst hy'
          rfl
        rw [hP, show -(.some x₀ y₀ h₀ : W.Point) - .some x₀ y₀ h₀ =
          -(.some x₀ y₀ h₀ + .some x₀ y₀ h₀) by abel]
        exact neg_mem (add_self_mem_filtration_of_sub_negY_small
          hW h₀ hx₀ hy₀ hred hψsmall hψ₀)
  · exact sub_mem_filtration_of_close_of_X_ne
      hW h₀ hx₀ hy₀ hred h hxx hx hy

/-- Equal coordinatewise reductions in the nonsingular locus differ by the exact formal
filtration.  This is the singular-special-fibre version of the exact-pin congruence criterion;
only nonsingularity of the displayed common reduction is used. -/
theorem sub_mem_filtration_of_nonsingularReduction_eq
    {P Q : W.Point} (hP : HasNonsingularReduction hW P) (hQ : HasNonsingularReduction hW Q)
    (hPQ : nonsingularReduction hW ⟨P, hP⟩ = nonsingularReduction hW ⟨Q, hQ⟩) :
    P - Q ∈ filtration hW 0 := by
  by_cases hQ₀ : Q ∈ filtration hW 0
  · exact AddSubgroup.sub_mem _
      ((nonsingularReduction_eq_zero_iff hW P hP).mp
        (hPQ.trans ((nonsingularReduction_eq_zero_iff hW Q hQ).mpr hQ₀))) hQ₀
  · have hP₀ : P ∉ filtration hW 0 := fun h ↦ hQ₀
      ((nonsingularReduction_eq_zero_iff hW Q hQ).mp
        (hPQ.symm.trans ((nonsingularReduction_eq_zero_iff hW P hP).mpr h)))
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd zero_mem_filtration hP₀
    rcases Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd zero_mem_filtration hQ₀
    have hPm : ¬ exp (2 : ℤ) ≤ Valued.v x := fun hc ↦ hP₀ (some_mem_filtration.mpr hc)
    have hQm : ¬ exp (2 : ℤ) ≤ Valued.v x₀ := fun hc ↦ hQ₀ (some_mem_filtration.mpr hc)
    obtain ⟨hxi, hyi⟩ := integral_of_not_mem hW hxy.left hPm
    obtain ⟨hxi₀, hyi₀⟩ := integral_of_not_mem hW h₀.left hQm
    rw [nonsingularReduction_some_of_not_mem hW hP hPm,
      nonsingularReduction_some_of_not_mem hW hQ hQm, Point.some.injEq] at hPQ
    refine sub_mem_filtration_of_equal_residues hW h₀ hxi₀ hyi₀ (hQ hQm) hxy ?_ ?_
    · refine mem_maximalIdeal_iff (x := ⟨x - x₀, valued_sub_le hxi hxi₀⟩) |>.mp
        (residue_eq_zero_iff _ |>.mp ?_)
      rw [res_sub hxi hxi₀ (valued_sub_le hxi hxi₀), hPQ.1, sub_self]
    · refine mem_maximalIdeal_iff (x := ⟨y - y₀, valued_sub_le hyi hyi₀⟩) |>.mp
        (residue_eq_zero_iff _ |>.mp ?_)
      rw [res_sub hyi hyi₀ (valued_sub_le hyi hyi₀), hPQ.2, sub_self]

end

include hW in
private theorem nonsingularReduction_neg
    {P : W.Point} (hP : HasNonsingularReduction hW P) :
    nonsingularReduction hW ⟨-P, hasNonsingularReduction_neg hW hP⟩ =
      -nonsingularReduction hW ⟨P, hP⟩ := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [Point.neg_some]
    by_cases hx : exp (2 : ℤ) ≤ Valued.v x
    · rw [nonsingularReduction_some_of_mem hW _ hx,
        nonsingularReduction_some_of_mem hW hP hx, neg_zero]
    · rw [nonsingularReduction_some_of_not_mem hW _ hx,
        nonsingularReduction_some_of_not_mem hW hP hx]
      calc
        .some
            (res ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
            (res ⟨W.negY x y,
              (integral_of_not_mem hW ((W.nonsingular_neg x y).mpr h).left hx).2⟩) _ =
          .some
            (res ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
            ((adicRedCurve W₀).negY
              (res ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
              (res ⟨y, (integral_of_not_mem hW h.left hx).2⟩))
            ((adicRedCurve W₀).nonsingular_neg _ _ |>.mpr (hP hx)) := by
              rw [Point.some.injEq]
              exact ⟨rfl, redCoord_negY hW
                (integral_of_not_mem hW h.left hx).1
                (integral_of_not_mem hW h.left hx).2
                (integral_of_not_mem hW ((W.nonsingular_neg x y).mpr h).left hx).2⟩
        _ = -(.some
            (res ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
            (res ⟨y, (integral_of_not_mem hW h.left hx).2⟩)
            (hP hx) : (adicRedCurve W₀).Point) :=
          (Point.neg_some (hP hx)).symm

section

variable [CharZero K]

include hW in
/-- Translation by a point of the formal kernel preserves the canonical nonsingular-reduction
domain and does not change coordinatewise reduction. -/
theorem nonsingularReduction_add_of_mem_filtration_left
    {P Q : W.Point} (hP : P ∈ filtration hW 0) (hQ : HasNonsingularReduction hW Q) :
    ∃ hPQ : HasNonsingularReduction hW (P + Q),
      nonsingularReduction hW ⟨P + Q, hPQ⟩ = nonsingularReduction hW ⟨Q, hQ⟩ := by
  by_cases hQ₀ : Q ∈ filtration hW 0
  · have hPQmem : P + Q ∈ filtration hW 0 := add_mem hP hQ₀
    let hPQ : HasNonsingularReduction hW (P + Q) :=
      hasNonsingularReduction_of_mem_filtration hW hPQmem
    refine ⟨hPQ, ?_⟩
    rw [(nonsingularReduction_eq_zero_iff hW (P + Q) hPQ).mpr hPQmem,
      (nonsingularReduction_eq_zero_iff hW Q hQ).mpr hQ₀]
  · have hPQ₀ : P + Q ∉ filtration hW 0 := fun h ↦ hQ₀ (by
      simpa using AddSubgroup.sub_mem (filtration hW 0) h hP)
    rcases Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd zero_mem_filtration hQ₀
    have hQm : ¬ exp (2 : ℤ) ≤ Valued.v x₀ :=
      fun hc ↦ hQ₀ (some_mem_filtration.mpr hc)
    obtain ⟨hx₀, hy₀⟩ := integral_of_not_mem hW h₀.left hQm
    generalize hS : P + (.some x₀ y₀ h₀ : W.Point) = S
    rcases S with _ | ⟨x, y, h⟩
    · exact absurd zero_mem_filtration (hS ▸ hPQ₀)
    have hSm : ¬ exp (2 : ℤ) ≤ Valued.v x := fun hc ↦
      hPQ₀ (by rw [hS]; exact some_mem_filtration.mpr hc)
    obtain ⟨hx, hy⟩ := integral_of_not_mem hW h.left hSm
    have hcoords : res (⟨x, hx⟩ : v.adicCompletionIntegers K) = res ⟨x₀, hx₀⟩ ∧
        res (⟨y, hy⟩ : v.adicCompletionIntegers K) = res ⟨y₀, hy₀⟩ := by
      by_contra hneCoords
      have hnegY₀ : Valued.v (W.negY x₀ y₀) ≤ 1 := valued_negY_le hW hx₀ hy₀
      have hne : ¬ (res (⟨x, hx⟩ : v.adicCompletionIntegers K) = res ⟨x₀, hx₀⟩ ∧
          res ⟨y, hy⟩ = (adicRedCurve W₀).negY
            (res ⟨x₀, hx₀⟩) (res ⟨W.negY x₀ y₀, hnegY₀⟩)) := by
        rintro ⟨hX, hY⟩
        apply hneCoords
        refine ⟨hX, ?_⟩
        rw [redCoord_negY hW hx₀ hy₀ hnegY₀,
          (adicRedCurve W₀).negY_negY] at hY
        exact hY
      have hlocal : ¬ (x = x₀ ∧ y = W.negY x₀ (W.negY x₀ y₀)) := by
        rintro ⟨hX, hY⟩
        apply hne
        refine ⟨congrArg (IsLocalRing.residue (v.adicCompletionIntegers K))
          (Subtype.ext hX), ?_⟩
        have hnegneg : W.negY x₀ (W.negY x₀ y₀) = y₀ := W.negY_negY x₀ y₀
        have hyEq : y = y₀ := hY.trans hnegneg
        calc
          res (⟨y, hy⟩ : v.adicCompletionIntegers K) = res ⟨y₀, hy₀⟩ :=
            congrArg (IsLocalRing.residue (v.adicCompletionIntegers K)) (Subtype.ext hyEq)
          _ = (adicRedCurve W₀).negY (res ⟨x₀, hx₀⟩)
              (res ⟨W.negY x₀ y₀, hnegY₀⟩) := by
            have hdoubleVal : Valued.v (W.negY x₀ (W.negY x₀ y₀)) ≤ 1 := by
              rw [hnegneg]
              exact hy₀
            have hdouble := redCoord_negY hW hx₀ hnegY₀ hdoubleVal
            have hsub :
                (⟨W.negY x₀ (W.negY x₀ y₀), hdoubleVal⟩ :
                    v.adicCompletionIntegers K) =
                  ⟨y₀, hy₀⟩ := Subtype.ext hnegneg
            exact (congrArg (IsLocalRing.residue (v.adicCompletionIntegers K)) hsub).symm.trans
              hdouble
      have hℓ : Valued.v (W.slope x x₀ y (W.negY x₀ y₀)) ≤ 1 :=
        valued_slope_le hW hx hx₀ hy hnegY₀ h.left
          ((W.nonsingular_neg x₀ y₀).mpr h₀).left hne
      have haX : Valued.v (W.addX x x₀ (W.slope x x₀ y (W.negY x₀ y₀))) ≤ 1 := by
        rw [coe_addX hW hx hx₀ hℓ]
        exact ((W₀.toAffine).addX ⟨x, hx⟩ ⟨x₀, hx₀⟩
          ⟨W.slope x x₀ y (W.negY x₀ y₀), hℓ⟩).property
      have hdiff : (.some x y h : W.Point) - .some x₀ y₀ h₀ = P := by
        rw [← hS]
        abel
      have hsum : (.some x y h : W.Point) - .some x₀ y₀ h₀ =
          .some
            (W.addX x x₀ (W.slope x x₀ y (W.negY x₀ y₀)))
            (W.addY x x₀ y (W.slope x x₀ y (W.negY x₀ y₀)))
            (nonsingular_add h ((W.nonsingular_neg x₀ y₀).mpr h₀) hlocal) := by
        rw [sub_eq_add_neg, Point.neg_some, Point.add_some hlocal]
      have hsumMem : (.some x y h : W.Point) - .some x₀ y₀ h₀ ∈ filtration hW 0 :=
        hdiff.symm ▸ hP
      rw [hsum, some_mem_filtration] at hsumMem
      exact not_exp_two_le_of_le_one haX hsumMem
    have hSred : HasNonsingularReduction hW (.some x y h) := by
      intro _
      simpa only [hcoords.1, hcoords.2] using hQ hQm
    have hredEq : nonsingularReduction hW ⟨(.some x y h : W.Point), hSred⟩ =
        nonsingularReduction hW ⟨(.some x₀ y₀ h₀ : W.Point), hQ⟩ := by
      rw [nonsingularReduction_some_of_not_mem hW hSred hSm,
        nonsingularReduction_some_of_not_mem hW hQ hQm, Point.some.injEq]
      exact hcoords
    refine ⟨?_, ?_⟩
    · simpa only [hS] using hSred
    · simpa only [hS] using hredEq

omit [CharZero K] in
include hW in
private theorem nonsingularReduction_add_of_reduced_ne_neg
    {x₁ x₂ y₁ y₂ : v.adicCompletion K}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hP : HasNonsingularReduction hW (.some x₁ y₁ h₁))
    (hQ : HasNonsingularReduction hW (.some x₂ y₂ h₂))
    (hPm : ¬ exp (2 : ℤ) ≤ Valued.v x₁) (hQm : ¬ exp (2 : ℤ) ≤ Valued.v x₂)
    (hne : nonsingularReduction hW ⟨.some x₁ y₁ h₁, hP⟩ ≠
      -nonsingularReduction hW ⟨.some x₂ y₂ h₂, hQ⟩) :
    ∃ hsum : HasNonsingularReduction hW
        ((.some x₁ y₁ h₁ : W.Point) + .some x₂ y₂ h₂),
      nonsingularReduction hW ⟨.some x₁ y₁ h₁ + .some x₂ y₂ h₂, hsum⟩ =
        nonsingularReduction hW ⟨.some x₁ y₁ h₁, hP⟩ +
          nonsingularReduction hW ⟨.some x₂ y₂ h₂, hQ⟩ := by
  obtain ⟨hx₁, hy₁⟩ := integral_of_not_mem hW h₁.left hPm
  obtain ⟨hx₂, hy₂⟩ := integral_of_not_mem hW h₂.left hQm
  have hneRes : ¬ (res (⟨x₁, hx₁⟩ : v.adicCompletionIntegers K) = res ⟨x₂, hx₂⟩ ∧
      res ⟨y₁, hy₁⟩ = (adicRedCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩)) := by
    rintro ⟨hX, hY⟩
    apply hne
    rw [nonsingularReduction_some_of_not_mem hW hP hPm,
      nonsingularReduction_some_of_not_mem hW hQ hQm]
    calc
      .some (res ⟨x₁, hx₁⟩) (res ⟨y₁, hy₁⟩) (hP hPm) =
          .some (res ⟨x₂, hx₂⟩)
            ((adicRedCurve W₀).negY (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩))
            ((adicRedCurve W₀).nonsingular_neg _ _ |>.mpr (hQ hQm)) := by
        rw [Point.some.injEq]
        exact ⟨hX, hY⟩
      _ = -(.some (res ⟨x₂, hx₂⟩) (res ⟨y₂, hy₂⟩) (hQ hQm) :
          (adicRedCurve W₀).Point) := (Point.neg_some (hQ hQm)).symm
  have hlocal : ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) :=
    not_eq_and_eq_negY_of_reduced hW hx₁ hx₂ hy₁ hy₂ hneRes
  have hℓ : Valued.v (W.slope x₁ x₂ y₁ y₂) ≤ 1 :=
    valued_slope_le hW hx₁ hx₂ hy₁ hy₂ h₁.left h₂.left hneRes
  have haX : Valued.v (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) ≤ 1 := by
    rw [coe_addX hW hx₁ hx₂ hℓ]
    exact ((W₀.toAffine).addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
      ⟨W.slope x₁ x₂ y₁ y₂, hℓ⟩).property
  have haY : Valued.v (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) ≤ 1 := by
    rw [coe_addY hW hx₁ hx₂ hy₁ hℓ]
    exact ((W₀.toAffine).addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
      ⟨W.slope x₁ x₂ y₁ y₂, hℓ⟩).property
  have hslope := red_slope hW hx₁ hx₂ hy₁ hy₂ h₁.left h₂.left hℓ hneRes
  have hgate := not_exp_two_le_of_le_one haX
  let hsumNonsingular : W.Nonsingular
      (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
      (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) :=
    nonsingular_add h₁ h₂ hlocal
  let S : W.Point := .some
    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
    (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) hsumNonsingular
  have hSred : HasNonsingularReduction hW S := by
    intro _
    change (adicRedCurve W₀).Nonsingular
      (res ⟨W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂), haX⟩)
      (res ⟨W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂), haY⟩)
    rw [redCoord_addX hW hx₁ hx₂ hℓ haX,
      redCoord_addY hW hx₁ hx₂ hy₁ hℓ haY, hslope]
    exact nonsingular_add (hP hPm) (hQ hQm) hneRes
  have hSredEq : nonsingularReduction hW ⟨S, hSred⟩ =
      nonsingularReduction hW ⟨(.some x₁ y₁ h₁ : W.Point), hP⟩ +
        nonsingularReduction hW ⟨(.some x₂ y₂ h₂ : W.Point), hQ⟩ := by
    change nonsingularReduction hW ⟨(.some
      (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
      (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) hsumNonsingular : W.Point), hSred⟩ = _
    rw [nonsingularReduction_some_of_not_mem hW _ hgate,
      nonsingularReduction_some_of_not_mem hW hP hPm,
      nonsingularReduction_some_of_not_mem hW hQ hQm, Point.add_some hneRes, Point.some.injEq]
    exact ⟨(redCoord_addX hW hx₁ hx₂ hℓ haX).trans (by rw [hslope]),
      (redCoord_addY hW hx₁ hx₂ hy₁ hℓ haY).trans (by rw [hslope])⟩
  have hadd : (.some x₁ y₁ h₁ : W.Point) + .some x₂ y₂ h₂ = S := by
    rw [Point.add_some hlocal]
  refine ⟨?_, ?_⟩
  · simpa only [hadd] using hSred
  · simpa only [hadd] using hSredEq

include hW in
private theorem nonsingularReduction_add_of_not_mem
    {P Q : W.Point} (hP : HasNonsingularReduction hW P) (hQ : HasNonsingularReduction hW Q)
    (hP₀ : P ∉ filtration hW 0) (hQ₀ : Q ∉ filtration hW 0) :
    ∃ hPQ : HasNonsingularReduction hW (P + Q),
      nonsingularReduction hW ⟨P + Q, hPQ⟩ =
        nonsingularReduction hW ⟨P, hP⟩ + nonsingularReduction hW ⟨Q, hQ⟩ := by
  by_cases hop : nonsingularReduction hW ⟨P, hP⟩ = -nonsingularReduction hW ⟨Q, hQ⟩
  · have hnegQ := hasNonsingularReduction_neg hW hQ
    have heq : nonsingularReduction hW ⟨P, hP⟩ = nonsingularReduction hW ⟨-Q, hnegQ⟩ :=
      hop.trans (nonsingularReduction_neg hW hQ).symm
    have hmem : P + Q ∈ filtration hW 0 := by
      have hdiff := sub_mem_filtration_of_nonsingularReduction_eq hW hP hnegQ heq
      simpa [sub_neg_eq_add] using hdiff
    let hPQ : HasNonsingularReduction hW (P + Q) :=
      hasNonsingularReduction_of_mem_filtration hW hmem
    refine ⟨hPQ, ?_⟩
    rw [(nonsingularReduction_eq_zero_iff hW (P + Q) hPQ).mpr hmem, hop, neg_add_cancel]
  · rcases P with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd zero_mem_filtration hP₀
    rcases Q with _ | ⟨x₂, y₂, h₂⟩
    · exact absurd zero_mem_filtration hQ₀
    exact nonsingularReduction_add_of_reduced_ne_neg hW h₁ h₂ hP hQ
      (fun hc ↦ hP₀ (some_mem_filtration.mpr hc))
      (fun hc ↦ hQ₀ (some_mem_filtration.mpr hc)) hop

/-- Coordinatewise reduction to the nonsingular locus is additive on its canonical domain.
This discharges the sole group-law premise left by `NonsingularReductionIsAdditive`. -/
theorem nonsingularReduction_isAdditive : NonsingularReductionIsAdditive hW := by
  intro P Q hP hQ
  by_cases hP₀ : P ∈ filtration hW 0
  · obtain ⟨hPQ, hred⟩ := nonsingularReduction_add_of_mem_filtration_left hW hP₀ hQ
    refine ⟨hPQ, ?_⟩
    rw [hred, (nonsingularReduction_eq_zero_iff hW P hP).mpr hP₀, zero_add]
  · by_cases hQ₀ : Q ∈ filtration hW 0
    · obtain ⟨hQP, hred⟩ := nonsingularReduction_add_of_mem_filtration_left hW hQ₀ hP
      have hadd : P + Q = Q + P := add_comm P Q
      let hPQ : HasNonsingularReduction hW (P + Q) := hadd ▸ hQP
      refine ⟨hPQ, ?_⟩
      have hred' : nonsingularReduction hW ⟨P + Q, hPQ⟩ = nonsingularReduction hW ⟨P, hP⟩ := by
        simpa only [hadd] using hred
      rw [hred', (nonsingularReduction_eq_zero_iff hW Q hQ).mpr hQ₀, add_zero]
    · exact nonsingularReduction_add_of_not_mem hW hP hQ hP₀ hQ₀

end

end WeierstrassCurve.Affine

namespace MazurTorsion.EllipticCurve

open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain.HeightOneSpectrum

local instance : DecidableEq
    (ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

local instance : DecidableEq
    (ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- Construct the five-adic tame-additive handoff from canonical nonsingular reduction.  The
group-law premise is discharged by `nonsingularReduction_isAdditive`; the remaining arguments
are exactly the special-cubic classification and component bound. -/
def TameAdditiveReductionDataAtFive.ofCanonicalNonsingularReduction
    {W : Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    {hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)) = W}
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    (especial : (adicRedCurve W₀).Point ≃+
      ResidueField (atFive.adicCompletionIntegers ℚ))
    (hcomponent : Nat.card
      (W.Point ⧸ nonsingularReductionSubgroup hW (nonsingularReduction_isAdditive hW)) ≤ 4) :
    TameAdditiveReductionDataAtFive hW :=
  TameAdditiveReductionDataAtFive.ofNonsingularReduction
    (nonsingularReduction_isAdditive hW) especial hcomponent

/-- The identical canonical construction at eleven, for the order-35 additive branch. -/
def TameAdditiveReductionDataAtEleven.ofCanonicalNonsingularReduction
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    {hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)) = W}
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (especial : (adicRedCurve W₀).Point ≃+
      ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : Nat.card
      (W.Point ⧸ nonsingularReductionSubgroup hW (nonsingularReduction_isAdditive hW)) ≤ 4) :
    TameAdditiveReductionDataAtEleven hW :=
  TameAdditiveReductionDataAtEleven.ofNonsingularReduction
    (nonsingularReduction_isAdditive hW) especial hcomponent

end MazurTorsion.EllipticCurve
