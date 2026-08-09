/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionClassNumber

/-!
# Real places of the `X₁(18)` two-division compositum

This file starts the signature calculation needed by the unit square-class
count.  The relative cubic `S³ - 3S - 10` has at most one real root.  Hence
restriction to the real cubic coefficient field injects the real embeddings
of the degree-nine compositum into the three embeddings of that coefficient
field.

The complementary lower bound is kept separate: it will be supplied by the
signed discriminant certificate for a rational power basis.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenTwoDivisionSignature

noncomputable section

open NumberField NumberField.InfinitePlace
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber

private theorem unique_real_root_twoDivisionCubic
    {a b : ℝ}
    (ha : a ^ 3 = 3 * a + 10)
    (hb : b ^ 3 = 3 * b + 10) :
    a = b := by
  by_contra hab
  have hfactor :
      (a - b) * (a ^ 2 + a * b + b ^ 2 - 3) = 0 := by
    linear_combination ha - hb
  have hquad : a ^ 2 + a * b + b ^ 2 = 3 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact (hab (sub_eq_zero.mp h)).elim
    · linarith
  have ha_sq_le : a ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (a + 2 * b)]
  have ha_le : a ≤ 2 := by
    nlinarith [sq_nonneg (a - 2)]
  have hcubic_le : a ^ 3 - 3 * a ≤ 2 := by
    have hnonneg : 0 ≤ (2 - a) * (a + 1) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr ha_le) (sq_nonneg (a + 1))
    nlinarith
  nlinarith

private def restrictRealEmbedding :
    { φ : M →+* ℂ // ComplexEmbedding.IsReal φ } → (Q.K →+* ℂ) :=
  fun φ ↦ φ.1.comp (algebraMap Q.K M)

private theorem restrictRealEmbedding_injective :
    Function.Injective restrictRealEmbedding := by
  intro φ ψ hrestrict
  apply Subtype.ext
  apply AdjoinRoot.ringHom_ext hrestrict
  let a : ℝ := φ.2.embedding s
  let b : ℝ := ψ.2.embedding s
  have ha : a ^ 3 = 3 * a + 10 := by
    simpa only [a, map_pow, map_mul, map_ofNat, map_add] using
      congrArg φ.2.embedding s_cubic
  have hb : b ^ 3 = 3 * b + 10 := by
    simpa only [b, map_pow, map_mul, map_ofNat, map_add] using
      congrArg ψ.2.embedding s_cubic
  have hab : a = b := unique_real_root_twoDivisionCubic ha hb
  calc
    φ.1 (AdjoinRoot.root relativePolynomial) = (a : ℂ) := by
      symm
      simpa only [a, s] using φ.2.coe_embedding_apply s
    _ = (b : ℂ) := congrArg ((↑·) : ℝ → ℂ) hab
    _ = ψ.1 (AdjoinRoot.root relativePolynomial) := by
      simpa only [b, s] using ψ.2.coe_embedding_apply s

private theorem coefficientField_finrank :
    Module.finrank ℚ Q.K = 3 := by
  calc
    Module.finrank ℚ Q.K = Q.cubicPolynomial.natDegree :=
      (AdjoinRoot.powerBasis Q.cubicPolynomial_irreducible.ne_zero).finrank
    _ = 3 := by
      simp only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
      compute_degree!

/-- The degree-nine two-division compositum has at most three real places.
The eventual unit square-class computation is the named downstream consumer
of this bound. -/
theorem nrRealPlaces_le_three : nrRealPlaces M ≤ 3 := by
  classical
  rw [← card_real_embeddings]
  calc
    Fintype.card { φ : M →+* ℂ // ComplexEmbedding.IsReal φ } ≤
        Fintype.card (Q.K →+* ℂ) :=
      Fintype.card_le_of_injective restrictRealEmbedding
        restrictRealEmbedding_injective
    _ = Module.finrank ℚ Q.K := NumberField.Embeddings.card Q.K ℂ
    _ = 3 := coefficientField_finrank

end

end MazurTorsion.XOneEighteenTwoDivisionSignature
