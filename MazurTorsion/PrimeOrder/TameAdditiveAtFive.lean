/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TameAdditiveFiltration
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Tactic.NormNum

/-!
# The tame additive contradiction at residue characteristic five

This is the prime-route consumer of the algebraic Néron filtration boundary.
It remains conditional on construction of that filtration from the actual
local elliptic curve.
-/

namespace MazurTorsion.PrimeOrder

open MazurTorsion.EllipticCurve
open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

universe u v

section ReductionType

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Multiplicative reduction forces the `j`-invariant to have valuation strictly greater than
one.  This is the elementary bridge from the integral-`j` formulation of potentially good
reduction to the reduction-type trichotomy. -/
theorem valuation_j_gt_one_of_hasMultiplicativeReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : W.HasMultiplicativeReduction R) :
    1 < valuation K (maximalIdeal R) W.j := by
  rw [WeierstrassCurve.j]
  simp only [Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_pow,
    WeierstrassCurve.coe_Δ',
    hW.multiplicativeReduction, one_pow, mul_one]
  exact one_lt_inv_iff₀.mpr
    ⟨(valuation K (maximalIdeal R)).pos_iff.mpr (by
        simpa only [WeierstrassCurve.coe_Δ'] using W.Δ'.ne_zero),
      hW.badReduction⟩

/-- An integral `j`-invariant excludes multiplicative reduction of a minimal equation. -/
theorem not_hasMultiplicativeReduction_of_valuation_j_le_one
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1) :
    ¬ W.HasMultiplicativeReduction R := by
  intro hW
  exact (not_lt_of_ge hj) (valuation_j_gt_one_of_hasMultiplicativeReduction hW)

end ReductionType

/-- A tame additive filtration with five-element residue group has no point
of prime exact order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive
    {G : Type u} [AddCommGroup G]
    (F : TameAdditiveFiltrationData.{u, v} G)
    (hresidue : Nat.card F.ResidueAdditive = 5)
    (P : G) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  letI : AddCommGroup F.Component := F.componentAddCommGroup
  letI : Finite F.Component := F.componentFinite
  letI : AddCommGroup F.ResidueAdditive := F.residueAddCommGroup
  letI : Finite F.ResidueAdditive := F.residueFinite
  intro horder
  have hcomponentCoprime : N.Coprime (Nat.card F.Component) :=
    Nat.coprime_of_lt_prime Nat.card_pos.ne'
      (lt_of_le_of_lt F.component_card_le_four (by omega)) hprime
  have hresidueCoprime : N.Coprime (Nat.card F.ResidueAdditive) := by
    rw [hresidue]
    exact Nat.coprime_of_lt_prime (by norm_num) (by omega) hprime
  have hzero := F.point_eq_zero_of_coprime_card hprime.ne_zero
    hcomponentCoprime hresidueCoprime horder
  rw [hzero] at horder
  simp at horder
  omega

/-- Integral `j`, the actual tame additive Néron filtration, and a marked prime-order point
upgrade a minimal equation to good reduction.  The proof uses Mathlib's exhaustive
good/multiplicative/additive trichotomy: integral `j` excludes the multiplicative branch and the
two finite quotients plus torsion-free formal kernel exclude the additive branch.

This is the checked local consumer expected after the formal-immersion argument supplies
potentially good reduction.  Constructing `F` from the genuine Néron model remains the geometric
input; it is not hidden in this statement. -/
theorem hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1)
    {G : Type u} [AddCommGroup G]
    (F : W.HasAdditiveReduction R → TameAdditiveFiltrationData.{u, v} G)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : G) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    W.HasGoodReduction R := by
  rcases W.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R with
    hgood | hmultiplicative | hadditive
  · exact hgood
  · exact (not_hasMultiplicativeReduction_of_valuation_j_le_one hj hmultiplicative).elim
  · exact (addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive
      (F hadditive) (hresidue hadditive) P N hprime hN horder).elim

end MazurTorsion.PrimeOrder
