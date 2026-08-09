/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCyclotomicNorms
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Powers of the prime above thirteen in the thirteenth cyclotomic field

Let `λ = (1 - ζ₁₃)` in the ring of integers of `ℚ(ζ₁₃)`.  This file proves
directly that `λ` is a prime ideal of absolute norm thirteen and computes the
cardinality of the quotient and its unit group modulo every positive power of
`λ`.

No ray class group or class-field-theoretic interface is introduced here.  The
unit count is elementary: modulo `λ ^ n`, the nonunits are exactly the image
of `λ`, whose cardinality is obtained from the quotient-cardinality tower.
-/

namespace MazurTorsion.XOneThirteenCyclotomic

open scoped NumberField

noncomputable section

local notation "O₁₃" => 𝓞 ThirteenCyclotomicField

/-- The checked integral representative really is `1 - ζ₁₃`. -/
theorem alphaThirteenInteger_eq_one_sub_zetaThirteenInteger :
    alphaThirteenInteger = 1 - zetaThirteenInteger := by
  simp [alphaThirteenInteger, evalAtZetaThirteen, alphaThirteen]

/-- The principal ideal `λ = (1 - ζ₁₃)`. -/
noncomputable def lambdaThirteenIdeal : Ideal O₁₃ :=
  Ideal.span ({1 - zetaThirteenInteger} : Set O₁₃)

/-- The displayed ideal is principal by construction. -/
theorem lambdaThirteenIdeal_isPrincipal : lambdaThirteenIdeal.IsPrincipal := by
  unfold lambdaThirteenIdeal
  infer_instance

/-- The exact absolute norm of `λ` is thirteen. -/
theorem lambdaThirteenIdeal_absNorm :
    Ideal.absNorm lambdaThirteenIdeal = 13 := by
  rw [lambdaThirteenIdeal, ← alphaThirteenInteger_eq_one_sub_zetaThirteenInteger,
    Ideal.absNorm_span_singleton, norm_alphaThirteenInteger]
  norm_num

/-- In particular, `λ` is nonzero. -/
theorem lambdaThirteenIdeal_ne_bot : lambdaThirteenIdeal ≠ ⊥ := by
  intro h
  have hnorm := lambdaThirteenIdeal_absNorm
  rw [h, Ideal.absNorm_bot] at hnorm
  norm_num at hnorm

/-- The ideal `λ` is prime. -/
theorem lambdaThirteenIdeal_isPrime : lambdaThirteenIdeal.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [lambdaThirteenIdeal_absNorm, Nat.irreducible_iff_prime]
  decide

/-- The nonzero prime `λ` is maximal in the Dedekind ring `O₁₃`. -/
theorem lambdaThirteenIdeal_isMaximal : lambdaThirteenIdeal.IsMaximal :=
  lambdaThirteenIdeal_isPrime.isMaximal lambdaThirteenIdeal_ne_bot

/-- Contracting `λ` to `ℤ` gives `(13)`. -/
theorem lambdaThirteenIdeal_comap :
    lambdaThirteenIdeal.comap (algebraMap ℤ O₁₃) =
      Ideal.span ({(13 : ℤ)} : Set ℤ) := by
  have h := Ideal.span_singleton_absNorm
    (I := lambdaThirteenIdeal) (by
      rw [lambdaThirteenIdeal_absNorm]
      decide)
  simpa [lambdaThirteenIdeal_absNorm] using h.symm

/-- Thus `λ` lies over the rational prime `(13)`. -/
theorem lambdaThirteenIdeal_liesOver :
    lambdaThirteenIdeal.LiesOver (Ideal.span ({(13 : ℤ)} : Set ℤ)) :=
  ⟨lambdaThirteenIdeal_comap.symm⟩

/-- Principality, primality, residue characteristic, and norm of `λ`, bundled
for downstream arithmetic. -/
theorem lambdaThirteenIdeal_certificate :
    lambdaThirteenIdeal.IsPrincipal ∧
      lambdaThirteenIdeal.IsPrime ∧
      lambdaThirteenIdeal.LiesOver (Ideal.span ({(13 : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm lambdaThirteenIdeal = 13 :=
  ⟨lambdaThirteenIdeal_isPrincipal, lambdaThirteenIdeal_isPrime,
    lambdaThirteenIdeal_liesOver, lambdaThirteenIdeal_absNorm⟩

/-- The quotient by `λ ^ n` has exactly `13 ^ n` elements. -/
theorem natCard_quotient_lambdaThirteenIdeal_pow (n : ℕ) :
    Nat.card (O₁₃ ⧸ lambdaThirteenIdeal ^ n) = 13 ^ n := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow,
    lambdaThirteenIdeal_absNorm]

/-- Every quotient by a power of `λ` is finite. -/
noncomputable instance finite_quotient_lambdaThirteenIdeal_pow (n : ℕ) :
    Finite (O₁₃ ⧸ lambdaThirteenIdeal ^ n) :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_quotient_lambdaThirteenIdeal_pow]
    positivity)

/-- A residue class modulo a positive power of `λ` is a unit exactly when
any displayed lift does not lie in `λ`. -/
theorem isUnit_mk_lambdaThirteenIdeal_pow_iff_notMem
    (n : ℕ) (hn : n ≠ 0) (x : O₁₃) :
    IsUnit (Ideal.Quotient.mk (lambdaThirteenIdeal ^ n) x) ↔
      x ∉ lambdaThirteenIdeal := by
  letI : lambdaThirteenIdeal.IsMaximal := lambdaThirteenIdeal_isMaximal
  exact Ideal.Quotient.isUnit_mk_pow_iff_notMem lambdaThirteenIdeal hn

private theorem natCard_units_add_natCard_nonunits
    (R : Type*) [Monoid R] [Finite R] :
    Nat.card Rˣ + Nat.card {x : R // ¬IsUnit x} = Nat.card R := by
  classical
  let e : IsUnit.submonoid R ≃ {x : R // IsUnit x} :=
    Equiv.subtypeEquivProp (by
      funext x
      exact propext (IsUnit.mem_submonoid_iff x))
  calc
    Nat.card Rˣ + Nat.card {x : R // ¬IsUnit x} =
        Nat.card {x : R // IsUnit x} + Nat.card {x : R // ¬IsUnit x} := by
      rw [Nat.card_congr Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv,
        Nat.card_congr e]
    _ = Nat.card ({x : R // IsUnit x} ⊕ {x : R // ¬IsUnit x}) := by
      rw [Nat.card_sum]
    _ = Nat.card R :=
      Nat.card_congr (Equiv.sumCompl fun x : R ↦ IsUnit x)

/-- The nonunits modulo `λ ^ n` are the additive image of `λ`. -/
private noncomputable def nonunitsEquivLambdaImage (n : ℕ) (hn : n ≠ 0) :
    {x : O₁₃ ⧸ lambdaThirteenIdeal ^ n // ¬IsUnit x} ≃
      Submodule.map (lambdaThirteenIdeal ^ n).mkQ lambdaThirteenIdeal := by
  classical
  refine
    { toFun := fun x ↦ ⟨x.1, ?_⟩
      invFun := fun x ↦ ⟨x.1, ?_⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl }
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.1
    rw [← ha]
    apply Submodule.mem_map_of_mem
    by_contra hnotMem
    apply x.2
    rw [← ha]
    exact (isUnit_mk_lambdaThirteenIdeal_pow_iff_notMem
      n hn a).mpr hnotMem
  · intro hunit
    rcases Submodule.mem_map.mp x.2 with ⟨a, ha, hax⟩
    have haUnit : IsUnit (Ideal.Quotient.mk (lambdaThirteenIdeal ^ n) a) := by
      change IsUnit ((lambdaThirteenIdeal ^ n).mkQ a)
      rwa [hax]
    exact ((isUnit_mk_lambdaThirteenIdeal_pow_iff_notMem
      n hn a).mp haUnit) ha

/-- The image `λ / λ ^ n` has `13 ^ (n - 1)` elements for `n > 0`. -/
private theorem natCard_lambdaImage (n : ℕ) (hn : n ≠ 0) :
    Nat.card
        (Submodule.map (lambdaThirteenIdeal ^ n).mkQ lambdaThirteenIdeal) =
      13 ^ (n - 1) := by
  have hle : lambdaThirteenIdeal ^ n ≤ lambdaThirteenIdeal :=
    Ideal.pow_le_self hn
  have hcard := Submodule.card_quotient_mul_card_quotient
    lambdaThirteenIdeal (lambdaThirteenIdeal ^ n) hle
  have hbase : Nat.card (O₁₃ ⧸ lambdaThirteenIdeal) = 13 := by
    simpa using natCard_quotient_lambdaThirteenIdeal_pow 1
  rw [hbase, natCard_quotient_lambdaThirteenIdeal_pow] at hcard
  have hpow : 13 ^ n = 13 ^ (n - 1) * 13 := by
    calc
      13 ^ n = 13 ^ ((n - 1) + 1) := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      _ = 13 ^ (n - 1) * 13 := by rw [pow_add]; norm_num
  rw [hpow] at hcard
  omega

/-- The exact unit-group cardinality modulo a positive power of `λ`. -/
theorem natCard_units_quotient_lambdaThirteenIdeal_pow
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card ((O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ) =
      12 * 13 ^ (n - 1) := by
  have hpartition := natCard_units_add_natCard_nonunits
    (O₁₃ ⧸ lambdaThirteenIdeal ^ n)
  rw [Nat.card_congr (nonunitsEquivLambdaImage n hn),
    natCard_lambdaImage n hn,
    natCard_quotient_lambdaThirteenIdeal_pow] at hpartition
  have hpow : 13 ^ n = 13 ^ (n - 1) * 13 := by
    calc
      13 ^ n = 13 ^ ((n - 1) + 1) := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      _ = 13 ^ (n - 1) * 13 := by rw [pow_add]; norm_num
  rw [hpow] at hpartition
  omega

/-- Consequently, the unit-group cardinality modulo `λ ^ n` is prime to
nineteen for every positive `n`. -/
theorem natCard_units_quotient_lambdaThirteenIdeal_pow_coprime_nineteen
    (n : ℕ) (hn : n ≠ 0) :
    (Nat.card ((O₁₃ ⧸ lambdaThirteenIdeal ^ n)ˣ)).Coprime 19 := by
  rw [natCard_units_quotient_lambdaThirteenIdeal_pow n hn]
  exact Nat.Coprime.mul_left (by norm_num)
    (Nat.Coprime.pow_left (n - 1) (by norm_num))

end

end MazurTorsion.XOneThirteenCyclotomic
