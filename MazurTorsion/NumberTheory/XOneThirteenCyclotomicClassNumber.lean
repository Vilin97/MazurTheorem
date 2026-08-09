/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCyclotomicNorms
import MazurTorsion.NumberTheory.XOneThirteenCyclotomicPrimeCutoff
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Class number one for the thirteenth cyclotomic field

This file supplies principal prime ideals for every exceptional rational
prime left by the checked Minkowski cutoff.  The norm-`27` generator is
handled by comparing it with a maximal ideal above `3` and using the exact
inertia degree `ord₁₃(3) = 3`.  The resulting finite ideal-class criterion
proves that the ring of integers of `ℚ(ζ₁₃)` is a principal ideal ring.
-/

namespace MazurTorsion.XOneThirteenCyclotomic

open Algebra Ideal Nat NumberField RingOfIntegers
open scoped Cyclotomic NumberField

noncomputable section

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

local instance : IsCyclotomicExtension {13} ℚ ThirteenCyclotomicField :=
  CyclotomicField.isCyclotomicExtension 13 ℚ

private theorem principal_prime_span_certificate
    {a : 𝓞 ThirteenCyclotomicField} {p : ℕ}
    (hnorm : Algebra.norm ℤ a = p) (hp : p.Prime) :
    let I : Ideal (𝓞 ThirteenCyclotomicField) := Ideal.span {a}
    I.IsPrincipal ∧ I.IsPrime ∧
      I.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm I = p := by
  dsimp only
  have habs : Ideal.absNorm (Ideal.span {a}) = p := by
    rw [Ideal.absNorm_span_singleton, hnorm]
    simp
  have hprime : (Ideal.span {a} : Ideal (𝓞 ThirteenCyclotomicField)).IsPrime := by
    apply Ideal.isPrime_of_irreducible_absNorm
    rw [habs, Nat.irreducible_iff_prime]
    exact hp.prime
  have hcontract := Ideal.span_singleton_absNorm
    (I := (Ideal.span {a} : Ideal (𝓞 ThirteenCyclotomicField))) (by
      simpa [habs] using hp)
  have hlies :
      (Ideal.span {a} : Ideal (𝓞 ThirteenCyclotomicField)).LiesOver
        (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    constructor
    change Ideal.span ({(p : ℤ)} : Set ℤ) =
      Ideal.comap (algebraMap ℤ (𝓞 ThirteenCyclotomicField)) (Ideal.span {a})
    simpa [habs] using hcontract
  exact ⟨inferInstance, hprime, hlies, habs⟩

/-! ## Principal prime ideals of prime norm -/

/-- The principal ideal of norm `79`. -/
noncomputable def seventyNineIdeal : Ideal (𝓞 ThirteenCyclotomicField) :=
  Ideal.span {alphaSeventyNineInteger}

theorem seventyNineIdeal_certificate :
    seventyNineIdeal.IsPrincipal ∧ seventyNineIdeal.IsPrime ∧
      seventyNineIdeal.LiesOver (Ideal.span ({(79 : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm seventyNineIdeal = 79 := by
  unfold seventyNineIdeal
  exact principal_prime_span_certificate norm_alphaSeventyNineInteger (by decide)

theorem seventyNineIdeal_isPrincipal : seventyNineIdeal.IsPrincipal :=
  seventyNineIdeal_certificate.1

theorem seventyNineIdeal_isPrime : seventyNineIdeal.IsPrime :=
  seventyNineIdeal_certificate.2.1

theorem seventyNineIdeal_liesOver :
    seventyNineIdeal.LiesOver (Ideal.span ({(79 : ℤ)} : Set ℤ)) :=
  seventyNineIdeal_certificate.2.2.1

/-- The principal ideal of norm `131`. -/
noncomputable def oneThirtyOneIdeal : Ideal (𝓞 ThirteenCyclotomicField) :=
  Ideal.span {alphaOneThirtyOneInteger}

theorem oneThirtyOneIdeal_certificate :
    oneThirtyOneIdeal.IsPrincipal ∧ oneThirtyOneIdeal.IsPrime ∧
      oneThirtyOneIdeal.LiesOver (Ideal.span ({(131 : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm oneThirtyOneIdeal = 131 := by
  unfold oneThirtyOneIdeal
  exact principal_prime_span_certificate norm_alphaOneThirtyOneInteger (by decide)

theorem oneThirtyOneIdeal_isPrincipal : oneThirtyOneIdeal.IsPrincipal :=
  oneThirtyOneIdeal_certificate.1

theorem oneThirtyOneIdeal_isPrime : oneThirtyOneIdeal.IsPrime :=
  oneThirtyOneIdeal_certificate.2.1

theorem oneThirtyOneIdeal_liesOver :
    oneThirtyOneIdeal.LiesOver (Ideal.span ({(131 : ℤ)} : Set ℤ)) :=
  oneThirtyOneIdeal_certificate.2.2.1

/-- The principal ideal of norm `157`. -/
noncomputable def oneFiftySevenIdeal : Ideal (𝓞 ThirteenCyclotomicField) :=
  Ideal.span {alphaOneFiftySevenInteger}

theorem oneFiftySevenIdeal_certificate :
    oneFiftySevenIdeal.IsPrincipal ∧ oneFiftySevenIdeal.IsPrime ∧
      oneFiftySevenIdeal.LiesOver (Ideal.span ({(157 : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm oneFiftySevenIdeal = 157 := by
  unfold oneFiftySevenIdeal
  exact principal_prime_span_certificate norm_alphaOneFiftySevenInteger (by decide)

theorem oneFiftySevenIdeal_isPrincipal : oneFiftySevenIdeal.IsPrincipal :=
  oneFiftySevenIdeal_certificate.1

theorem oneFiftySevenIdeal_isPrime : oneFiftySevenIdeal.IsPrime :=
  oneFiftySevenIdeal_certificate.2.1

theorem oneFiftySevenIdeal_liesOver :
    oneFiftySevenIdeal.LiesOver (Ideal.span ({(157 : ℤ)} : Set ℤ)) :=
  oneFiftySevenIdeal_certificate.2.2.1

/-! ## The ramified prime above thirteen -/

/-- Mathlib's ramified principal ideal `(ζ - 1)` above `13`. -/
noncomputable def thirteenIdeal : Ideal (𝓞 ThirteenCyclotomicField) :=
  Ideal.span {zetaThirteenInteger - 1}

theorem thirteenIdeal_isPrincipal : thirteenIdeal.IsPrincipal := by
  unfold thirteenIdeal
  infer_instance

theorem thirteenIdeal_isPrime : thirteenIdeal.IsPrime := by
  unfold thirteenIdeal zetaThirteenInteger
  rw [Ideal.span_singleton_prime]
  · exact zetaThirteen_spec.zeta_sub_one_prime'
  · exact zetaThirteen_spec.zeta_sub_one_prime'.ne_zero

theorem thirteenIdeal_absNorm : Ideal.absNorm thirteenIdeal = 13 := by
  unfold thirteenIdeal zetaThirteenInteger
  rw [Ideal.absNorm_span_singleton,
    zetaThirteen_spec.norm_toInteger_sub_one_of_prime_ne_two']
  · norm_num
  · norm_num

theorem thirteenIdeal_liesOver :
    thirteenIdeal.LiesOver (Ideal.span ({(13 : ℤ)} : Set ℤ)) := by
  have hcontract := Ideal.span_singleton_absNorm
    (I := thirteenIdeal) (by
      rw [thirteenIdeal_absNorm]
      decide)
  constructor
  change Ideal.span ({(13 : ℤ)} : Set ℤ) =
    Ideal.comap (algebraMap ℤ (𝓞 ThirteenCyclotomicField)) thirteenIdeal
  simpa [thirteenIdeal_absNorm] using hcontract

theorem thirteenIdeal_certificate :
    thirteenIdeal.IsPrincipal ∧ thirteenIdeal.IsPrime ∧
      thirteenIdeal.LiesOver (Ideal.span ({(13 : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm thirteenIdeal = 13 :=
  ⟨thirteenIdeal_isPrincipal, thirteenIdeal_isPrime,
    thirteenIdeal_liesOver, thirteenIdeal_absNorm⟩

/-! ## The degree-three prime above three -/

/-- The principal ideal generated by `ζ³ - ζ - 1`, of norm `27`. -/
noncomputable def twentySevenIdeal : Ideal (𝓞 ThirteenCyclotomicField) :=
  Ideal.span {alphaTwentySevenInteger}

theorem twentySevenIdeal_isPrincipal : twentySevenIdeal.IsPrincipal := by
  unfold twentySevenIdeal
  infer_instance

theorem twentySevenIdeal_absNorm : Ideal.absNorm twentySevenIdeal = 27 := by
  rw [twentySevenIdeal, Ideal.absNorm_span_singleton,
    norm_alphaTwentySevenInteger]
  norm_num

private theorem orderOf_three_mod_thirteen :
    orderOf (3 : ZMod 13) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · decide
  · intro m hm hm0
    interval_cases m <;> decide

/-- The norm-`27` principal span is itself a prime ideal above `3`. -/
theorem twentySevenIdeal_prime_liesOver :
    twentySevenIdeal.IsPrime ∧
      twentySevenIdeal.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
  have hp : Nat.Prime 3 := by decide
  have hdiv : 3 ∣ Ideal.absNorm twentySevenIdeal := by
    rw [twentySevenIdeal_absNorm]
    norm_num
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp twentySevenIdeal hdiv
  letI : P.IsPrime := hPmax.isPrime
  letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) :=
    ⟨hPunder.symm⟩
  letI : Fact (Nat.Prime 3) := ⟨hp⟩
  letI : NeZero 13 := ⟨by norm_num⟩
  have hinertia : P.inertiaDeg ℤ = 3 := by
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
      (m := 13) 3 ThirteenCyclotomicField P (by norm_num)]
    exact orderOf_three_mod_thirteen
  have hPnorm : Ideal.absNorm P = 27 := by
    simpa [hinertia] using (Ideal.pow_inertiaDeg 3 P).symm
  obtain ⟨J, hJ⟩ := hPdvd
  have hnorm := congrArg Ideal.absNorm hJ
  rw [twentySevenIdeal_absNorm, map_mul, hPnorm] at hnorm
  have hJnorm : Ideal.absNorm J = 1 := by omega
  have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJnorm
  have hEq : twentySevenIdeal = P := by
    simpa [hJtop] using hJ
  constructor
  · rw [hEq]
    exact hPmax.isPrime
  · constructor
    change Ideal.span ({(3 : ℤ)} : Set ℤ) = twentySevenIdeal.under ℤ
    rw [hEq]
    exact hPunder.symm

theorem twentySevenIdeal_isPrime : twentySevenIdeal.IsPrime :=
  twentySevenIdeal_prime_liesOver.1

theorem twentySevenIdeal_liesOver :
    twentySevenIdeal.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) :=
  twentySevenIdeal_prime_liesOver.2

theorem twentySevenIdeal_certificate :
    twentySevenIdeal.IsPrincipal ∧ twentySevenIdeal.IsPrime ∧
      twentySevenIdeal.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm twentySevenIdeal = 27 :=
  ⟨twentySevenIdeal_isPrincipal, twentySevenIdeal_isPrime,
    twentySevenIdeal_liesOver, twentySevenIdeal_absNorm⟩

/-! ## Minkowski consumer -/

/-- The ring of integers of the thirteenth cyclotomic field is a principal
ideal ring. -/
theorem thirteenCyclotomic_isPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 ThirteenCyclotomicField) := by
  letI : IsGalois ℚ ThirteenCyclotomicField :=
    IsCyclotomicExtension.isGalois {13} ℚ ThirteenCyclotomicField
  apply isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  intro p hpIcc hp
  by_cases hexceptional : p ∈ exceptionalPrimes
  · simp only [exceptionalPrimes, Finset.mem_insert,
      Finset.mem_singleton] at hexceptional
    rcases hexceptional with h | h | h | h | h | h
    · subst p
      exact ⟨twentySevenIdeal,
        ⟨twentySevenIdeal_isPrime, twentySevenIdeal_liesOver⟩,
        Or.inr twentySevenIdeal_isPrincipal⟩
    · subst p
      exact ⟨thirteenIdeal,
        ⟨thirteenIdeal_isPrime, thirteenIdeal_liesOver⟩,
        Or.inr thirteenIdeal_isPrincipal⟩
    · subst p
      exact ⟨fiftyThreeIdeal,
        ⟨fiftyThreeIdeal_isPrime, fiftyThreeIdeal_liesOver⟩,
        Or.inr fiftyThreeIdeal_isPrincipal⟩
    · subst p
      exact ⟨seventyNineIdeal,
        ⟨seventyNineIdeal_isPrime, seventyNineIdeal_liesOver⟩,
        Or.inr seventyNineIdeal_isPrincipal⟩
    · subst p
      exact ⟨oneThirtyOneIdeal,
        ⟨oneThirtyOneIdeal_isPrime, oneThirtyOneIdeal_liesOver⟩,
        Or.inr oneThirtyOneIdeal_isPrincipal⟩
    · subst p
      exact ⟨oneFiftySevenIdeal,
        ⟨oneFiftySevenIdeal_isPrime, oneFiftySevenIdeal_liesOver⟩,
        Or.inr oneFiftySevenIdeal_isPrincipal⟩
  · have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
      (Ideal.span_singleton_prime hpInt.ne_zero).2 hpInt
    obtain ⟨P⟩ :=
      (inferInstance : Nonempty
        (primesOver (Ideal.span ({(p : ℤ)} : Set ℤ))
          (𝓞 ThirteenCyclotomicField)))
    refine ⟨P.1, P.2, Or.inl ?_⟩
    have hp_le := (Finset.mem_Icc.mp hpIcc).2
    change p ≤ ⌊minkowskiClassBound ThirteenCyclotomicField⌋₊ at hp_le
    change ⌊minkowskiClassBound ThirteenCyclotomicField⌋₊ <
      p ^ P.1.inertiaDeg ℤ
    exact floor_minkowskiClassBound_lt_pow_inertiaDeg
      p hp hp_le hexceptional P.1 P.2

/-- The thirteenth cyclotomic field has class number one. -/
theorem thirteenCyclotomic_classNumber :
    NumberField.classNumber ThirteenCyclotomicField = 1 :=
  NumberField.classNumber_eq_one_iff.mpr
    thirteenCyclotomic_isPrincipalIdealRing

end

end MazurTorsion.XOneThirteenCyclotomic
