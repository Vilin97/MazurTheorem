/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.Nat.Prime.Int
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.PicardGroup
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ElementaryGlobalSections
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeKummer

/-!
# Kummer units over an integer prime localization

This file begins the arithmetic calculation of the multiplicative finite-flat factor on the
good open.  It classifies units of `ℤ[1/ℓ]` as an integral sign times an integral power of the
inverted prime.  Later quotient and fppf-cohomology consumers use this normal form; no vanishing
of `H¹(G_m)` is asserted here.
-/

noncomputable section

namespace AlgebraicGeometry.CommGroupScheme.MultiplicativeKummer

/-- The distinguished unit of `Localization.Away ℓ` represented by the inverted element `ℓ`. -/
noncomputable def awayGeneratorUnit (ℓ : ℤ) :
    (Localization.Away ℓ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit ℓ).unit

@[simp]
theorem awayGeneratorUnit_val (ℓ : ℤ) :
    (awayGeneratorUnit ℓ : Localization.Away ℓ) =
      algebraMap ℤ (Localization.Away ℓ) ℓ :=
  IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit ℓ)

/-- Map an integral sign into the units of the prime localization. -/
def intUnitMap (ℓ : ℤ) : ℤˣ →* (Localization.Away ℓ)ˣ :=
  Units.map (algebraMap ℤ (Localization.Away ℓ))

/-- Every unit of `ℤ[1/ℓ]`, for prime `ℓ`, is an integral sign times an integral power of the
inverted prime.  The proof uses the localization numerator and the theorem that every divisor of
a prime power is associated to a power of that prime. -/
theorem exists_eq_intUnit_mul_awayGeneratorUnit_zpow
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (u : (Localization.Away (ℓ : ℤ))ˣ) :
    ∃ ε : ℤˣ, ∃ z : ℤ,
      u = intUnitMap (ℓ : ℤ) ε * awayGeneratorUnit (ℓ : ℤ) ^ z := by
  let S := Localization.Away (ℓ : ℤ)
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hu⟩ :=
    IsLocalization.surj (Submonoid.powers (ℓ : ℤ)) (u : S)
  have haUnit : IsUnit (algebraMap ℤ S a) := by
    rw [← hu]
    exact u.isUnit.mul (by
      simpa using
        (IsLocalization.Away.algebraMap_pow_isUnit
          (S := Localization.Away (ℓ : ℤ)) (ℓ : ℤ) m))
  obtain ⟨n, han⟩ :=
    (IsLocalization.Away.algebraMap_isUnit_iff (S := S) (ℓ : ℤ)).mp haUnit
  have hℓInt : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  obtain ⟨i, _hi, hai⟩ := (dvd_prime_pow hℓInt n).mp han
  obtain ⟨ε, hε⟩ := hai
  let A : Sˣ := haUnit.unit
  let P : Sˣ := awayGeneratorUnit (ℓ : ℤ)
  let E : Sˣ := intUnitMap (ℓ : ℤ) ε
  have hu' : u * P ^ m = A := by
    apply Units.ext
    dsimp only [P, A]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, awayGeneratorUnit_val,
      IsUnit.unit_spec, ← map_pow]
    exact hu
  have hai' : A * E = P ^ i := by
    apply Units.ext
    dsimp only [A, E, P, intUnitMap]
    rw [Units.val_mul, IsUnit.unit_spec, Units.coe_map,
      Units.val_pow_eq_pow_val, awayGeneratorUnit_val]
    change algebraMap ℤ S a * algebraMap ℤ S (ε : ℤ) =
      algebraMap ℤ S (ℓ : ℤ) ^ i
    simpa only [← map_mul, ← map_pow] using congrArg (algebraMap ℤ S) hε
  refine ⟨ε⁻¹, (i : ℤ) - (m : ℤ), ?_⟩
  change u = intUnitMap (ℓ : ℤ) ε⁻¹ * P ^ ((i : ℤ) - (m : ℤ))
  calc
    u = A * (P ^ m)⁻¹ := by rw [← hu']; group
    _ = (P ^ i * E⁻¹) * (P ^ m)⁻¹ := by rw [← hai']; group
    _ = intUnitMap (ℓ : ℤ) ε⁻¹ * P ^ ((i : ℤ) - (m : ℤ)) := by
      rw [map_inv, zpow_sub, zpow_natCast, zpow_natCast]
      change (P ^ i * E⁻¹) * (P ^ m)⁻¹ =
        E⁻¹ * (P ^ i * (P ^ m)⁻¹)
      ac_rfl

/-- The class of the inverted prime in units modulo `n`th powers. -/
noncomputable def awayKummerGenerator (ℓ : ℕ) (n : ℕ) :
    FiniteFlatCommGroupScheme.UnitKummerClasses
      (Localization.Away (ℓ : ℤ)) n :=
  QuotientGroup.mk'
    (powMonoidHom n : (Localization.Away (ℓ : ℤ))ˣ →*
      (Localization.Away (ℓ : ℤ))ˣ).range
    (awayGeneratorUnit (ℓ : ℤ))

/-- For odd `n`, the image of every integral sign is trivial modulo `n`th powers. -/
theorem intUnitMap_kummerClass_eq_one
    (ℓ n : ℕ) (hn : Odd n) (ε : ℤˣ) :
    QuotientGroup.mk'
        (powMonoidHom n : (Localization.Away (ℓ : ℤ))ˣ →*
          (Localization.Away (ℓ : ℤ))ˣ).range
        (intUnitMap (ℓ : ℤ) ε) = 1 := by
  apply (QuotientGroup.eq_one_iff (intUnitMap (ℓ : ℤ) ε)).mpr
  apply MonoidHom.mem_range.mpr
  refine ⟨intUnitMap (ℓ : ℤ) ε, ?_⟩
  change (intUnitMap (ℓ : ℤ) ε) ^ n = intUnitMap (ℓ : ℤ) ε
  rw [← map_pow]
  rcases Int.units_eq_one_or ε with hε | hε
  · rw [hε]
    simp
  · rw [hε, hn.neg_one_pow]

/-- Every Kummer unit class over `ℤ[1/ℓ]` is an integral power of the inverted-prime class. -/
theorem exists_eq_awayKummerGenerator_zpow
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hn : Odd n)
    (x : FiniteFlatCommGroupScheme.UnitKummerClasses
      (Localization.Away (ℓ : ℤ)) n) :
    ∃ z : ℤ, x = awayKummerGenerator ℓ n ^ z := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom n : (Localization.Away (ℓ : ℤ))ˣ →*
      (Localization.Away (ℓ : ℤ))ˣ).range x
  obtain ⟨ε, z, hu⟩ :=
    exists_eq_intUnit_mul_awayGeneratorUnit_zpow ℓ hℓ u
  refine ⟨z, ?_⟩
  let qHom : (Localization.Away (ℓ : ℤ))ˣ →*
      FiniteFlatCommGroupScheme.UnitKummerClasses
        (Localization.Away (ℓ : ℤ)) n :=
    QuotientGroup.mk'
      (powMonoidHom n : (Localization.Away (ℓ : ℤ))ˣ →*
        (Localization.Away (ℓ : ℤ))ˣ).range
  change qHom u = awayKummerGenerator ℓ n ^ z
  calc
    qHom u = qHom
        (intUnitMap (ℓ : ℤ) ε * awayGeneratorUnit (ℓ : ℤ) ^ z) :=
      congrArg qHom hu
    _ = qHom (intUnitMap (ℓ : ℤ) ε) *
        qHom (awayGeneratorUnit (ℓ : ℤ) ^ z) := map_mul qHom _ _
    _ = 1 * (qHom (awayGeneratorUnit (ℓ : ℤ))) ^ z := by
      rw [show qHom (intUnitMap (ℓ : ℤ) ε) = 1 by
        exact intUnitMap_kummerClass_eq_one ℓ n hn ε]
      exact congrArg (1 * ·)
        (map_zpow qHom (awayGeneratorUnit (ℓ : ℤ)) z)
    _ = awayKummerGenerator ℓ n ^ z := by
      change 1 * (qHom (awayGeneratorUnit (ℓ : ℤ))) ^ z =
        (qHom (awayGeneratorUnit (ℓ : ℤ))) ^ z
      exact one_mul ((qHom (awayGeneratorUnit (ℓ : ℤ))) ^ z)

/-- The explicit Kummer unit quotient over an integer prime localization is finite for every
positive odd exponent. -/
theorem unitKummerClasses_finite_of_primeAway
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hn : Odd n) :
    Finite (FiniteFlatCommGroupScheme.UnitKummerClasses
      (Localization.Away (ℓ : ℤ)) n) := by
  let g := awayKummerGenerator ℓ n
  have hgen : ∀ x, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨z, hz⟩ := exists_eq_awayKummerGenerator_zpow ℓ n hℓ hn x
    exact Subgroup.mem_zpowers_iff.mpr ⟨z, hz.symm⟩
  have hfiniteOrder : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn.pos,
        FiniteFlatCommGroupScheme.UnitKummerClasses.pow_eq_one n g⟩
  letI : Finite (Subgroup.zpowers g) := hfiniteOrder.finite_zpowers.to_subtype
  exact Finite.of_surjective (fun y : Subgroup.zpowers g ↦ y.1) (by
    intro x
    exact ⟨⟨x, hgen x⟩, rfl⟩)

/-- The prime-localized Kummer unit quotient has at most `n` elements. -/
theorem unitKummerClasses_natCard_le_primeAway
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hn : Odd n) :
    Nat.card (FiniteFlatCommGroupScheme.UnitKummerClasses
      (Localization.Away (ℓ : ℤ)) n) ≤ n := by
  let g := awayKummerGenerator ℓ n
  have hgen : ∀ x, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨z, hz⟩ := exists_eq_awayKummerGenerator_zpow ℓ n hℓ hn x
    exact Subgroup.mem_zpowers_iff.mpr ⟨z, hz.symm⟩
  calc
    Nat.card (FiniteFlatCommGroupScheme.UnitKummerClasses
        (Localization.Away (ℓ : ℤ)) n) = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hgen).symm
    _ ≤ n := Nat.le_of_dvd hn.pos
      (orderOf_dvd_of_pow_eq_one
        (FiniteFlatCommGroupScheme.UnitKummerClasses.pow_eq_one n g))

/-! ## Exact order from the prime valuation -/

private theorem primeIntCast_isUnitRat (ℓ : ℕ) (hℓ : ℓ.Prime) :
    IsUnit ((algebraMap ℤ ℚ) (ℓ : ℤ)) := by
  apply isUnit_iff_ne_zero.mpr
  exact Int.cast_ne_zero.mpr (Int.ofNat_ne_zero.mpr hℓ.ne_zero)

/-- The canonical embedding of `ℤ[1/ℓ]` into `ℚ` for nonzero prime `ℓ`. -/
noncomputable def awayToRat (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Localization.Away (ℓ : ℤ) →+* ℚ :=
  Localization.awayLift (algebraMap ℤ ℚ) (ℓ : ℤ)
    (primeIntCast_isUnitRat ℓ hℓ)

@[simp]
theorem awayToRat_algebraMap (ℓ : ℕ) (hℓ : ℓ.Prime) (a : ℤ) :
    awayToRat ℓ hℓ
        (algebraMap ℤ (Localization.Away (ℓ : ℤ)) a) =
      (a : ℚ) := by
  exact IsLocalization.Away.lift_eq (ℓ : ℤ)
    (primeIntCast_isUnitRat ℓ hℓ) a

private theorem away_nontrivial (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nontrivial (Localization.Away (ℓ : ℤ)) :=
  ⟨⟨0, 1, fun h ↦ by
    have h' := congrArg (awayToRat ℓ hℓ) h
    exact (zero_ne_one : (0 : ℚ) ≠ 1)
      (by simpa only [map_zero, map_one] using h')⟩⟩

/-- The `ℓ`-adic exponent of a unit of `ℤ[1/ℓ]`, as a multiplicative homomorphism to the
multiplicative spelling of the additive group `ℤ`. -/
noncomputable def awayUnitValuation (ℓ : ℕ) (hℓ : ℓ.Prime) :
    (Localization.Away (ℓ : ℤ))ˣ →* Multiplicative ℤ := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  refine
    { toFun := fun u ↦ Multiplicative.ofAdd
        (padicValRat ℓ (awayToRat ℓ hℓ (u : Localization.Away (ℓ : ℤ))))
      map_one' := ?_
      map_mul' := ?_ }
  · change padicValRat ℓ (awayToRat ℓ hℓ 1) = 0
    rw [map_one, padicValRat.one]
  · intro u v
    change padicValRat ℓ (awayToRat ℓ hℓ ((u * v :
        (Localization.Away (ℓ : ℤ))ˣ) : Localization.Away (ℓ : ℤ))) =
      padicValRat ℓ (awayToRat ℓ hℓ (u : Localization.Away (ℓ : ℤ))) +
        padicValRat ℓ (awayToRat ℓ hℓ (v : Localization.Away (ℓ : ℤ)))
    rw [Units.val_mul, map_mul, padicValRat.mul]
    · exact (IsUnit.map (awayToRat ℓ hℓ) u.isUnit).ne_zero
    · exact (IsUnit.map (awayToRat ℓ hℓ) v.isUnit).ne_zero

/-- The distinguished inverted-prime unit has valuation one. -/
@[simp]
theorem awayUnitValuation_awayGeneratorUnit (ℓ : ℕ) (hℓ : ℓ.Prime) :
    awayUnitValuation ℓ hℓ (awayGeneratorUnit (ℓ : ℤ)) =
      Multiplicative.ofAdd 1 := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  change padicValRat ℓ
      (awayToRat ℓ hℓ
        (awayGeneratorUnit (ℓ : ℤ) : Localization.Away (ℓ : ℤ))) = 1
  rw [awayGeneratorUnit_val, awayToRat_algebraMap,
    padicValRat.of_int, padicValInt.self hℓ.one_lt]
  norm_num

/-- Integral signs have valuation zero in the prime localization. -/
@[simp]
theorem awayUnitValuation_intUnitMap
    (ℓ : ℕ) (hℓ : ℓ.Prime) (ε : ℤˣ) :
    awayUnitValuation ℓ hℓ (intUnitMap (ℓ : ℤ) ε) =
      Multiplicative.ofAdd 0 := by
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  rcases Int.units_eq_one_or ε with hε | hε
  · subst ε
    simp only [map_one]
    rfl
  · rw [hε]
    change padicValRat ℓ
      (awayToRat ℓ hℓ
        ((intUnitMap (ℓ : ℤ)) (-1) : Localization.Away (ℓ : ℤ))) = 0
    rw [show ((intUnitMap (ℓ : ℤ)) (-1) : Localization.Away (ℓ : ℤ)) =
        algebraMap ℤ (Localization.Away (ℓ : ℤ)) (-1 : ℤ) by rfl,
      awayToRat_algebraMap]
    change padicValRat ℓ (-1 : ℚ) = 0
    rw [padicValRat.neg, padicValRat.one]

/-- The class of the inverted prime is nontrivial modulo `n`th powers as soon as `n > 1`.
Indeed, an `n`th-power representative would have valuation divisible by `n`, whereas the
distinguished generator has valuation one. -/
theorem awayKummerGenerator_ne_one
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hn : 1 < n) :
    awayKummerGenerator ℓ n ≠ 1 := by
  intro hgen
  have hrange : awayGeneratorUnit (ℓ : ℤ) ∈
      (powMonoidHom n : (Localization.Away (ℓ : ℤ))ˣ →*
        (Localization.Away (ℓ : ℤ))ˣ).range :=
    (QuotientGroup.eq_one_iff (awayGeneratorUnit (ℓ : ℤ))).mp hgen
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hrange
  have hval := congrArg (awayUnitValuation ℓ hℓ) hu
  have hmultiple : n • (awayUnitValuation ℓ hℓ u).toAdd = 1 := by
    simpa only [powMonoidHom_apply, map_pow, toAdd_pow, toAdd_ofAdd,
      awayUnitValuation_awayGeneratorUnit] using congrArg Multiplicative.toAdd hval
  have hdvd : (n : ℤ) ∣ 1 := by
    refine ⟨(awayUnitValuation ℓ hℓ u).toAdd, ?_⟩
    simpa only [nsmul_eq_mul] using hmultiple.symm
  have hnDvdOne : n ∣ 1 := by exact_mod_cast hdvd
  exact (Nat.not_dvd_of_pos_of_lt Nat.zero_lt_one hn) hnDvdOne

/-- For a prime exponent, the inverted-prime Kummer class has exact order that prime. -/
theorem orderOf_awayKummerGenerator
    (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) :
    orderOf (awayKummerGenerator ℓ p) = p := by
  have horderDvd : orderOf (awayKummerGenerator ℓ p) ∣ p :=
    orderOf_dvd_of_pow_eq_one
      (FiniteFlatCommGroupScheme.UnitKummerClasses.pow_eq_one p
        (awayKummerGenerator ℓ p))
  rcases (Nat.dvd_prime hp).mp horderDvd with horder | horder
  · exact False.elim (awayKummerGenerator_ne_one ℓ p hℓ hp.one_lt
      (orderOf_eq_one_iff.mp horder))
  · exact horder

/-- The unit Kummer quotient over `ℤ[1/ℓ]` has exactly `p` elements for odd prime `p`. -/
theorem unitKummerClasses_natCard_primeAway
    (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) (hpOdd : Odd p) :
    Nat.card (FiniteFlatCommGroupScheme.UnitKummerClasses
      (Localization.Away (ℓ : ℤ)) p) = p := by
  have hgen : ∀ x : FiniteFlatCommGroupScheme.UnitKummerClasses
      (Localization.Away (ℓ : ℤ)) p,
      x ∈ Subgroup.zpowers (awayKummerGenerator ℓ p) := by
    intro x
    obtain ⟨z, hz⟩ := exists_eq_awayKummerGenerator_zpow ℓ p hℓ hpOdd x
    exact Subgroup.mem_zpowers_iff.mpr ⟨z, hz.symm⟩
  rw [← orderOf_eq_card_of_forall_mem_zpowers hgen,
    orderOf_awayKummerGenerator ℓ p hℓ hp]

/-- The exact arithmetic certificate for units modulo `p`th powers over `ℤ[1/ℓ]`. -/
noncomputable def unitKummerClassesCertifiedDataPrimeAway
    (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) (hpOdd : Odd p) :
    FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (FiniteFlatCommGroupScheme.UnitKummerClasses
        (Localization.Away (ℓ : ℤ)) p) where
  finite := unitKummerClasses_finite_of_primeAway ℓ p hℓ hpOdd
  length := 1
  card_eq := by
    rw [pow_one]
    exact unitKummerClasses_natCard_primeAway ℓ p hℓ hp hpOdd

/-- The actual geometric Kummer kernel over `ℤ[1/ℓ]` has certified `p`-length one.  This is the
downstream consumer of both the arithmetic unit calculation and the checked fppf Kummer
exactness equivalence. -/
noncomputable def unitKummerBoundaryKernelCertifiedDataPrimeAway
    (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) (hpOdd : Odd p) :
    FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (fppfHOneMap
        (powerKernelPresentation (Localization.Away (ℓ : ℤ)) p).inclusion).ker := by
  letI : Nontrivial (Localization.Away (ℓ : ℤ)) := away_nontrivial ℓ hℓ
  exact (unitKummerClassesCertifiedDataPrimeAway ℓ p hℓ hp hpOdd).congr
    (unitKummerBoundaryMulEquivKernel
      (R := Localization.Away (ℓ : ℤ)) p hp.ne_zero)

/-! ## Picard triviality of the prime localization -/

/-- The localization `ℤ[1/ℓ]` at a prime is a principal ideal ring.  This records the arithmetic
input behind vanishing of its ring Picard group without asserting an fppf-cohomology comparison. -/
theorem away_isPrincipalIdealRing (ℓ : ℕ) (hℓ : ℓ.Prime) :
    IsPrincipalIdealRing (Localization.Away (ℓ : ℤ)) := by
  letI : Nontrivial (Localization.Away (ℓ : ℤ)) := away_nontrivial ℓ hℓ
  letI : IsDomain (Localization.Away (ℓ : ℤ)) :=
    NoZeroDivisors.to_isDomain _
  let hM : Submonoid.powers (ℓ : ℤ) ≤ nonZeroDivisors ℤ := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero n (Int.ofNat_ne_zero.mpr hℓ.ne_zero))
  letI : IsDedekindDomain (Localization.Away (ℓ : ℤ)) :=
    IsLocalization.isDedekindDomain ℤ hM _
  exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid _

/-- Every class in the ring Picard group of `ℤ[1/ℓ]` is trivial. -/
theorem awayPic_eq_one (ℓ : ℕ) (hℓ : ℓ.Prime)
    (L : CommRing.Pic (Localization.Away (ℓ : ℤ))) :
    L = 1 := by
  letI : Nontrivial (Localization.Away (ℓ : ℤ)) := away_nontrivial ℓ hℓ
  letI : IsDomain (Localization.Away (ℓ : ℤ)) :=
    NoZeroDivisors.to_isDomain _
  letI : IsPrincipalIdealRing (Localization.Away (ℓ : ℤ)) :=
    away_isPrincipalIdealRing ℓ hℓ
  exact Subsingleton.elim L 1

/-- Every invertible module over `ℤ[1/ℓ]` is explicitly linearly equivalent to the trivial
rank-one module.  This is the downstream consumer of prime-localization Picard triviality needed
by a future comparison from multiplicative fppf cocycles to invertible modules. -/
noncomputable def awayInvertibleModuleLinearEquiv
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (M : Type*) [AddCommGroup M]
    [Module (Localization.Away (ℓ : ℤ)) M]
    [Module.Invertible (Localization.Away (ℓ : ℤ)) M] :
    M ≃ₗ[Localization.Away (ℓ : ℤ)] Localization.Away (ℓ : ℤ) := by
  letI : Nontrivial (Localization.Away (ℓ : ℤ)) := away_nontrivial ℓ hℓ
  letI : IsDomain (Localization.Away (ℓ : ℤ)) :=
    NoZeroDivisors.to_isDomain _
  exact Classical.choice (CommRing.Pic.mk_eq_one_iff.mp
    (awayPic_eq_one ℓ hℓ
      (CommRing.Pic.mk (Localization.Away (ℓ : ℤ)) M)))

end AlgebraicGeometry.CommGroupScheme.MultiplicativeKummer
