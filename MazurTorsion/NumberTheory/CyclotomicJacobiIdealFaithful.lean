/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicJacobiSumTwo
import MazurTorsion.NumberTheory.CyclotomicStickelbergerTwoResidue

/-!
# The faithful-orbit factorization of the second Jacobi sum

For a finite prime with faithful cyclotomic Galois orbit, this file proves
the exact ideal factorization of the conjugate diagonal Jacobi sum.  The
orientation is forced by the convention that the canonical residue character
reduces to the positive power `x ^ ((Nv - 1) / p)`: the raw Jacobi sum is
supported on the lower half, so its complex conjugate is supported on the
upper half selected by `stickelbergerTwoCoefficient`.

The proof uses only finite-field binomial-sum vanishing, faithfulness of the
prime orbit, and the checked identity `J * conj J = Nv`.  No reciprocity law
or assumed Jacobi factorization is used.
-/

open Algebra
open scoped BigOperators NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

variable {p : ℕ} [Fact p.Prime]

local notation "K" => PrimeCyclotomicField p
local notation "OK" => NumberField.RingOfIntegers K
local notation "FI" => FractionalIdeal (nonZeroDivisors OK) K

private noncomputable def faithfulJacobiOrbitIdeal
    (v : FinitePrime K) : Ideal OK :=
  ∏ a : (ZMod p)ˣ,
    (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v).asIdeal ^
      stickelbergerTwoCoefficient p a

private def unitsEquivPositiveResidues :
    (ZMod p)ˣ ≃ {n : ℕ // n ∈ Finset.Icc 1 (p - 1)} where
  toFun a := ⟨(a : ZMod p).val, by
    rw [Finset.mem_Icc]
    constructor
    · exact ZMod.val_pos.mpr (Units.ne_zero a)
    · have := ZMod.val_lt (a : ZMod p)
      omega⟩
  invFun n :=
    ZMod.unitOfCoprime n.1 <|
      Nat.Coprime.symm <| (Fact.out : p.Prime).coprime_iff_not_dvd.mpr <| by
        intro hpn
        have hn := Finset.mem_Icc.mp n.2
        have hp_le_n := Nat.le_of_dvd (by omega) hpn
        omega
  left_inv a := by
    apply Units.ext
    exact ZMod.natCast_zmod_val (a : ZMod p)
  right_inv n := by
    apply Subtype.ext
    apply ZMod.val_natCast_of_lt
    have hn := Finset.mem_Icc.mp n.2
    omega

private theorem sum_stickelbergerTwoCoefficient (hp5 : 5 ≤ p) :
    ∑ a : (ZMod p)ˣ, stickelbergerTwoCoefficient p a = p / 2 := by
  classical
  have hp_ne_two : p ≠ 2 := by omega
  have hp_odd : p % 2 = 1 :=
    ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp_ne_two
  let e := unitsEquivPositiveResidues (p := p)
  calc
    ∑ a : (ZMod p)ˣ, stickelbergerTwoCoefficient p a =
        ∑ n : {n : ℕ // n ∈ Finset.Icc 1 (p - 1)},
          if p ≤ 2 * n.1 then 1 else 0 := by
      apply Fintype.sum_equiv e
      intro a
      change stickelbergerTwoCoefficient p a =
        if p ≤ 2 * (a : ZMod p).val then 1 else 0
      exact stickelbergerTwoCoefficient_eq_ite (p := p) a
    _ = ∑ n ∈ Finset.Icc 1 (p - 1), if p ≤ 2 * n then 1 else 0 := by
      exact Finset.sum_attach (Finset.Icc 1 (p - 1))
        (fun n : ℕ ↦ if p ≤ 2 * n then 1 else 0)
    _ = (Finset.Icc (p / 2 + 1) (p - 1)).card := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.Icc 1 (p - 1)).filter (fun n ↦ p ≤ 2 * n) =
            Finset.Icc (p / 2 + 1) (p - 1) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilter]
      simp
    _ = p / 2 := by
      rw [Nat.card_Icc]
      omega

private noncomputable def residueQuotientEquiv
    (sigma : Gal(K/ℚ)) (v : FinitePrime K) :
    (OK ⧸ v.asIdeal) ≃+* (OK ⧸ (mapFinitePrime sigma v).asIdeal) :=
  Ideal.quotientEquiv v.asIdeal (mapFinitePrime sigma v).asIdeal
    (baseIntegerEquiv sigma) (mapFinitePrime_asIdeal sigma v)

omit [Fact p.Prime] in
private theorem absNorm_mapFinitePrime
    (sigma : Gal(K/ℚ)) (v : FinitePrime K) :
    Ideal.absNorm (mapFinitePrime sigma v).asIdeal =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (residueQuotientEquiv sigma v).symm.toEquiv

private noncomputable def idealQuotientEquiv
    (e : OK ≃+* OK) (I : Ideal OK) :
    (OK ⧸ I) ≃+* (OK ⧸ Ideal.map e I) :=
  Ideal.quotientEquiv I (Ideal.map e I) e rfl

omit [Fact p.Prime] in
private theorem absNorm_map_ringEquiv (e : OK ≃+* OK) (I : Ideal OK) :
    Ideal.absNorm (Ideal.map e I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (idealQuotientEquiv e I).symm.toEquiv

private theorem absNorm_faithfulJacobiOrbitIdeal
    (hp5 : 5 ≤ p) (v : FinitePrime K) :
    Ideal.absNorm (faithfulJacobiOrbitIdeal v) =
      (Ideal.absNorm v.asIdeal) ^ (p / 2) := by
  classical
  simp only [faithfulJacobiOrbitIdeal, map_prod, map_pow,
    absNorm_mapFinitePrime]
  calc
    ∏ a : (ZMod p)ˣ,
        Ideal.absNorm v.asIdeal ^ stickelbergerTwoCoefficient p a =
        Ideal.absNorm v.asIdeal ^
          (∑ a : (ZMod p)ˣ, stickelbergerTwoCoefficient p a) := by
      exact Finset.prod_pow_eq_pow_sum Finset.univ _ _
    _ = Ideal.absNorm v.asIdeal ^ (p / 2) := by
      rw [sum_stickelbergerTwoCoefficient hp5]

private theorem quotientMap_cyclotomicPowerResidueChar_pow_apply
    (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (n : ℕ) (hn : 0 < n)
    (hd : 0 < (Ideal.absNorm v.asIdeal - 1) / p)
    (x : OK ⧸ v.asIdeal) :
    Ideal.Quotient.mk v.asIdeal
        ((cyclotomicPowerResidueChar v hpv ^ n) x) =
      x ^ (n * ((Ideal.absNorm v.asIdeal - 1) / p)) := by
  classical
  letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Field (OK ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let d := (Ideal.absNorm v.asIdeal - 1) / p
  by_cases hx : x = 0
  · subst x
    rw [MulChar.pow_apply' _ hn.ne', MulChar.map_zero, zero_pow hn.ne', map_zero,
      zero_pow (Nat.mul_pos hn hd).ne']
  · let xu : (OK ⧸ v.asIdeal)ˣ := Units.mk0 x hx
    have hbase : Ideal.Quotient.mk v.asIdeal
        (cyclotomicPowerResidueChar v hpv x) = x ^ d := by
      simpa only [xu, Units.val_mk0, d] using
        quotientMap_cyclotomicPowerResidueChar_apply_unit v hpv xu
    rw [MulChar.pow_apply' _ hn.ne']
    change Ideal.Quotient.mk v.asIdeal
        ((cyclotomicPowerResidueChar v hpv x) ^ n) = x ^ (n * d)
    rw [map_pow, hbase]
    simp only [← pow_mul, mul_comm]

private theorem quotientMap_jacobiSum_character_pow
    (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (n : ℕ) (hn : 0 < n)
    (hd : 0 < (Ideal.absNorm v.asIdeal - 1) / p) :
    letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
    Ideal.Quotient.mk v.asIdeal
        (jacobiSum (cyclotomicPowerResidueChar v hpv ^ n)
          (cyclotomicPowerResidueChar v hpv ^ n)) =
      ∑ x : OK ⧸ v.asIdeal,
        x ^ (n * ((Ideal.absNorm v.asIdeal - 1) / p)) *
          (1 - x) ^ (n * ((Ideal.absNorm v.asIdeal - 1) / p)) := by
  letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
  simp only [jacobiSum, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [quotientMap_cyclotomicPowerResidueChar_pow_apply v hpv n hn hd x,
    quotientMap_cyclotomicPowerResidueChar_pow_apply v hpv n hn hd (1 - x)]

private theorem jacobiSum_character_pow_mem_of_lowerHalf
    (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (a : (ZMod p)ˣ) (ha : 2 * (a : ZMod p).val < p) :
    letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
    jacobiSum
        (cyclotomicPowerResidueChar v hpv ^ (a : ZMod p).val)
        (cyclotomicPowerResidueChar v hpv ^ (a : ZMod p).val) ∈
      v.asIdeal := by
  letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Field (OK ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let n := (a : ZMod p).val
  let d := (Ideal.absNorm v.asIdeal - 1) / p
  have hn : 0 < n := ZMod.val_pos.mpr (Units.ne_zero a)
  have hdiv : p ∣ Ideal.absNorm v.asIdeal - 1 :=
    prime_dvd_absNorm_sub_one v hpv
  have hnorm_sub_pos : 0 < Ideal.absNorm v.asIdeal - 1 := by
    have hnorm : 1 < Ideal.absNorm v.asIdeal := by
      simpa only [← Nat.card_eq_fintype_card, residueField_card_eq_absNorm] using
        (Fintype.one_lt_card : 1 < Fintype.card (OK ⧸ v.asIdeal))
    omega
  have hd : 0 < d :=
    Nat.div_pos (Nat.le_of_dvd hnorm_sub_pos hdiv) (Fact.out : p.Prime).pos
  have hpd : p * d = Ideal.absNorm v.asIdeal - 1 :=
    Nat.mul_div_cancel' hdiv
  have hdegree : 2 * (n * d) < Ideal.absNorm v.asIdeal - 1 := by
    rw [← hpd]
    simpa only [n, mul_assoc] using Nat.mul_lt_mul_of_pos_right ha hd
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    quotientMap_jacobiSum_character_pow v hpv n hn hd]
  apply sum_pow_mul_one_sub_pow_eq_zero
  simpa only [← Nat.card_eq_fintype_card, residueField_card_eq_absNorm] using hdegree

omit [Fact p.Prime] in
private theorem baseIntegerEquiv_mul_apply
    (sigma tau : Gal(K/ℚ)) (x : OK) :
    baseIntegerEquiv (sigma * tau) x =
      baseIntegerEquiv sigma (baseIntegerEquiv tau x) := by
  apply NumberField.RingOfIntegers.ext
  rfl

private theorem galoisOfDirectCharacter_mul
    (a b : (ZMod p)ˣ) :
    galoisOfDirectCharacter (a * b) =
      galoisOfDirectCharacter a * galoisOfDirectCharacter b := by
  apply (directCharacterEquiv p).injective
  simp only [map_mul, directCharacterEquiv_apply,
    directCharacter_galoisOfDirectCharacter]

private theorem baseIntegerEquiv_galois_neg_one_jacobiSumTwo
    (hp : 2 < p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal) :
    letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
    baseIntegerEquiv (galoisOfDirectCharacter (-1 : (ZMod p)ˣ))
        (cyclotomicJacobiSumTwo v hpv) =
      cyclotomicIntegerComplexConj p hp (cyclotomicJacobiSumTwo v hpv) := by
  letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
  let chi := cyclotomicPowerResidueChar v hpv
  have hval : (((-1 : (ZMod p)ˣ) : ZMod p).val) = p - 1 := by
    letI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    change (-1 : ZMod p).val = p - 1
    rw [ZMod.val_neg_of_ne_zero, ZMod.val_one]
  have hpow : chi ^ (p - 1) = chi⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    have horder := pow_orderOf_eq_one chi
    rwa [orderOf_cyclotomicPowerResidueChar v hpv] at horder
  rw [cyclotomicJacobiSumTwo_galois,
    directCharacter_galoisOfDirectCharacter,
    cyclotomicJacobiSumTwo_complexConj hp, hval]
  change jacobiSum (chi ^ (p - 1)) (chi ^ (p - 1)) =
    jacobiSum chi⁻¹ chi⁻¹
  rw [hpow]

private theorem cyclotomicJacobiSumTwo_complexConj_mem_upperHalfPrime
    (hp5 : 5 ≤ p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (a : (ZMod p)ˣ) (ha : p ≤ 2 * (a : ZMod p).val) :
    cyclotomicIntegerComplexConj p (by omega)
        (cyclotomicJacobiSumTwo v hpv) ∈
      (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v).asIdeal := by
  classical
  letI : Fintype (OK ⧸ v.asIdeal) := Fintype.ofFinite _
  let b : (ZMod p)ˣ := -a
  have hbval : (b : ZMod p).val = p - (a : ZMod p).val := by
    letI : NeZero (a : ZMod p) := ⟨Units.ne_zero a⟩
    exact ZMod.val_neg_of_ne_zero (a : ZMod p)
  have hbLower : 2 * (b : ZMod p).val < p := by
    have hp_ne_two : p ≠ 2 := by omega
    have hp_odd : p % 2 = 1 :=
      ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp_ne_two
    have haval_lt : (a : ZMod p).val < p := ZMod.val_lt _
    rw [hbval]
    omega
  have hbmem : baseIntegerEquiv (galoisOfDirectCharacter b)
      (cyclotomicJacobiSumTwo v hpv) ∈ v.asIdeal := by
    rw [cyclotomicJacobiSumTwo_galois,
      directCharacter_galoisOfDirectCharacter]
    exact jacobiSum_character_pow_mem_of_lowerHalf v hpv b hbLower
  have hab : a⁻¹ * b = (-1 : (ZMod p)ˣ) := by
    change a⁻¹ * (-a) = (-1 : (ZMod p)ˣ)
    simp
  have htransport :
      baseIntegerEquiv (galoisOfDirectCharacter a⁻¹)
          (baseIntegerEquiv (galoisOfDirectCharacter b)
            (cyclotomicJacobiSumTwo v hpv)) =
        cyclotomicIntegerComplexConj p (by omega)
          (cyclotomicJacobiSumTwo v hpv) := by
    rw [← baseIntegerEquiv_mul_apply,
      ← galoisOfDirectCharacter_mul, hab,
      baseIntegerEquiv_galois_neg_one_jacobiSumTwo (by omega) v hpv]
  have hmapped := (baseIntegerEquiv_mem_mapFinitePrime_iff
    (galoisOfDirectCharacter a⁻¹) v
    (baseIntegerEquiv (galoisOfDirectCharacter b)
      (cyclotomicJacobiSumTwo v hpv))).mpr hbmem
  rwa [htransport] at hmapped

private theorem faithfulJacobiOrbitIdeal_eq_iInf
    (v : FinitePrime K)
    (horbit : Function.Injective
      (fun a : (ZMod p)ˣ ↦ mapFinitePrime (galoisOfDirectCharacter a) v)) :
    faithfulJacobiOrbitIdeal v =
      ⨅ a : (ZMod p)ˣ,
        (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v).asIdeal ^
          stickelbergerTwoCoefficient p a := by
  classical
  let f := fun a : (ZMod p)ˣ ↦
    mapFinitePrime (galoisOfDirectCharacter a⁻¹) v
  have hf : Function.Injective f := by
    intro a b hab
    exact inv_injective (horbit hab)
  have hpair : (↑(Finset.univ : Finset ((ZMod p)ˣ)) : Set ((ZMod p)ˣ)).Pairwise
      (Function.onFun IsCoprime fun a : (ZMod p)ˣ ↦
        (f a).asIdeal ^ stickelbergerTwoCoefficient p a) := by
    intro a _ b _ hab
    exact IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne
      (f a) (f b) (hf.ne hab) _ _
  unfold faithfulJacobiOrbitIdeal
  simpa only [Finset.mem_univ, iInf_true] using
    (Ideal.prod_eq_iInf_of_pairwise_isCoprime hpair)

private theorem span_complexConj_le_faithfulJacobiOrbitIdeal
    (hp5 : 5 ≤ p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (horbit : Function.Injective
      (fun a : (ZMod p)ˣ ↦ mapFinitePrime (galoisOfDirectCharacter a) v)) :
    Ideal.span {
      cyclotomicIntegerComplexConj p (by omega)
        (cyclotomicJacobiSumTwo v hpv)} ≤ faithfulJacobiOrbitIdeal v := by
  classical
  rw [faithfulJacobiOrbitIdeal_eq_iInf v horbit]
  refine le_iInf fun a ↦ ?_
  rw [Ideal.span_singleton_le_iff_mem,
    stickelbergerTwoCoefficient_eq_ite]
  split_ifs with ha
  · simpa using
      cyclotomicJacobiSumTwo_complexConj_mem_upperHalfPrime hp5 v hpv a ha
  · simp

private theorem absNorm_span_cyclotomicJacobiSumTwo_complexConj
    (hp5 : 5 ≤ p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal) :
    Ideal.absNorm (Ideal.span {
      cyclotomicIntegerComplexConj p (by omega)
        (cyclotomicJacobiSumTwo v hpv)}) =
      Ideal.absNorm v.asIdeal ^ (p / 2) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ K :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let J := cyclotomicJacobiSumTwo v hpv
  let C := cyclotomicIntegerComplexConj p (by omega) J
  have hmap : Ideal.map (cyclotomicIntegerComplexConj p (by omega))
      (Ideal.span {J}) = Ideal.span {C} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hnorm_eq : Ideal.absNorm (Ideal.span {J}) =
      Ideal.absNorm (Ideal.span {C}) := by
    rw [← hmap]
    exact (absNorm_map_ringEquiv
      (cyclotomicIntegerComplexConj p (by omega)) (Ideal.span {J})).symm
  have hmul : Ideal.span {J} * Ideal.span {C} =
      Ideal.span {(Ideal.absNorm v.asIdeal : OK)} := by
    rw [Ideal.span_singleton_mul_span_singleton]
    exact congrArg Ideal.span (congrArg singleton
      (cyclotomicJacobiSumTwo_mul_complexConj (by omega) v hpv))
  have hrank : Module.finrank ℤ OK = p - 1 := by
    rw [NumberField.RingOfIntegers.rank,
      IsCyclotomicExtension.Rat.finrank p K,
      Nat.totient_prime (Fact.out : p.Prime)]
  have hnorm_mul := congrArg Ideal.absNorm hmul
  rw [map_mul, Ideal.absNorm_span_natCast, hrank, hnorm_eq] at hnorm_mul
  have hp_ne_two : p ≠ 2 := by omega
  have hp_odd : p % 2 = 1 :=
    ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp_ne_two
  apply Nat.pow_left_injective (n := 2) (by omega)
  calc
    Ideal.absNorm (Ideal.span {C}) ^ 2 =
        Ideal.absNorm v.asIdeal ^ (p - 1) := by
      simpa only [pow_two] using hnorm_mul
    _ = (Ideal.absNorm v.asIdeal ^ (p / 2)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega

private theorem span_cyclotomicJacobiSumTwo_complexConj_eq_faithfulJacobiOrbitIdeal
    (hp5 : 5 ≤ p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (horbit : Function.Injective
      (fun a : (ZMod p)ˣ ↦ mapFinitePrime (galoisOfDirectCharacter a) v)) :
    Ideal.span {
      cyclotomicIntegerComplexConj p (by omega)
        (cyclotomicJacobiSumTwo v hpv)} =
      faithfulJacobiOrbitIdeal v := by
  let C := cyclotomicIntegerComplexConj p (by omega)
    (cyclotomicJacobiSumTwo v hpv)
  have hle : Ideal.span {C} ≤ faithfulJacobiOrbitIdeal v :=
    span_complexConj_le_faithfulJacobiOrbitIdeal hp5 v hpv horbit
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.mpr hle
  have hnormC : Ideal.absNorm (Ideal.span {C}) =
      Ideal.absNorm v.asIdeal ^ (p / 2) :=
    absNorm_span_cyclotomicJacobiSumTwo_complexConj hp5 v hpv
  have hnormU : Ideal.absNorm (faithfulJacobiOrbitIdeal v) =
      Ideal.absNorm v.asIdeal ^ (p / 2) :=
    absNorm_faithfulJacobiOrbitIdeal hp5 v
  have hnormD : Ideal.absNorm D = 1 := by
    have hnorm := congrArg Ideal.absNorm hD
    rw [map_mul, hnormC, hnormU] at hnorm
    exact Nat.eq_of_mul_eq_mul_left
      (pow_pos (Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)) _)
      (by simpa using hnorm.symm)
  calc
    Ideal.span {C} = faithfulJacobiOrbitIdeal v * D := hD
    _ = faithfulJacobiOrbitIdeal v * ⊤ := by
      rw [(Ideal.absNorm_eq_one_iff.mp hnormD)]
    _ = faithfulJacobiOrbitIdeal v := by simp

/-- Exact integral-ideal factorization of the conjugate second Jacobi sum
at a finite prime with faithful cyclotomic Galois orbit. -/
theorem span_cyclotomicJacobiSumTwo_complexConj_eq_orbitProduct
    (hp5 : 5 ≤ p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (horbit : Function.Injective
      (fun a : (ZMod p)ˣ ↦ mapFinitePrime (galoisOfDirectCharacter a) v)) :
    Ideal.span {
      cyclotomicIntegerComplexConj p (by omega)
        (cyclotomicJacobiSumTwo v hpv)} =
      ∏ a : (ZMod p)ˣ,
        (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v).asIdeal ^
          stickelbergerTwoCoefficient p a := by
  exact span_cyclotomicJacobiSumTwo_complexConj_eq_faithfulJacobiOrbitIdeal
    hp5 v hpv horbit

private theorem cyclotomicJacobiSumTwo_complexConj_ne_zero
    (hp : 2 < p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal) :
    cyclotomicIntegerComplexConj p hp (cyclotomicJacobiSumTwo v hpv) ≠ 0 :=
  by
    simpa only [map_zero] using
      (cyclotomicIntegerComplexConj p hp).injective.ne
        (cyclotomicJacobiSumTwo_ne_zero hp v hpv)

/-- Fractional-ideal form of the faithful-orbit Jacobi factorization.  The
principal fractional ideal of the conjugate Jacobi sum is exactly the
corrected Stickelberger-two prime product. -/
theorem toPrincipalIdeal_cyclotomicJacobiSumTwo_complexConj_eq_stickelbergerTwoPrimeIdeal
    (hp5 : 5 ≤ p) (v : FinitePrime K) (hpv : (p : OK) ∉ v.asIdeal)
    (horbit : Function.Injective
      (fun a : (ZMod p)ˣ ↦ mapFinitePrime (galoisOfDirectCharacter a) v)) :
    toPrincipalIdeal OK K
        (Units.mk0
          (algebraMap OK K
            (cyclotomicIntegerComplexConj p (by omega)
              (cyclotomicJacobiSumTwo v hpv)))
          ((IsFractionRing.injective OK K).ne
            (cyclotomicJacobiSumTwo_complexConj_ne_zero (by omega) v hpv))) =
      stickelbergerTwoPrimeIdeal v := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton (nonZeroDivisors OK)
      (algebraMap OK K
        (cyclotomicIntegerComplexConj p (by omega)
          (cyclotomicJacobiSumTwo v hpv))) = _
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    span_cyclotomicJacobiSumTwo_complexConj_eq_orbitProduct hp5 v hpv horbit]
  unfold stickelbergerTwoPrimeIdeal
  rw [Units.coe_prod]
  simp only [Units.val_pow_eq_pow_val,
    NumberTheory.UnramifiedArtin.primeFractionalIdealUnit,
    Units.val_mk0]
  simpa only [FractionalIdeal.coeIdealHom_apply,
    FractionalIdeal.coeIdeal_pow] using
    (map_prod (FractionalIdeal.coeIdealHom (nonZeroDivisors OK) K)
      (fun a : (ZMod p)ˣ ↦
        (mapFinitePrime (galoisOfDirectCharacter a⁻¹) v).asIdeal ^
          stickelbergerTwoCoefficient p a) Finset.univ)

end NumberTheory.CyclotomicCharacter.InverseExtension
