/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Xavier Roblot
-/

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Multiset.Sum
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-!
# A weak nonsplitting theorem for number fields

This file proves the global fact needed by the inverse-cyclotomic argument:
a nontrivial finite Galois extension of number fields has a finite prime that
does not split completely.

The proof uses only the pinned Mathlib. Two hypothetical prime lifts above
every base prime give a norm-multiplying injection from pairs of nonzero
ideals into nonzero ideals of the extension. Regrouping the Dedekind zeta
series by ideals then forces the zeta function of the extension to dominate
the square of the base zeta function, contradicting the simple poles supplied
by the class-number formula.

The conceptual route was identified during the prior-art audit of
DE0CH/flt-lean recorded in `docs/PRIOR_ART.md`; no source text is copied from
that unlicensed repository. The finite-fibre counting identity below is
adapted from the Apache-2.0 Mathlib proof of
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, authored by Xavier
Roblot.
-/

open scoped NumberField nonZeroDivisors Real
open Filter Topology
open IsDedekindDomain

namespace NumberTheory.WeakChebotarev

noncomputable section

/-! ## Unique-factorization encoding of pairs of ideals -/

section FactorEncoding

variable (R : Type*) [CommRing R] [IsDedekindDomain R]

/-- The normalized prime factors of an ideal, regarded as finite primes. -/
def spectrumFactors (I : Ideal R) : Multiset (HeightOneSpectrum R) :=
  (UniqueFactorizationMonoid.normalizedFactors I).attach.map fun P =>
    ⟨P.1,
      Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor P.1 P.2),
      (UniqueFactorizationMonoid.prime_of_normalized_factor P.1 P.2).ne_zero⟩

lemma spectrumFactors_map_asIdeal (I : Ideal R) :
    (spectrumFactors R I).map HeightOneSpectrum.asIdeal =
      UniqueFactorizationMonoid.normalizedFactors I := by
  simp [spectrumFactors]

lemma spectrumFactors_prod_asIdeal {I : Ideal R} (hI : I ≠ 0) :
    ((spectrumFactors R I).map HeightOneSpectrum.asIdeal).prod = I := by
  rw [spectrumFactors_map_asIdeal]
  simpa using UniqueFactorizationMonoid.prod_normalizedFactors_eq hI

omit [IsDedekindDomain R] in
lemma disjSum_injective : Function.Injective
    (fun st : Multiset (HeightOneSpectrum R) × Multiset (HeightOneSpectrum R) =>
      st.1.disjSum st.2) := by
  classical
  intro a b h
  change a.1.map Sum.inl + a.2.map Sum.inr =
    b.1.map Sum.inl + b.2.map Sum.inr at h
  apply Prod.ext
  · rw [Multiset.ext]
    intro x
    have hx := congrArg (Multiset.count (Sum.inl x)) h
    rw [Multiset.count_add, Multiset.count_add,
      Multiset.count_map_eq_count' Sum.inl _ Sum.inl_injective x,
      Multiset.count_map_eq_count' Sum.inl _ Sum.inl_injective x] at hx
    have ha : Multiset.count (Sum.inl x) (a.2.map Sum.inr) = 0 :=
      Multiset.count_eq_zero_of_notMem (by simp)
    have hb : Multiset.count (Sum.inl x) (b.2.map Sum.inr) = 0 :=
      Multiset.count_eq_zero_of_notMem (by simp)
    simpa [ha, hb] using hx
  · rw [Multiset.ext]
    intro x
    have hx := congrArg (Multiset.count (Sum.inr x)) h
    rw [Multiset.count_add, Multiset.count_add,
      Multiset.count_map_eq_count' Sum.inr _ Sum.inr_injective x,
      Multiset.count_map_eq_count' Sum.inr _ Sum.inr_injective x] at hx
    have ha : Multiset.count (Sum.inr x) (a.1.map Sum.inl) = 0 :=
      Multiset.count_eq_zero_of_notMem (by simp)
    have hb : Multiset.count (Sum.inr x) (b.1.map Sum.inl) = 0 :=
      Multiset.count_eq_zero_of_notMem (by simp)
    simpa [ha, hb] using hx

/-- A finite prime of a number field, represented by a nonzero prime ideal. -/
abbrev FinitePrime (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- Two disjoint, norm-preserving choices of primes above every base prime
extend multiplicatively to an injective norm-product map on pairs of nonzero
ideals. -/
theorem exists_normProductIdealEmbedding
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    (h : ∀ v : FinitePrime K, ∃ q₁ q₂ : FinitePrime F,
      q₁ ≠ q₂ ∧
      q₁.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
      q₂.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
      Ideal.absNorm q₁.asIdeal = Ideal.absNorm v.asIdeal ∧
      Ideal.absNorm q₂.asIdeal = Ideal.absNorm v.asIdeal) :
    ∃ Φ : (Ideal (NumberField.RingOfIntegers K))⁰ ×
        (Ideal (NumberField.RingOfIntegers K))⁰ →
        (Ideal (NumberField.RingOfIntegers F))⁰,
      Function.Injective Φ ∧ ∀ IJ,
        Ideal.absNorm (Φ IJ : Ideal (NumberField.RingOfIntegers F)) =
          Ideal.absNorm (IJ.1 : Ideal (NumberField.RingOfIntegers K)) *
            Ideal.absNorm (IJ.2 : Ideal (NumberField.RingOfIntegers K)) := by
  classical
  let pair (v : FinitePrime K) :
      {qq : FinitePrime F × FinitePrime F //
        qq.1 ≠ qq.2 ∧
        qq.1.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        qq.2.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        Ideal.absNorm qq.1.asIdeal = Ideal.absNorm v.asIdeal ∧
        Ideal.absNorm qq.2.asIdeal = Ideal.absNorm v.asIdeal} :=
    Classical.choice (show Nonempty _ from by
      obtain ⟨q₁, q₂, hne, h₁, h₂, hn₁, hn₂⟩ := h v
      exact ⟨⟨(q₁, q₂), hne, h₁, h₂, hn₁, hn₂⟩⟩)
  let q₁ : FinitePrime K → FinitePrime F := fun v => (pair v).1.1
  let q₂ : FinitePrime K → FinitePrime F := fun v => (pair v).1.2
  have hq₁_under (v : FinitePrime K) :
      (q₁ v).asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal :=
    (pair v).2.2.1
  have hq₂_under (v : FinitePrime K) :
      (q₂ v).asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal :=
    (pair v).2.2.2.1
  have hq₁_norm (v : FinitePrime K) :
      Ideal.absNorm (q₁ v).asIdeal = Ideal.absNorm v.asIdeal :=
    (pair v).2.2.2.2.1
  have hq₂_norm (v : FinitePrime K) :
      Ideal.absNorm (q₂ v).asIdeal = Ideal.absNorm v.asIdeal :=
    (pair v).2.2.2.2.2
  have hq₁_ne_q₂ (v : FinitePrime K) : q₁ v ≠ q₂ v :=
    (pair v).2.1
  have hq₁_inj : Function.Injective q₁ := by
    intro v w hvw
    apply HeightOneSpectrum.ext
    have := congrArg
      (fun q : FinitePrime F =>
        q.asIdeal.under (NumberField.RingOfIntegers K)) hvw
    simpa only [hq₁_under] using this
  have hq₂_inj : Function.Injective q₂ := by
    intro v w hvw
    apply HeightOneSpectrum.ext
    have := congrArg
      (fun q : FinitePrime F =>
        q.asIdeal.under (NumberField.RingOfIntegers K)) hvw
    simpa only [hq₂_under] using this
  have hcross (v w : FinitePrime K) : q₁ v ≠ q₂ w := by
    intro hvw
    have hvw' : v = w := by
      apply HeightOneSpectrum.ext
      have := congrArg
        (fun q : FinitePrime F =>
          q.asIdeal.under (NumberField.RingOfIntegers K)) hvw
      simpa only [hq₁_under, hq₂_under] using this
    subst w
    exact hq₁_ne_q₂ v hvw
  let qsum : FinitePrime K ⊕ FinitePrime K ↪ FinitePrime F :=
    ⟨fun z => Sum.elim q₁ q₂ z, by
      intro z z' hzz
      cases z with
      | inl v =>
          cases z' with
          | inl w => exact congrArg Sum.inl (hq₁_inj hzz)
          | inr w => exact (hcross v w hzz).elim
      | inr v =>
          cases z' with
          | inl w => exact (hcross w v hzz.symm).elim
          | inr w => exact congrArg Sum.inr (hq₂_inj hzz)⟩
  let qIdeal : FinitePrime K ⊕ FinitePrime K ↪
      Ideal (NumberField.RingOfIntegers F) :=
    qsum.trans
      ⟨HeightOneSpectrum.asIdeal, fun _ _ hval => HeightOneSpectrum.ext hval⟩
  let factorPair (IJ :
      (Ideal (NumberField.RingOfIntegers K))⁰ ×
        (Ideal (NumberField.RingOfIntegers K))⁰) :
      Multiset (FinitePrime K ⊕ FinitePrime K) :=
    (spectrumFactors _ IJ.1.1).disjSum (spectrumFactors _ IJ.2.1)
  let phiIdeal (IJ :
      (Ideal (NumberField.RingOfIntegers K))⁰ ×
        (Ideal (NumberField.RingOfIntegers K))⁰) :
      Ideal (NumberField.RingOfIntegers F) :=
    ((factorPair IJ).map qIdeal).prod
  have hphi_ne (IJ) : phiIdeal IJ ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨v, _, hv⟩ := Multiset.mem_map.mp hzero
    change (qIdeal v : Ideal (NumberField.RingOfIntegers F)) = ⊥ at hv
    change (qsum v).asIdeal = ⊥ at hv
    exact (qsum v).ne_bot hv
  let Φ : (Ideal (NumberField.RingOfIntegers K))⁰ ×
        (Ideal (NumberField.RingOfIntegers K))⁰ →
        (Ideal (NumberField.RingOfIntegers F))⁰ :=
    fun IJ => ⟨phiIdeal IJ, mem_nonZeroDivisors_iff_ne_zero.mpr (hphi_ne IJ)⟩
  have hfactor (IJ) :
      UniqueFactorizationMonoid.normalizedFactors (phiIdeal IJ) =
        (factorPair IJ).map qIdeal := by
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    intro Q hQ
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hQ
    exact (qsum v).prime
  have hΦinj : Function.Injective Φ := by
    intro IJ IJ' hEq
    have hEqIdeal : phiIdeal IJ = phiIdeal IJ' := congrArg Subtype.val hEq
    have hEqFactors : (factorPair IJ).map qIdeal =
        (factorPair IJ').map qIdeal := by
      rw [← hfactor IJ, ← hfactor IJ', hEqIdeal]
    have hEqPair : factorPair IJ = factorPair IJ' :=
      Multiset.map_injective qIdeal.injective hEqFactors
    have hEqComponents :
        (spectrumFactors _ IJ.1.1, spectrumFactors _ IJ.2.1) =
          (spectrumFactors _ IJ'.1.1, spectrumFactors _ IJ'.2.1) :=
      disjSum_injective _ hEqPair
    apply Prod.ext
    · apply Subtype.ext
      rw [← spectrumFactors_prod_asIdeal _
          (mem_nonZeroDivisors_iff_ne_zero.mp IJ.1.2),
        ← spectrumFactors_prod_asIdeal _
          (mem_nonZeroDivisors_iff_ne_zero.mp IJ'.1.2),
        congrArg (fun m => (m.map HeightOneSpectrum.asIdeal).prod)
          (congrArg Prod.fst hEqComponents)]
    · apply Subtype.ext
      rw [← spectrumFactors_prod_asIdeal _
          (mem_nonZeroDivisors_iff_ne_zero.mp IJ.2.2),
        ← spectrumFactors_prod_asIdeal _
          (mem_nonZeroDivisors_iff_ne_zero.mp IJ'.2.2),
        congrArg (fun m => (m.map HeightOneSpectrum.asIdeal).prod)
          (congrArg Prod.snd hEqComponents)]
  refine ⟨Φ, hΦinj, ?_⟩
  intro IJ
  change Ideal.absNorm (phiIdeal IJ) = _
  dsimp only [phiIdeal]
  rw [map_multiset_prod, Multiset.map_map]
  change ((factorPair IJ).map
      (fun z => Ideal.absNorm (qIdeal z))).prod = _
  dsimp only [factorPair]
  rw [Multiset.map_disjSum, Multiset.prod_add]
  congr 1
  · have heq :
        (spectrumFactors _ IJ.1.1).map
            (fun v => Ideal.absNorm (qIdeal (Sum.inl v))) =
          (spectrumFactors _ IJ.1.1).map
            (fun v => Ideal.absNorm v.asIdeal) := by
      apply Multiset.map_congr rfl
      intro v hv
      change Ideal.absNorm (q₁ v).asIdeal = Ideal.absNorm v.asIdeal
      exact hq₁_norm v
    rw [heq]
    have hcomp :
        (spectrumFactors _ IJ.1.1).map
            (fun v => Ideal.absNorm v.asIdeal) =
          ((spectrumFactors _ IJ.1.1).map HeightOneSpectrum.asIdeal).map
            Ideal.absNorm := by
      rw [Multiset.map_map]
      rfl
    rw [hcomp, ← map_multiset_prod,
      spectrumFactors_prod_asIdeal _
        (mem_nonZeroDivisors_iff_ne_zero.mp IJ.1.2)]
  · have heq :
        (spectrumFactors _ IJ.2.1).map
            (fun v => Ideal.absNorm (qIdeal (Sum.inr v))) =
          (spectrumFactors _ IJ.2.1).map
            (fun v => Ideal.absNorm v.asIdeal) := by
      apply Multiset.map_congr rfl
      intro v hv
      change Ideal.absNorm (q₂ v).asIdeal = Ideal.absNorm v.asIdeal
      exact hq₂_norm v
    rw [heq]
    have hcomp :
        (spectrumFactors _ IJ.2.1).map
            (fun v => Ideal.absNorm v.asIdeal) =
          ((spectrumFactors _ IJ.2.1).map HeightOneSpectrum.asIdeal).map
            Ideal.absNorm := by
      rw [Multiset.map_map]
      rfl
    rw [hcomp, ← map_multiset_prod,
      spectrumFactors_prod_asIdeal _
        (mem_nonZeroDivisors_iff_ne_zero.mp IJ.2.2)]

end FactorEncoding

/-! ## Regrouping the Dedekind zeta series by nonzero ideals -/

open Asymptotics

open Asymptotics Finset in
/-- The partial sums of the norm-fibre cardinalities have the residue of the
Dedekind zeta function as their linear asymptotic. The finite-fibre rewrite is
adapted from the pinned Mathlib class-number-formula proof. -/
theorem tendsto_sum_card_absNorm_eq_div
    (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun n : ℕ ↦ (∑ m ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          Ideal.absNorm I = m} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← _root_.Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ _root_.Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- Absolute convergence of the coefficient presentation of the Dedekind
zeta series for real `s > 1`. -/
theorem lseriesSummable_dedekindZeta
    (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    LSeriesSummable
      (fun n ↦ (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = n} : ℂ)) s := by
  have hbase := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
      Ideal.absNorm I = n} : ℝ))
    (r := 1) (s := (s : ℂ))
    (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (r := 1) (by simpa using tendsto_sum_card_absNorm_eq_div K))
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  convert hbase using 1
  norm_cast

/-- The real Dirichlet series indexed directly by nonzero integral ideals. -/
def idealZeta (K : Type*) [Field K] [NumberField K] (s : ℝ) : ℝ :=
  ∑' I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥},
    (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ^ (-s)

private def realLTerm (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
      Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ s

private def fiberTerm (K : Type*) [Field K] [NumberField K] (s : ℝ)
    (x : (n : ℕ) × {I : Ideal (NumberField.RingOfIntegers K) //
      Ideal.absNorm I = n}) : ℝ :=
  if x.1 = 0 then 0 else (x.1 : ℝ) ^ (-s)

private lemma fiberTerm_nonneg
    (K : Type*) [Field K] [NumberField K] (s : ℝ) (x) :
    0 ≤ fiberTerm K s x := by
  simp only [fiberTerm]
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg x.1) (-s)

private lemma tsum_fiberTerm
    (K : Type*) [Field K] [NumberField K] (s : ℝ) (n : ℕ) :
    (∑' I : {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n},
      fiberTerm K s ⟨n, I⟩) = realLTerm K s n := by
  classical
  letI : Fintype {I : Ideal (NumberField.RingOfIntegers K) //
      Ideal.absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq (S :=
      NumberField.RingOfIntegers K) n).fintype
  rw [tsum_fintype]
  by_cases hn : n = 0
  · simp [fiberTerm, realLTerm, hn]
  · simp only [fiberTerm, realLTerm, hn, ↓reduceIte, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [Nat.card_eq_fintype_card]
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

private lemma summable_realLTerm
    (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) : Summable (realLTerm K s) := by
  rw [← Complex.summable_ofReal]
  have hsum := lseriesSummable_dedekindZeta K hs
  exact hsum.congr fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [realLTerm]
    · simp only [realLTerm, hn, ↓reduceIte, LSeries.term_of_ne_zero hn,
        ← Complex.ofReal_natCast n,
        ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      norm_cast

private lemma summable_fiberTerm
    (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) : Summable (fiberTerm K s) := by
  rw [summable_sigma_of_nonneg (fiberTerm_nonneg K s)]
  constructor
  · intro n
    classical
    letI : Fintype {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq (S :=
        NumberField.RingOfIntegers K) n).fintype
    exact Summable.of_finite
  · exact (summable_realLTerm K s hs).congr fun n =>
      (tsum_fiberTerm K s n).symm

private def allIdealTerm
    (K : Type*) [Field K] [NumberField K] (s : ℝ)
    (I : Ideal (NumberField.RingOfIntegers K)) : ℝ :=
  if I = ⊥ then 0 else (Ideal.absNorm I : ℝ) ^ (-s)

private lemma fiberTerm_eq_allIdealTerm_comp
    (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    fiberTerm K s = allIdealTerm K s ∘
      (Equiv.sigmaFiberEquiv
        (fun I : Ideal (NumberField.RingOfIntegers K) => Ideal.absNorm I)) := by
  funext x
  rcases x with ⟨n, I⟩
  simp only [fiberTerm, allIdealTerm, Function.comp_apply]
  by_cases hn : n = 0
  · rw [if_pos hn]
    have hI : (I : Ideal (NumberField.RingOfIntegers K)) = ⊥ := by
      rw [← Ideal.absNorm_eq_zero_iff, I.2, hn]
    simp [hI]
  · rw [if_neg hn]
    have hI : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
      intro hbot
      apply hn
      rw [← I.2, hbot, Ideal.absNorm_bot]
    simp [hI, I.2]

private lemma tsum_realLTerm_eq_allIdealTerm
    (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    (∑' n, realLTerm K s n) = ∑' I, allIdealTerm K s I := by
  have hsum := summable_fiberTerm K s hs
  calc
    (∑' n, realLTerm K s n) =
        ∑' n, ∑' I, fiberTerm K s ⟨n, I⟩ := by
      apply tsum_congr
      exact fun n => (tsum_fiberTerm K s n).symm
    _ = ∑' x, fiberTerm K s x := hsum.tsum_sigma.symm
    _ = ∑' I, allIdealTerm K s I := by
      rw [fiberTerm_eq_allIdealTerm_comp]
      exact (Equiv.sigmaFiberEquiv
        (fun I : Ideal (NumberField.RingOfIntegers K) => Ideal.absNorm I)).tsum_eq
        (allIdealTerm K s)

private lemma tsum_allIdealTerm_eq_idealZeta
    (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    (∑' I, allIdealTerm K s I) = idealZeta K s := by
  rw [idealZeta]
  calc
    (∑' I, allIdealTerm K s I) =
        ∑' I : Ideal (NumberField.RingOfIntegers K),
          ({I : Ideal (NumberField.RingOfIntegers K) | I ≠ ⊥}.indicator
            (fun I => (Ideal.absNorm I : ℝ) ^ (-s))) I := by
      apply tsum_congr
      intro I
      by_cases hI : I = ⊥
      · simp [allIdealTerm, hI]
      · simp [allIdealTerm, hI]
    _ = ∑' I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥},
        (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ^ (-s) :=
      (_root_.tsum_subtype
        {I : Ideal (NumberField.RingOfIntegers K) | I ≠ ⊥}
        (fun I => (Ideal.absNorm I : ℝ) ^ (-s))).symm

/-- For `s > 1`, Mathlib's coefficient definition of Dedekind zeta is the
sum of `N(I)⁻ˢ` over nonzero ideals. -/
theorem dedekindZeta_re_eq_idealZeta
    (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    (NumberField.dedekindZeta K s).re = idealZeta K s := by
  rw [NumberField.dedekindZeta, LSeries,
    Complex.re_tsum (lseriesSummable_dedekindZeta K hs)]
  calc
    _ = ∑' n, realLTerm K s n := by
      apply tsum_congr
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [realLTerm]
      · simp only [realLTerm, hn, ↓reduceIte, LSeries.term_of_ne_zero hn,
          ← Complex.ofReal_natCast n,
          ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
        rw [show (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
            Ideal.absNorm I = n} : ℂ) =
              ((Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
                Ideal.absNorm I = n} : ℝ) : ℂ) by norm_cast,
          ← Complex.ofReal_div, Complex.ofReal_re]
    _ = ∑' I, allIdealTerm K s I :=
      tsum_realLTerm_eq_allIdealTerm K s hs
    _ = idealZeta K s := tsum_allIdealTerm_eq_idealZeta K s

/-! ## Square domination and the pole contradiction -/

private def nonzeroIdealWeight
    (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (I : (Ideal (NumberField.RingOfIntegers K))⁰) : ℝ :=
  (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ^ (-s)

private lemma nonzeroIdealWeight_nonneg
    (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    0 ≤ nonzeroIdealWeight K s I :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private def nonzeroIdealEquiv
    (K : Type*) [Field K] [NumberField K] :
    (Ideal (NumberField.RingOfIntegers K))⁰ ≃
      {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥} where
  toFun I := ⟨I.1, by
    simpa only [Ideal.zero_eq_bot] using
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩
  invFun I := ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    simpa only [Ideal.zero_eq_bot] using I.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma tsum_nonzeroIdealWeight_eq_idealZeta
    (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    (∑' I, nonzeroIdealWeight K s I) = idealZeta K s := by
  calc
    (∑' I, nonzeroIdealWeight K s I) =
        ∑' I : (Ideal (NumberField.RingOfIntegers K))⁰,
          (Ideal.absNorm
            ((nonzeroIdealEquiv K I :
              {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥}) :
                Ideal (NumberField.RingOfIntegers K)) : ℝ) ^ (-s) := by
      apply tsum_congr
      intro I
      rfl
    _ = ∑' I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥},
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ^ (-s) :=
      (nonzeroIdealEquiv K).tsum_eq
        (fun I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥} =>
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ^ (-s))
    _ = idealZeta K s := rfl

private lemma nonzeroIdealWeight_summable
    (K : Type*) [Field K] [NumberField K] (s : ℝ) (hs : 1 < s) :
    Summable (nonzeroIdealWeight K s) := by
  let e := Equiv.sigmaFiberEquiv
    (fun I : Ideal (NumberField.RingOfIntegers K) => Ideal.absNorm I)
  have hsigma := summable_fiberTerm K s hs
  have hcomp : fiberTerm K s = allIdealTerm K s ∘ e :=
    fiberTerm_eq_allIdealTerm_comp K s
  have hsAll : Summable (allIdealTerm K s) := by
    apply e.summable_iff.mp
    rw [← hcomp]
    exact hsigma
  have hsSubtype := hsAll.subtype
    (fun I : Ideal (NumberField.RingOfIntegers K) => I ≠ ⊥)
  have hsNonzero : Summable
      (fun I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥} =>
        (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ^ (-s)) := by
    apply hsSubtype.congr
    intro I
    simp [allIdealTerm, I.2]
  have hsEquiv := (nonzeroIdealEquiv K).summable_iff.mpr hsNonzero
  exact hsEquiv.congr fun I => rfl

private theorem tsum_pair_le_of_injective
    {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    (hf : Summable f) (hf0 : ∀ a, 0 ≤ f a)
    (hg : Summable g) (hg0 : ∀ b, 0 ≤ g b)
    (e : α × α ↪ β)
    (he : ∀ x, g (e x) = f x.1 * f x.2) :
    (∑' a, f a) ^ 2 ≤ ∑' b, g b := by
  have hff : Summable (fun x : α × α ↦ f x.1 * f x.2) :=
    hf.mul_of_nonneg hf hf0 hf0
  rw [pow_two, hf.tsum_mul_tsum hf hff]
  exact hff.tsum_le_tsum_of_inj e e.injective
    (fun b _ ↦ hg0 b) (fun x ↦ (he x).ge) hg

private theorem idealZeta_sq_le_of_normProductEmbedding
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F]
    (Φ : (Ideal (NumberField.RingOfIntegers K))⁰ ×
        (Ideal (NumberField.RingOfIntegers K))⁰ →
        (Ideal (NumberField.RingOfIntegers F))⁰)
    (hΦ : Function.Injective Φ)
    (hnorm : ∀ IJ,
      Ideal.absNorm (Φ IJ : Ideal (NumberField.RingOfIntegers F)) =
        Ideal.absNorm (IJ.1 : Ideal (NumberField.RingOfIntegers K)) *
          Ideal.absNorm (IJ.2 : Ideal (NumberField.RingOfIntegers K)))
    (s : ℝ) (hs : 1 < s) :
    (idealZeta K s) ^ 2 ≤ idealZeta F s := by
  rw [← tsum_nonzeroIdealWeight_eq_idealZeta K s,
    ← tsum_nonzeroIdealWeight_eq_idealZeta F s]
  apply tsum_pair_le_of_injective
    (nonzeroIdealWeight_summable K s hs)
    (nonzeroIdealWeight_nonneg K s)
    (nonzeroIdealWeight_summable F s hs)
    (nonzeroIdealWeight_nonneg F s)
    ⟨Φ, hΦ⟩
  intro IJ
  change nonzeroIdealWeight F s (Φ IJ) =
    nonzeroIdealWeight K s IJ.1 * nonzeroIdealWeight K s IJ.2
  rw [nonzeroIdealWeight, nonzeroIdealWeight, nonzeroIdealWeight,
    hnorm IJ, Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem dedekindZeta_re_sq_le_of_twoPrimeLifts
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    (h : ∀ v : FinitePrime K,
      ∃ q₁ q₂ : FinitePrime F,
        q₁ ≠ q₂ ∧
        q₁.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        q₂.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        Ideal.absNorm q₁.asIdeal = Ideal.absNorm v.asIdeal ∧
        Ideal.absNorm q₂.asIdeal = Ideal.absNorm v.asIdeal)
    (s : ℝ) (hs : 1 < s) :
    ((NumberField.dedekindZeta K s).re) ^ 2 ≤
      (NumberField.dedekindZeta F s).re := by
  obtain ⟨Φ, hΦ, hnorm⟩ := exists_normProductIdealEmbedding h
  rw [dedekindZeta_re_eq_idealZeta K s hs,
    dedekindZeta_re_eq_idealZeta F s hs]
  exact idealZeta_sq_le_of_normProductEmbedding Φ hΦ hnorm s hs

private def realDedekindZeta
    (K : Type*) [Field K] [NumberField K] (s : ℝ) : ℝ :=
  (NumberField.dedekindZeta K (s : ℂ)).re

private theorem tendsto_sub_one_mul_realDedekindZeta_nhdsGT
    (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * realDedekindZeta K s)
      (𝓝[>] 1) (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have h := (Complex.continuous_re.tendsto
    (NumberField.dedekindZeta_residue K : ℂ)).comp
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  simpa only [Function.comp_def, realDedekindZeta, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, sub_zero, zero_mul, mul_zero] using h

private theorem false_of_realDedekindZeta_sq_le
    (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]
    (hle : ∀ s : ℝ, 1 < s →
      (realDedekindZeta K s) ^ 2 ≤ realDedekindZeta F s) : False := by
  have hK := tendsto_sub_one_mul_realDedekindZeta_nhdsGT K
  have hF := tendsto_sub_one_mul_realDedekindZeta_nhdsGT F
  have hleft : Tendsto
      (fun s : ℝ ↦ ((s - 1) * realDedekindZeta K s) ^ 2)
      (𝓝[>] 1) (𝓝 ((NumberField.dedekindZeta_residue K) ^ 2)) :=
    hK.pow 2
  have hright : Tendsto
      (fun s : ℝ ↦ (s - 1) * ((s - 1) * realDedekindZeta F s))
      (𝓝[>] 1) (𝓝 0) := by
    have hsub' : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_id.sub
        (tendsto_const_nhds : Tendsto
          (fun _ : ℝ ↦ (1 : ℝ)) (𝓝 1) (𝓝 1)))
    have hsub : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 0) :=
      hsub'.mono_left nhdsWithin_le_nhds
    simpa using hsub.mul hF
  have heventually :
      (fun s : ℝ ↦ ((s - 1) * realDedekindZeta K s) ^ 2) ≤ᶠ[𝓝[>] 1]
      (fun s : ℝ ↦ (s - 1) * ((s - 1) * realDedekindZeta F s)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 ≤ (s - 1) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (hle s hs) hs0
    nlinarith
  have hz : (NumberField.dedekindZeta_residue K) ^ 2 ≤ 0 :=
    tendsto_le_of_eventuallyLE hleft hright heventually
  nlinarith [NumberField.dedekindZeta_residue_pos K]

private theorem false_of_twoPrimeLifts
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F]
    (h : ∀ v : FinitePrime K,
      ∃ q₁ q₂ : FinitePrime F,
        q₁ ≠ q₂ ∧
        q₁.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        q₂.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        Ideal.absNorm q₁.asIdeal = Ideal.absNorm v.asIdeal ∧
        Ideal.absNorm q₂.asIdeal = Ideal.absNorm v.asIdeal) : False := by
  apply false_of_realDedekindZeta_sq_le K F
  intro s hs
  exact dedekindZeta_re_sq_le_of_twoPrimeLifts h s hs

/-! ## From complete splitting to the two prime lifts -/

private theorem absNorm_eq_of_mem_primesOver_of_allSplit
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] [IsGalois K F]
    (hdeg : 1 < Module.finrank K F)
    (hSplit : ∀ v : FinitePrime K,
      (Ideal.primesOver v.asIdeal
        (NumberField.RingOfIntegers F)).ncard = Module.finrank K F)
    (v : FinitePrime K)
    (Q : Ideal (NumberField.RingOfIntegers F))
    (hQ : Q ∈ Ideal.primesOver v.asIdeal
      (NumberField.RingOfIntegers F)) :
    Ideal.absNorm Q = Ideal.absNorm v.asIdeal := by
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver v.asIdeal := hQ.2
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      v.asIdeal (NumberField.RingOfIntegers F) Gal(F/K)
  rw [hSplit v, IsGaloisGroup.card_eq_finrank Gal(F/K) K F] at hfund
  have hfinrank : Module.finrank K F ≠ 0 :=
    Nat.ne_of_gt (lt_trans Nat.zero_lt_one hdeg)
  have hef :
      v.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers F) *
        v.asIdeal.inertiaDegIn (NumberField.RingOfIntegers F) = 1 :=
    (Nat.mul_eq_left hfinrank).mp hfund
  have hfIn : v.asIdeal.inertiaDegIn
      (NumberField.RingOfIntegers F) = 1 :=
    Nat.eq_one_of_dvd_one ⟨
      v.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers F), by
        simpa [mul_comm] using hef.symm⟩
  have hf : Q.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q Gal(F/K)]
    exact hfIn
  have hnorm := Ideal.absNorm_pow_inertiaDeg v.asIdeal Q
  simpa [hf] using hnorm.symm

private theorem twoPrimeLifts_of_allSplit
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] [IsGalois K F]
    (hdeg : 1 < Module.finrank K F)
    (hSplit : ∀ v : FinitePrime K,
      (Ideal.primesOver v.asIdeal
        (NumberField.RingOfIntegers F)).ncard = Module.finrank K F) :
    ∀ v : FinitePrime K,
      ∃ q₁ q₂ : FinitePrime F,
        q₁ ≠ q₂ ∧
        q₁.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        q₂.asIdeal.under (NumberField.RingOfIntegers K) = v.asIdeal ∧
        Ideal.absNorm q₁.asIdeal = Ideal.absNorm v.asIdeal ∧
        Ideal.absNorm q₂.asIdeal = Ideal.absNorm v.asIdeal := by
  intro v
  let Q₁ : Ideal.primesOver v.asIdeal
      (NumberField.RingOfIntegers F) :=
    Classical.choice v.asIdeal.nonempty_primesOver
  have hcard : 1 < (Ideal.primesOver v.asIdeal
      (NumberField.RingOfIntegers F)).ncard := by
    rw [hSplit v]
    exact hdeg
  obtain ⟨Q₂, hQ₂, hne⟩ :=
    Set.exists_ne_of_one_lt_ncard hcard
      (Q₁ : Ideal (NumberField.RingOfIntegers F))
  let q₁ : FinitePrime F :=
    ⟨Q₁.1, Q₁.2.1,
      Ideal.ne_bot_of_mem_primesOver v.ne_bot Q₁.2⟩
  let q₂ : FinitePrime F :=
    ⟨Q₂, hQ₂.1,
      Ideal.ne_bot_of_mem_primesOver v.ne_bot hQ₂⟩
  refine ⟨q₁, q₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact hne (congrArg HeightOneSpectrum.asIdeal heq).symm
  · exact ((Ideal.liesOver_iff _ _).mp Q₁.2.2).symm
  · exact ((Ideal.liesOver_iff _ _).mp hQ₂.2).symm
  · exact absNorm_eq_of_mem_primesOver_of_allSplit
      hdeg hSplit v Q₁ Q₁.2
  · exact absNorm_eq_of_mem_primesOver_of_allSplit
      hdeg hSplit v Q₂ hQ₂

/-- Every nontrivial finite Galois extension of number fields has a finite
prime that does not split completely. -/
theorem exists_nonSplitFinitePrime
    {K F : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] [IsGalois K F]
    (hdeg : 1 < Module.finrank K F) :
    ∃ v : FinitePrime K,
      (Ideal.primesOver v.asIdeal
        (NumberField.RingOfIntegers F)).ncard ≠ Module.finrank K F := by
  by_contra hnone
  apply false_of_twoPrimeLifts (K := K) (F := F)
  apply twoPrimeLifts_of_allSplit hdeg
  intro v
  by_contra hv
  exact hnone ⟨v, hv⟩

end

end NumberTheory.WeakChebotarev
