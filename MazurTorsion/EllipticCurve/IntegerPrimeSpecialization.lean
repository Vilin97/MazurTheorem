/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime

/-!
# Torsion in the formal kernel at the integer primes five and eleven

The exact-pinned `EllipticCurves` reduction library proves that the formal kernel over an adic
completion contains no nonzero torsion when the absolute ramification index is less than
`p - 1`.  This file discharges that arithmetic condition for the two unramified completions of
`ℚ` used by the formal-immersion route, at `p = 5` and `p = 11`.

These statements do not assume good reduction: they concern the formal filtration attached to
an arbitrary integral Weierstrass equation whose generic fibre is elliptic.  Thus they are the
part of torsion specialization which can be checked before a Neron special fibre and its
component map have been constructed.
-/

open WeierstrassCurve

namespace MazurTorsion.IntegerPrimeSpecialization

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open WeierstrassCurve.Affine

/-- The height-one prime `(p)` of `ℤ`. -/
def integerPrime (p : ℕ) [Fact p.Prime] : HeightOneSpectrum ℤ :=
  .ofPrime (p := Ideal.span {(p : ℤ)})
    (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp Fact.out))

@[simp] theorem integerPrime_asIdeal (p : ℕ) [Fact p.Prime] :
    (integerPrime p).asIdeal = Ideal.span {(p : ℤ)} :=
  rfl

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The integer height-one prime above five, with its primality witness fixed internally. -/
def atFive : HeightOneSpectrum ℤ := integerPrime 5

/-- The integer height-one prime above eleven, with its primality witness fixed internally. -/
def atEleven : HeightOneSpectrum ℤ := integerPrime 11

@[simp] theorem atFive_asIdeal : atFive.asIdeal = Ideal.span {(5 : ℤ)} :=
  rfl

@[simp] theorem atEleven_asIdeal : atEleven.asIdeal = Ideal.span {(11 : ℤ)} :=
  rfl

theorem five_mem_atFive : (5 : ℤ) ∈ atFive.asIdeal := by
  rw [atFive_asIdeal]
  exact Ideal.mem_span_singleton_self 5

theorem five_not_mem_atFive_pow_four : (5 : ℤ) ∉ atFive.asIdeal ^ (5 - 1) := by
  rw [atFive_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  norm_num

theorem eleven_mem_atEleven : (11 : ℤ) ∈ atEleven.asIdeal := by
  rw [atEleven_asIdeal]
  exact Ideal.mem_span_singleton_self 11

theorem eleven_not_mem_atEleven_pow_ten :
    (11 : ℤ) ∉ atEleven.asIdeal ^ (11 - 1) := by
  rw [atEleven_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  norm_num

instance : DecidableEq (ℤ ⧸ atFive.asIdeal) :=
  (Int.quotientSpanNatEquivZMod 5).toEquiv.decidableEq

instance : DecidableEq (ℤ ⧸ atEleven.asIdeal) :=
  (Int.quotientSpanNatEquivZMod 11).toEquiv.decidableEq

/-- The residue field at the integer prime five, identified with `ZMod 5`. -/
noncomputable def residueFiveAlgEquiv : (ℤ ⧸ atFive.asIdeal) ≃ₐ[ℤ] ZMod 5 :=
  AlgEquiv.ofRingEquiv (f := Int.quotientSpanNatEquivZMod 5) fun x ↦ by
    change (Int.quotientSpanNatEquivZMod 5 :
      (ℤ ⧸ Ideal.span {((5 : ℕ) : ℤ)}) →+* ZMod 5)
        (Ideal.Quotient.mk (Ideal.span {((5 : ℕ) : ℤ)}) x) = Int.castRingHom (ZMod 5) x
    simpa only [RingHom.comp_apply] using DFunLike.congr_fun
      (Int.quotientSpanNatEquivZMod_comp_Quotient_mk 5) x

/-- The residue field at the integer prime eleven, identified with `ZMod 11`. -/
noncomputable def residueElevenAlgEquiv : (ℤ ⧸ atEleven.asIdeal) ≃ₐ[ℤ] ZMod 11 :=
  AlgEquiv.ofRingEquiv (f := Int.quotientSpanNatEquivZMod 11) fun x ↦ by
    change (Int.quotientSpanNatEquivZMod 11 :
      (ℤ ⧸ Ideal.span {((11 : ℕ) : ℤ)}) →+* ZMod 11)
        (Ideal.Quotient.mk (Ideal.span {((11 : ℕ) : ℤ)}) x) = Int.castRingHom (ZMod 11) x
    simpa only [RingHom.comp_apply] using DFunLike.congr_fun
      (Int.quotientSpanNatEquivZMod_comp_Quotient_mk 11) x

/-- Membership in the maximal-ideal filtration of the completion is detected before
completion.  This is the integer-prime specialization of the exact-pin comparison theorem. -/
theorem natCast_mem_completion_maximalIdeal_pow_iff
    (v : HeightOneSpectrum ℤ) {p n : ℕ} :
    (p : v.adicCompletionIntegers ℚ) ∈
        maximalIdeal (v.adicCompletionIntegers ℚ) ^ n ↔
      (p : ℤ) ∈ v.asIdeal ^ n := by
  rw [show (p : v.adicCompletionIntegers ℚ) =
      algebraMap ℤ (v.adicCompletionIntegers ℚ) (p : ℤ) from (map_natCast _ p).symm,
    algebraMap_mem_maximalIdeal_pow_iff]

theorem five_mem_completion_maximalIdeal :
    (5 : atFive.adicCompletionIntegers ℚ) ∈
      maximalIdeal (atFive.adicCompletionIntegers ℚ) := by
  have h : (5 : ℤ) ∈ atFive.asIdeal ^ 1 := by
    rw [pow_one]
    exact five_mem_atFive
  simpa [pow_one] using
    (natCast_mem_completion_maximalIdeal_pow_iff atFive (p := 5) (n := 1)).mpr h

theorem five_not_mem_completion_maximalIdeal_pow_four :
    (5 : atFive.adicCompletionIntegers ℚ) ∉
      maximalIdeal (atFive.adicCompletionIntegers ℚ) ^ (5 - 1) := by
  intro h
  have hz := (natCast_mem_completion_maximalIdeal_pow_iff atFive
    (p := 5) (n := 5 - 1)).mp h
  exact five_not_mem_atFive_pow_four hz

theorem eleven_mem_completion_maximalIdeal :
    (11 : atEleven.adicCompletionIntegers ℚ) ∈
      maximalIdeal (atEleven.adicCompletionIntegers ℚ) := by
  have h : (11 : ℤ) ∈ atEleven.asIdeal ^ 1 := by
    rw [pow_one]
    exact eleven_mem_atEleven
  simpa [pow_one] using
    (natCast_mem_completion_maximalIdeal_pow_iff atEleven (p := 11) (n := 1)).mpr h

theorem eleven_not_mem_completion_maximalIdeal_pow_ten :
    (11 : atEleven.adicCompletionIntegers ℚ) ∉
      maximalIdeal (atEleven.adicCompletionIntegers ℚ) ^ (11 - 1) := by
  intro h
  have hz := (natCast_mem_completion_maximalIdeal_pow_iff atEleven
    (p := 11) (n := 11 - 1)).mp h
  exact eleven_not_mem_atEleven_pow_ten hz

/-- At the unramified prime five, a torsion point in the formal kernel is zero.  The integral
model need not have good reduction. -/
theorem torsion_eq_zero_of_mem_formalKernel_atFive
    {W : Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    {P : W.Point} (hP : P ∈ filtration hW 0) (hord : IsOfFinAddOrder P) :
    P = 0 := by
  exact eq_zero_of_isOfFinAddOrder_of_mem_filtration (by norm_num)
    five_mem_completion_maximalIdeal five_not_mem_completion_maximalIdeal_pow_four hP hord

/-- At the unramified prime eleven, a torsion point in the formal kernel is zero.  The integral
model need not have good reduction. -/
theorem torsion_eq_zero_of_mem_formalKernel_atEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    {P : W.Point} (hP : P ∈ filtration hW 0) (hord : IsOfFinAddOrder P) :
    P = 0 := by
  exact eq_zero_of_isOfFinAddOrder_of_mem_filtration (by norm_num)
    eleven_mem_completion_maximalIdeal eleven_not_mem_completion_maximalIdeal_pow_ten hP hord

/-- Two torsion points at five agree if their difference lies in the formal kernel.  This is the
collision statement consumed by torsion specialization. -/
theorem torsion_eq_of_sub_mem_formalKernel_atFive
    {W : Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    {P Q : W.Point} (hP : IsOfFinAddOrder P) (hQ : IsOfFinAddOrder Q)
    (hPQ : P - Q ∈ filtration hW 0) : P = Q := by
  apply sub_eq_zero.mp
  exact torsion_eq_zero_of_mem_formalKernel_atFive hW hPQ
    (sub_eq_add_neg P Q ▸ hP.add hQ.neg)

/-- Two torsion points at eleven agree if their difference lies in the formal kernel. -/
theorem torsion_eq_of_sub_mem_formalKernel_atEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    {P Q : W.Point} (hP : IsOfFinAddOrder P) (hQ : IsOfFinAddOrder Q)
    (hPQ : P - Q ∈ filtration hW 0) : P = Q := by
  apply sub_eq_zero.mp
  exact torsion_eq_zero_of_mem_formalKernel_atEleven hW hPQ
    (sub_eq_add_neg P Q ▸ hP.add hQ.neg)

end MazurTorsion.IntegerPrimeSpecialization
