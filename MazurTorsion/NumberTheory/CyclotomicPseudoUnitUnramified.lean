/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Valuation.LocalSubring
import MazurTorsion.NumberTheory.CyclotomicPseudoUnitNormalization

/-!
# Ramification of locally primary cyclotomic pseudo-units

This file proves the ramification-theoretic part of the one-sided Kummer
reciprocity argument.  Away from the unique prime above `p`, a pseudo-unit
radicand can be normalized to an integral unit at the chosen prime.  The
derivative of its Kummer polynomial then witnesses that the prime does not
divide the different.

At the cyclotomic prime, a local `p`-th root gives an embedding of the Kummer
extension into the completed base field.  Pulling back the completion's
maximal ideal produces one prime of ramification index one; Galois
transitivity gives the same index for every prime above the cyclotomic prime.
-/

open scoped NumberField nonZeroDivisors WithZero

namespace NumberTheory.CyclotomicCharacter

universe u

/-- The rational prime `p` belongs to a finite prime of `Q(zeta_p)` exactly
when that finite prime is the cyclotomic prime. -/
theorem natCast_prime_mem_finitePrime_iff_eq_cyclotomicPrime
    {p : ℕ} [Fact p.Prime]
    (v : FinitePrime (PrimeCyclotomicField p)) :
    (p : NumberField.RingOfIntegers (PrimeCyclotomicField p)) ∈ v.asIdeal ↔
      v = cyclotomicPrime p := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  letI : IsCyclotomicExtension {p} ℚ (PrimeCyclotomicField p) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let hζ := IsCyclotomicExtension.zeta_spec p ℚ (PrimeCyclotomicField p)
  constructor
  · intro hpv
    have hover : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
      (Ideal.liesOver_span_iff v.isPrime.ne_top
        (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))).mpr hpv
    letI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hover
    apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
      p (PrimeCyclotomicField p) hζ v.asIdeal
  · rintro rfl
    letI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ
        (PrimeCyclotomicField p) := by simpa using
      (inferInstance : IsCyclotomicExtension {p} ℚ
        (PrimeCyclotomicField p))
    have hζ' : IsPrimitiveRoot
        (IsCyclotomicExtension.zeta p ℚ (PrimeCyclotomicField p))
        (p ^ (0 + 1)) := by
      convert hζ using 1; simp
    exact IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one p 0 hζ'

end NumberTheory.CyclotomicCharacter

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- A Kummer extension defined by a pseudo-unit is unramified at every
finite prime other than the unique cyclotomic prime. -/
theorem isUnramifiedAtFinitePlace_of_ne_cyclotomicPrime
    (E : InverseExtension p L)
    (hdiv : ∀ w : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) w
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand))
    (v : FinitePrime (PrimeCyclotomicField p))
    (hv : v ≠ cyclotomicPrime p) :
    E.IsUnramifiedAtFinitePlace v := by
  let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
  let K := PrimeCyclotomicField p
  let S := NumberField.RingOfIntegers L
  let P := E.kummerPresentation
  obtain ⟨c, η, B, hη_ne, hη, hspan, hcoprime_v, _hcoprime_cyclotomic⟩ :=
    E.exists_coprime_integral_pseudoUnit_normalization
      hdiv v.asIdeal v.ne_bot
  let θ : L := algebraMap K L (c : K) * P.radical
  have hθ_pow : θ ^ p = algebraMap R L η := by
    calc
      θ ^ p = algebraMap K L ((c : K) ^ p) * P.radical ^ p := by
        simp only [θ, mul_pow, map_pow]
      _ = algebraMap K L ((c : K) ^ p) *
          algebraMap K L P.radicand := by rw [P.pow_radical]
      _ = algebraMap K L (P.radicand * (c : K) ^ p) := by
        rw [map_mul, mul_comm]
      _ = algebraMap K L (algebraMap R K η) := by rw [hη]
      _ = algebraMap R L η := by rw [IsScalarTower.algebraMap_apply R K L]
  have hθ_integral : IsIntegral R θ := by
    apply IsIntegral.of_pow (Fact.out : p.Prime).pos
    rw [hθ_pow]
    exact isIntegral_algebraMap
  let θint : S := ⟨θ, isIntegral_trans θ hθ_integral⟩
  have hθint_val : algebraMap S L θint = θ := by
    change algebraMap (NumberField.RingOfIntegers L) L
      (⟨θ, isIntegral_trans θ hθ_integral⟩ :
        NumberField.RingOfIntegers L) = θ
    exact NumberField.RingOfIntegers.map_mk θ _
  have hradical_mem :
      P.radical ∈ IntermediateField.adjoin K ({θ} : Set L) := by
    have hθ_mem : θ ∈ IntermediateField.adjoin K ({θ} : Set L) :=
      IntermediateField.subset_adjoin K {θ} (Set.mem_singleton θ)
    have hc_mem : algebraMap K L ((c : K)⁻¹) ∈
        IntermediateField.adjoin K ({θ} : Set L) :=
      (IntermediateField.adjoin K ({θ} : Set L)).algebraMap_mem _
    rw [show P.radical = algebraMap K L ((c : K)⁻¹) * θ by
      change P.radical = algebraMap K L ((c : K)⁻¹) *
        (algebraMap K L (c : K) * P.radical)
      rw [map_inv₀, ← mul_assoc,
        inv_mul_cancel₀
          ((map_ne_zero (algebraMap K L)).mpr (Units.ne_zero c)), one_mul]]
    exact mul_mem hc_mem hθ_mem
  have hθ_adjoin : IntermediateField.adjoin K ({θ} : Set L) = ⊤ := by
    apply top_unique
    rw [← P.adjoin_radical]
    exact IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr hradical_mem)
  have hθint_adjoin :
      Algebra.adjoin K
        ({algebraMap S L θint} : Set L) = ⊤ := by
    rw [hθint_val]
    exact Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic θ) hθ_adjoin
  have hθ_pow_finrank :
      θ ^ Module.finrank K L = algebraMap K L (algebraMap R K η) := by
    rw [E.finrank_eq_prime, hθ_pow, IsScalarTower.algebraMap_apply R K L]
  have hpoly_irreducible :
      Irreducible
        (Polynomial.X ^ p - Polynomial.C (algebraMap R K η)) := by
    simpa only [K, E.finrank_eq_prime] using
      irreducible_X_pow_sub_C_of_root_adjoin_eq_top
        hθ_pow_finrank hθ_adjoin
  have hpoly_aeval :
      Polynomial.aeval θ
        (Polynomial.X ^ p - Polynomial.C (algebraMap R K η)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      hθ_pow, IsScalarTower.algebraMap_apply R K L, sub_self]
  have hminpoly_K :
      minpoly K θ =
        Polynomial.X ^ p - Polynomial.C (algebraMap R K η) :=
    (minpoly.eq_of_irreducible_of_monic hpoly_irreducible hpoly_aeval
      (Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero)).symm
  have hθint_integral_R : IsIntegral R θint :=
    IsIntegralClosure.isIntegral R L θint
  have hminpoly_R :
      minpoly R θint = Polynomial.X ^ p - Polynomial.C η := by
    apply Polynomial.map_injective (algebraMap R K)
      (IsFractionRing.injective R K)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L hθint_integral_R,
      hθint_val, hminpoly_K]
    simp
  have hη_not_mem_v : η ∉ v.asIdeal := by
    intro hηv
    have hspan_le : Ideal.span {η} ≤ v.asIdeal :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hηv)
    have hcoprime_add : Ideal.span {η} + v.asIdeal = 1 :=
      (Ideal.isCoprime_iff_add).mp hcoprime_v
    apply v.isPrime.ne_top
    apply top_unique
    rw [← Ideal.one_eq_top, ← hcoprime_add]
    exact add_le hspan_le le_rfl
  have hp_not_mem_v : (p : R) ∉ v.asIdeal := by
    intro hpv
    exact hv
      ((natCast_prime_mem_finitePrime_iff_eq_cyclotomicPrime v).mp hpv)
  change Algebra.IsUnramifiedIn S v.asIdeal
  intro Q hQ hQover
  letI : Q.IsPrime := hQ
  letI : Q.LiesOver v.asIdeal := hQover
  have hθint_pow : θint ^ p = algebraMap R S η := by
    apply NumberField.RingOfIntegers.ext
    change θ ^ p = algebraMap R L η
    exact hθ_pow
  have hθint_not_mem_Q : θint ∉ Q := by
    intro hθQ
    have hηQ : algebraMap R S η ∈ Q := by
      rw [← hθint_pow]
      exact Q.pow_mem_of_mem hθQ p (Fact.out : p.Prime).pos
    exact hη_not_mem_v
      ((Ideal.mem_of_liesOver Q v.asIdeal η).mpr hηQ)
  have hp_not_mem_Q : (p : S) ∉ Q := by
    intro hpQ
    exact hp_not_mem_v
      ((Ideal.mem_of_liesOver Q v.asIdeal (p : R)).mpr (by
        simpa only [map_natCast] using hpQ))
  have hθint_pred_not_mem_Q : θint ^ (p - 1) ∉ Q :=
    mt (hQ.mem_of_pow_mem (p - 1)) hθint_not_mem_Q
  have hderivative_not_mem_Q :
      (p : S) * θint ^ (p - 1) ∉ Q :=
    hQ.mul_notMem hp_not_mem_Q hθint_pred_not_mem_Q
  have hderivative_mem :
      Polynomial.aeval θint (Polynomial.derivative (minpoly R θint)) ∈
        differentIdeal R S :=
    aeval_derivative_mem_differentIdeal R K L θint hθint_adjoin
  have hderivative_value_mem :
      (p : S) * θint ^ (p - 1) ∈ differentIdeal R S := by
    rw [hminpoly_R] at hderivative_mem
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero] at hderivative_mem
    simpa only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
      map_natCast] using hderivative_mem
  rw [← not_dvd_differentIdeal_iff (A := R) (B := S) (P := Q)]
  intro hQdiv
  exact hderivative_not_mem_Q
    ((Ideal.dvd_iff_le.mp hQdiv) hderivative_value_mem)

/-- If the Kummer radicand is a `p`-th power in the cyclotomic-prime
completion, then the Kummer extension is unramified at that prime. -/
theorem isUnramifiedAtCyclotomicPrime_of_isPthPower
    (E : InverseExtension p L)
    (hlocal : ∃ y : (cyclotomicPrime p).adicCompletion
        (PrimeCyclotomicField p),
      y ^ p = algebraMap (PrimeCyclotomicField p)
        ((cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p))
        E.kummerPresentation.radicand) :
    E.IsUnramifiedAtFinitePlace (cyclotomicPrime p) := by
  let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
  let K := PrimeCyclotomicField p
  let S := NumberField.RingOfIntegers L
  let v := cyclotomicPrime p
  let C := v.adicCompletion K
  let T := v.adicCompletionIntegers K
  let P := E.kummerPresentation
  letI : IsScalarTower R T C := by
    exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsScalarTower'
      R K v
  letI : IsGalois (PrimeCyclotomicField p) L := E.isGalois
  obtain ⟨y, hy⟩ := hlocal
  have hP_integral : IsIntegral K P.radical := IsIntegral.of_finite K P.radical
  have hP_adjoin_algebra : Algebra.adjoin K ({P.radical} : Set L) = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hP_integral.isAlgebraic
      P.adjoin_radical
  have hP_aeval : Polynomial.aeval P.radical
      (Polynomial.X ^ p - Polynomial.C P.radicand) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      P.pow_radical, sub_self]
  have hP_minpoly : minpoly K P.radical =
      Polynomial.X ^ p - Polynomial.C P.radicand :=
    (minpoly.eq_of_irreducible_of_monic (P.irreducible E) hP_aeval
      (Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero)).symm
  let pb : PowerBasis K L :=
    PowerBasis.ofAdjoinEqTop hP_integral hP_adjoin_algebra
  have hy_minpoly : Polynomial.aeval y (minpoly K pb.gen) = 0 := by
    rw [PowerBasis.ofAdjoinEqTop_gen, hP_minpoly]
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy,
      sub_self]
  let φ : L →ₐ[K] C := pb.lift y hy_minpoly
  let ψC : S →ₐ[R] C :=
    (φ.restrictScalars R).comp (IsScalarTower.toAlgHom R S L)
  have hψC_mem (x : S) : ψC x ∈ T := by
    have hxS : IsIntegral R x :=
      IsIntegralClosure.isIntegral R L x
    have hx : IsIntegral R ((IsScalarTower.toAlgHom R S L) x) :=
      hxS.map (IsScalarTower.toAlgHom R S L)
    have hx' : IsIntegral R (ψC x) := by
      simpa only [ψC, AlgHom.coe_comp, Function.comp_apply] using
        hx.map (φ.restrictScalars R)
    have hxT : IsIntegral T (ψC x) := hx'.tower_top
    exact LocalSubring.mem_of_isMax_of_isIntegral
      (ValuationSubring.isMax_toLocalSubring T) hxT
  let ψ : S →ₐ[R] T :=
    { toFun := fun x ↦ ⟨ψC x, hψC_mem x⟩
      map_one' := by
        apply Subtype.ext
        exact ψC.map_one
      map_mul' := fun x z ↦ by
        apply Subtype.ext
        exact ψC.map_mul x z
      map_zero' := by
        apply Subtype.ext
        exact ψC.map_zero
      map_add' := fun x z ↦ by
        apply Subtype.ext
        exact ψC.map_add x z
      commutes' := fun r ↦ by
        apply Subtype.ext
        exact ψC.commutes r }
  let m : Ideal T := IsLocalRing.maximalIdeal T
  let Q : Ideal S := Ideal.comap ψ.toRingHom m
  have hm_prime : m.IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal T).isPrime
  letI : m.IsPrime := hm_prime
  have hQ_prime : Q.IsPrime := hm_prime.comap ψ.toRingHom
  letI : Q.IsPrime := hQ_prime
  have hQ_over : Q.LiesOver v.asIdeal := by
    constructor
    ext r
    change r ∈ v.asIdeal ↔ ψ (algebraMap R S r) ∈ m
    rw [ψ.commutes]
    change r ∈ v.asIdeal ↔
      (algebraMap R T r : T) ∈ IsLocalRing.maximalIdeal T
    have hmem (a : T) :
        a ∈ IsLocalRing.maximalIdeal T ↔
          Valued.v (a : C) < 1 := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        not_congr
          IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      constructor
      · intro ha
        exact lt_of_le_of_ne a.2 ha
      · exact ne_of_lt
    rw [hmem (algebraMap R T r)]
    change r ∈ v.asIdeal ↔
      Valued.v (algebraMap R C r) < 1
    have hc : Valued.v (algebraMap R C r) =
        v.valuation K (algebraMap R K r) := by
      rw [IsScalarTower.algebraMap_apply R K C]
      exact
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v r
    rw [hc,
      IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  letI : Q.LiesOver v.asIdeal := hQ_over
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  let πT : T := algebraMap R T π
  have hπT_value : Valued.v (πT : C) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap R C π) = WithZero.exp (-1 : ℤ)
    rw [IsScalarTower.algebraMap_apply R K C]
    have hKC := congrFun
      (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion R K v)
      (algebraMap R K π)
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply,
      id_eq] at hKC
    rw [hKC,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hgenerator :
      (inferInstance :
        (Valued.v : Valuation C ℤᵐ⁰).IsRankOneDiscrete).generator =
        Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)
  have hπT_uniformizer :
      (Valued.v : Valuation C ℤᵐ⁰).IsUniformizer πT := by
    rw [Valuation.IsUniformizer, hπT_value, hgenerator]
    rfl
  have hm_span : m = Ideal.span {πT} := by
    change IsLocalRing.maximalIdeal T = Ideal.span {πT}
    exact hπT_uniformizer.is_generator
  have hv_map_le_Q : Ideal.map (algebraMap R S) v.asIdeal ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (Q.over_def v.asIdeal).le
  have hπ_v : π ∈ v.asIdeal := by
    rw [← v.intValuation_lt_one_iff_mem, hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hramQ' : v.asIdeal.ramificationIdx' Q = 1 := by
    by_contra hram
    have hv_map_le_Q2 : Ideal.map (algebraMap R S) v.asIdeal ≤ Q ^ 2 :=
      (Ideal.ramificationIdx'_ne_one_iff hv_map_le_Q).mp hram
    have hπ_map_Q2 : algebraMap R S π ∈ Q ^ 2 :=
      hv_map_le_Q2 (Ideal.mem_map_of_mem (algebraMap R S) hπ_v)
    have hmapQ : Ideal.map ψ.toRingHom Q ≤ m := by
      change Ideal.map ψ.toRingHom (Ideal.comap ψ.toRingHom m) ≤ m
      exact Ideal.map_comap_le
    have hmapQ2 : Ideal.map ψ.toRingHom (Q ^ 2) ≤ m ^ 2 := by
      rw [Ideal.map_pow]
      exact pow_left_mono 2 hmapQ
    have hπT_m2 : πT ∈ m ^ 2 := by
      apply hmapQ2
      have hmapped := Ideal.mem_map_of_mem ψ.toRingHom hπ_map_Q2
      have hψπ : ψ (algebraMap R S π) = πT := by
        exact ψ.commutes π
      rw [← hψπ]
      exact hmapped
    have hm_le_sq : m ≤ m ^ 2 := by
      calc
        m = Ideal.span {πT} := hm_span
        _ ≤ m ^ 2 :=
          Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπT_m2)
    have hm_sq_lt : m ^ 2 < m :=
      Ideal.pow_lt_self m (IsDiscreteValuationRing.not_a_field T)
        (IsLocalRing.maximalIdeal.isMaximal T).ne_top 2 (by norm_num)
    exact (not_le_of_gt hm_sq_lt) hm_le_sq
  have hramQ : Q.ramificationIdx R = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]
    exact hramQ'
  refine
    (E.isUnramifiedAtFinitePlace_iff_ramificationIdx_eq_one
      (cyclotomicPrime p)).mpr ?_
  intro Q' _ hQ'_over
  letI : Q'.LiesOver v.asIdeal := hQ'_over
  exact
    (Ideal.ramificationIdx_eq_of_isGaloisGroup
      v.asIdeal Q' Q Gal(L/K)).trans hramQ

/-- A pseudo-unit radicand that is locally a `p`-th power at the unique
cyclotomic prime defines an extension unramified at every finite place. -/
theorem isUnramifiedAtFinitePlaces_of_pseudoUnit_locallyPrimary
    (E : InverseExtension p L)
    (hdiv : ∀ w : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) w
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand))
    (hlocal : ∃ y : (cyclotomicPrime p).adicCompletion
        (PrimeCyclotomicField p),
      y ^ p = algebraMap (PrimeCyclotomicField p)
        ((cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p))
        E.kummerPresentation.radicand) :
    E.IsUnramifiedAtFinitePlaces := by
  intro v
  by_cases hv : v = cyclotomicPrime p
  · subst v
    exact E.isUnramifiedAtCyclotomicPrime_of_isPthPower hlocal
  · exact E.isUnramifiedAtFinitePlace_of_ne_cyclotomicPrime hdiv v hv

end NumberTheory.CyclotomicCharacter.InverseExtension
