/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import MazurTorsion.NumberTheory.UnramifiedArtin

/-!
# Empty-support Selmer groups and ideal-class torsion

For a Dedekind domain `R` with fraction field `K` and a positive natural
number `n`, this file constructs the canonical homomorphism

`K⟮∅, n⟯ → ClassGroup R[n]`.

A representative has principal divisor divisible coefficientwise by `n`.
Dividing that divisor and using the free-abelian description of nonzero
fractional ideals gives an `n`-th root ideal. Its ideal class is independent
of the representative. The construction is formalized first on the preimage
of the Selmer group in `Kˣ`, then descended through actual `n`-th powers.

The kernel is proved to be exactly the image of integral units modulo
`n`-th powers, and the map onto class-group torsion is proved surjective.
Thus this file formalizes the short exact sequence

`Rˣ/(Rˣ)^n → K⟮∅, n⟯ → ClassGroup R[n] → 1`.

This is ideal-theoretic and uses no global reciprocity or class-field-theory
existence theorem. The construction is also proved natural under ring
automorphisms of `R`, acting through the induced automorphisms of `K`, the
empty-support Selmer group, and the ideal class group.
-/


open scoped nonZeroDivisors

namespace IsDedekindDomain.selmerGroup

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The exponent of a principal fractional ideal is the negative logarithm
of the normalized finite-place valuation. -/
theorem count_spanSingleton_eq_neg_valuationLog
    (a : K) (ha : a ≠ 0) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ a) =
      -WithZero.log (v.valuation K a) := by
  let x : Kˣ := Units.mk0 a ha
  let s := IsLocalization.sec R⁰ (x : K)
  have hs : IsLocalization.mk' K s.1 s.2 = x :=
    IsLocalization.mk'_sec K x
  have hI : FractionalIdeal.spanSingleton R⁰ (x : K) =
      FractionalIdeal.spanSingleton R⁰
          ((algebraMap R K) (s.2 : R))⁻¹ *
        (Ideal.span {s.1} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg
    rw [← hs, IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hcount := FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) hI
  have hval := congrArg WithZero.log
    (HeightOneSpectrum.valuationOfNeZeroToFun_eq v x)
  dsimp only [HeightOneSpectrum.valuationOfNeZeroToFun, x, s] at hval hcount ⊢
  simp only [Units.val_mk0] at hval hcount ⊢
  change
    (-((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {(IsLocalization.sec R⁰ a).1})).factors : ℤ) -
      -((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {((IsLocalization.sec R⁰ a).2 : R)})).factors : ℤ)) =
        WithZero.log (v.valuation K a) at hval
  rw [hcount]
  omega

theorem valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  erw [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply,
    ← QuotientGroup.coe_mk', QuotientGroup.map_mk']
  constructor
  · intro h
    have hq := (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.injective
      (h.trans (map_one
        (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative).symm)
    have hm := (QuotientGroup.eq_one_iff
      (v.valuationOfNeZero x)).mp hq
    change Multiplicative.toAdd (v.valuationOfNeZero x) ∈
      AddSubgroup.zmultiples (n : ℤ) at hm
    rw [AddSubgroup.mem_zmultiples_iff] at hm
    rcases hm with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [mul_comm] using hk.symm
  · rintro ⟨k, hk⟩
    have hm : Multiplicative.toAdd (v.valuationOfNeZero x) ∈
        AddSubgroup.zmultiples (n : ℤ) := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨k, by simpa [mul_comm] using hk.symm⟩
    change v.valuationOfNeZero x ∈
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) at hm
    have hq := (QuotientGroup.eq_one_iff
      (v.valuationOfNeZero x)).mpr hm
    have he := congrArg
      (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative hq
    exact he.trans (map_one
      (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative)

open NumberTheory.UnramifiedArtin

/-- The finitely supported divisor of a nonzero field element, obtained from
its principal fractional ideal. -/
noncomputable def principalDivisor :
    Kˣ →* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  (fractionalIdealDivisor R K).toMultiplicativeRight.comp
    (toPrincipalIdeal R K)

@[simp]
theorem principalDivisor_apply (x : Kˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (principalDivisor (R := R) (K := K) x) v =
      -Multiplicative.toAdd (v.valuationOfNeZero x) := by
  have hval := congrArg WithZero.log
    (HeightOneSpectrum.valuationOfNeZero_eq v x)
  change Multiplicative.toAdd (v.valuationOfNeZero x) =
    WithZero.log (v.valuation K (x : K)) at hval
  unfold principalDivisor
  change fractionalIdealDivisor R K
      (Additive.ofMul (toPrincipalIdeal R K x)) v = _
  rw [fractionalIdealDivisor_apply]
  simp only [toMul_ofMul, coe_toPrincipalIdeal]
  rw [count_spanSingleton_eq_neg_valuationLog (x : K) x.ne_zero v]
  exact congrArg Neg.neg hval.symm

/-- Representatives in `Kˣ` whose classes satisfy all empty-support
Selmer local conditions. -/
def preSelmer (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap
    (QuotientGroup.mk'
      (powMonoidHom n : Kˣ →* Kˣ).range)
    (selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n))

/-- Every coefficient of the principal divisor of a pre-Selmer
representative is divisible by `n`. -/
theorem principalDivisor_coeff_dvd (n : ℕ)
    (x : preSelmer (R := R) (K := K) n)
    (v : HeightOneSpectrum R) :
    (n : ℤ) ∣
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) v := by
  have hlocal : v.valuationOfNeZeroMod n
      (QuotientGroup.mk (x : Kˣ)) = 1 :=
    x.property v (Set.notMem_empty v)
  have hv := (valuationOfNeZeroMod_mk_eq_one_iff v n (x : Kˣ)).mp hlocal
  rw [principalDivisor_apply]
  exact dvd_neg.mpr hv

/-- Divide the principal divisor of a pre-Selmer representative
coefficientwise by `n`. -/
noncomputable def rootDivisor (n : ℕ)
    (x : preSelmer (R := R) (K := K) n) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.mapRange (fun z : ℤ => z / (n : ℤ)) (by simp)
    (Multiplicative.toAdd
      (principalDivisor (R := R) (K := K) (x : Kˣ)))

@[simp]
theorem rootDivisor_apply (n : ℕ)
    (x : preSelmer (R := R) (K := K) n)
    (v : HeightOneSpectrum R) :
    rootDivisor (R := R) (K := K) n x v =
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) v / (n : ℤ) := by
  rfl

theorem rootDivisor_one (n : ℕ) :
    rootDivisor (R := R) (K := K) n 1 = 0 := by
  ext v
  simp [rootDivisor]

theorem rootDivisor_mul (n : ℕ)
    (x y : preSelmer (R := R) (K := K) n) :
    rootDivisor (R := R) (K := K) n (x * y) =
      rootDivisor (R := R) (K := K) n x +
        rootDivisor (R := R) (K := K) n y := by
  ext v
  simp only [rootDivisor_apply, Subgroup.coe_mul, map_mul,
    toAdd_mul, Finsupp.add_apply]
  exact Int.add_ediv_of_dvd_left
    (principalDivisor_coeff_dvd (R := R) (K := K) n x v)

/-- Taking the divided divisor is a homomorphism on pre-Selmer
representatives. -/
noncomputable def rootDivisorHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun x := Multiplicative.ofAdd (rootDivisor (R := R) (K := K) n x)
  map_one' := congrArg Multiplicative.ofAdd
    (rootDivisor_one (R := R) (K := K) n)
  map_mul' x y := congrArg Multiplicative.ofAdd
    (rootDivisor_mul (R := R) (K := K) n x y)

/-- The fractional ideal whose divisor is the coefficientwise divided
principal divisor. -/
noncomputable def rootIdealHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      (FractionalIdeal R⁰ K)ˣ :=
  (fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm.toMonoidHom.comp
    (rootDivisorHom (R := R) (K := K) n)

/-- Multiplying the divided divisor by `n` recovers the original principal
divisor. -/
theorem nsmul_rootDivisor (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    n • rootDivisor (R := R) (K := K) n x =
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) := by
  ext v
  have hdvd := principalDivisor_coeff_dvd
    (R := R) (K := K) n x v
  simpa only [Finsupp.smul_apply, rootDivisor_apply, nsmul_eq_mul,
    Nat.cast_ofNat, mul_comm] using Int.ediv_mul_cancel hdvd

/-- The `n`-th power of the selected root ideal is the principal ideal of
the representative. -/
theorem rootIdealHom_pow (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    rootIdealHom (R := R) (K := K) n x ^ n =
      toPrincipalIdeal R K (x : Kˣ) := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  rw [map_pow]
  change (fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n) x))) ^ n = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (n • rootDivisor (R := R) (K := K) n x) =
    principalDivisor (R := R) (K := K) (x : Kˣ)
  rw [nsmul_rootDivisor]
  rfl

/-- On an actual `n`-th power, the selected root ideal is the expected
principal ideal. -/
theorem rootIdealHom_of_pow (n : ℕ) [NeZero n]
    (y : Kˣ)
    (hy : y ^ n ∈ preSelmer (R := R) (K := K) n) :
    rootIdealHom (R := R) (K := K) n ⟨y ^ n, hy⟩ =
      toPrincipalIdeal R K y := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  change fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n) ⟨y ^ n, hy⟩)) = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (rootDivisor (R := R) (K := K) n ⟨y ^ n, hy⟩) =
    principalDivisor (R := R) (K := K) y
  apply Multiplicative.ofAdd.injective
  ext v
  change rootDivisor (R := R) (K := K) n ⟨y ^ n, hy⟩ v =
    Multiplicative.toAdd
      (principalDivisor (R := R) (K := K) y) v
  simp only [rootDivisor_apply, map_pow,
    toAdd_pow, Finsupp.smul_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr (NeZero.ne n))

/-- The class of a principal fractional ideal is trivial. -/
@[simp]
theorem classGroup_mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 := by
  rw [ClassGroup.mk_eq_one_iff]
  exact ⟨x, by
    change ((toPrincipalIdeal R K x : FractionalIdeal R⁰ K) :
      Submodule R K) = R ∙ (x : K)
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩

/-- Map a pre-Selmer representative to the class of its divided root
ideal. -/
noncomputable def preSelmerClassHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →* ClassGroup R :=
  (ClassGroup.mk K).comp (rootIdealHom (R := R) (K := K) n)

/-- The image class is killed by `n`. -/
theorem preSelmerClassHom_pow (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    preSelmerClassHom (R := R) (K := K) n x ^ n = 1 := by
  change ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n x) ^ n = 1
  rw [← map_pow, rootIdealHom_pow]
  exact classGroup_mk_toPrincipalIdeal (R := R) (K := K) (x : Kˣ)

/-- Actual `n`-th powers are pre-Selmer representatives. -/
theorem powRange_le_preSelmer (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range ≤
      preSelmer (R := R) (K := K) n := by
  rintro z ⟨y, rfl⟩
  have hq : QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range) (y ^ n) = 1 := by
    apply (QuotientGroup.eq_one_iff (y ^ n)).mpr
    exact ⟨y, rfl⟩
  change QuotientGroup.mk (y ^ n) ∈
    selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)
  rw [hq]
  exact Subgroup.one_mem _

/-- The subgroup of actual `n`-th powers inside the pre-Selmer group. -/
def preSelmerPowers (n : ℕ) :
    Subgroup (preSelmer (R := R) (K := K) n) :=
  ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf
    (preSelmer (R := R) (K := K) n)

/-- Changing a pre-Selmer representative by an actual `n`-th power does
not change the resulting ideal class. -/
theorem preSelmerPowers_le_ker (n : ℕ) [NeZero n] :
    preSelmerPowers (R := R) (K := K) n ≤
      (preSelmerClassHom (R := R) (K := K) n).ker := by
  intro z hz
  rcases hz with ⟨y, hy⟩
  have hyPre : y ^ n ∈ preSelmer (R := R) (K := K) n :=
    powRange_le_preSelmer (R := R) (K := K) n ⟨y, rfl⟩
  have hz_eq : z = (⟨y ^ n, hyPre⟩ :
      preSelmer (R := R) (K := K) n) := by
    apply Subtype.ext
    exact hy.symm
  change preSelmerClassHom (R := R) (K := K) n z = 1
  rw [hz_eq]
  change ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n ⟨y ^ n, hyPre⟩) = 1
  rw [rootIdealHom_of_pow, classGroup_mk_toPrincipalIdeal]

/-- Send a pre-Selmer representative to its class in the empty-support
Selmer group. -/
def preSelmerToSelmer (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), x.property⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

theorem preSelmerToSelmer_surjective (n : ℕ) :
    Function.Surjective (preSelmerToSelmer
      (R := R) (K := K) n) := by
  intro q
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom n : Kˣ →* Kˣ).range (q :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
  have hxPre : x ∈ preSelmer (R := R) (K := K) n := by
    change (QuotientGroup.mk'
      (powMonoidHom n : Kˣ →* Kˣ).range) x ∈
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n)
    exact hx ▸ q.property
  refine ⟨⟨x, hxPre⟩, ?_⟩
  apply Subtype.ext
  exact hx

theorem preSelmerToSelmer_ker (n : ℕ) :
    (preSelmerToSelmer (R := R) (K := K) n).ker =
      preSelmerPowers (R := R) (K := K) n := by
  ext x
  constructor
  · intro hx
    have hq : QuotientGroup.mk (x : Kˣ) = 1 :=
      congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff (x : Kˣ)).mp hq
  · intro hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (x : Kˣ)).mpr hx

/-- The quotient of pre-Selmer representatives by actual powers is the
empty-support Selmer group. -/
noncomputable def preSelmerQuotientEquiv (n : ℕ) :
    preSelmer (R := R) (K := K) n ⧸
        preSelmerPowers (R := R) (K := K) n ≃*
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) :=
  QuotientGroup.liftEquiv
    (preSelmerPowers (R := R) (K := K) n)
    (preSelmerToSelmer_surjective (R := R) (K := K) n)
    (preSelmerToSelmer_ker (R := R) (K := K) n).symm

/-- Descend the root-ideal class homomorphism across actual `n`-th
powers. -/
noncomputable def quotientClassGroupHom (n : ℕ) [NeZero n] :
    preSelmer (R := R) (K := K) n ⧸
        preSelmerPowers (R := R) (K := K) n →* ClassGroup R :=
  QuotientGroup.lift
    (preSelmerPowers (R := R) (K := K) n)
    (preSelmerClassHom (R := R) (K := K) n)
    (preSelmerPowers_le_ker (R := R) (K := K) n)

/-- The canonical homomorphism from the empty-support `n`-Selmer group to
the ideal class group. -/
noncomputable def toClassGroup (n : ℕ) [NeZero n] :
    selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) →*
      ClassGroup R :=
  (quotientClassGroupHom (R := R) (K := K) n).comp
    (preSelmerQuotientEquiv (R := R) (K := K) n).symm.toMonoidHom

/-- Formula for the class-group map on a chosen field representative. -/
theorem toClassGroup_preSelmerToSelmer (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    toClassGroup (R := R) (K := K) n
        (preSelmerToSelmer (R := R) (K := K) n x) =
      preSelmerClassHom (R := R) (K := K) n x := by
  let e := preSelmerQuotientEquiv (R := R) (K := K) n
  have he : e (QuotientGroup.mk x) =
      preSelmerToSelmer (R := R) (K := K) n x := by
    rfl
  change quotientClassGroupHom (R := R) (K := K) n
      (e.symm (preSelmerToSelmer (R := R) (K := K) n x)) = _
  rw [← he, e.symm_apply_apply]
  rfl

/-- Every class in the image is killed by `n`. -/
theorem toClassGroup_pow (n : ℕ) [NeZero n]
    (q : selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) :
    toClassGroup (R := R) (K := K) n q ^ n = 1 := by
  obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective
    (R := R) (K := K) n q
  rw [toClassGroup_preSelmerToSelmer]
  exact preSelmerClassHom_pow (R := R) (K := K) n x

/-- The `n`-torsion subgroup of the ideal class group. -/
def classGroupTorsion (n : ℕ) : Subgroup (ClassGroup R) :=
  (powMonoidHom n : ClassGroup R →* ClassGroup R).ker

/-- The canonical empty-support Selmer-to-class-group map, with codomain
restricted to `n`-torsion. -/
noncomputable def toClassGroupTorsion (n : ℕ) [NeZero n] :
    selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) →*
      classGroupTorsion (R := R) n :=
  (toClassGroup (R := R) (K := K) n).codRestrict
    (classGroupTorsion (R := R) n)
    (fun q => toClassGroup_pow (R := R) (K := K) n q)

/-- An integral unit, regarded as a pre-Selmer representative. -/
noncomputable def unitPreSelmer (n : ℕ) (u : Rˣ) :
    preSelmer (R := R) (K := K) n :=
  ⟨Units.map (algebraMap R K : R →+* K) u,
    (@fromUnit R _ _ K _ _ _ n u).property⟩

@[simp]
theorem preSelmerToSelmer_unitPreSelmer (n : ℕ) (u : Rˣ) :
    preSelmerToSelmer (R := R) (K := K) n
      (unitPreSelmer (R := R) (K := K) n u) =
    @fromUnit R _ _ K _ _ _ n u := by
  rfl

@[simp]
theorem rootDivisor_unitPreSelmer (n : ℕ) (u : Rˣ) :
    rootDivisor (R := R) (K := K) n
      (unitPreSelmer (R := R) (K := K) n u) = 0 := by
  ext v
  rw [rootDivisor_apply, principalDivisor_apply]
  rw [show ((unitPreSelmer (R := R) (K := K) n u :
      preSelmer (R := R) (K := K) n) : Kˣ) =
      Units.map (algebraMap R K : R →+* K) u from rfl]
  rw [HeightOneSpectrum.valuation_of_unit_eq]
  simp

@[simp]
theorem rootIdealHom_unitPreSelmer (n : ℕ) (u : Rˣ) :
    rootIdealHom (R := R) (K := K) n
      (unitPreSelmer (R := R) (K := K) n u) = 1 := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  change fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n)
          (unitPreSelmer (R := R) (K := K) n u))) = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (rootDivisor (R := R) (K := K) n
        (unitPreSelmer (R := R) (K := K) n u)) = _
  rw [rootDivisor_unitPreSelmer, map_one]
  rfl

/-- Integral units lie in the kernel of the class-group map. -/
@[simp]
theorem toClassGroup_fromUnit (n : ℕ) [NeZero n] (u : Rˣ) :
    toClassGroup (R := R) (K := K) n
      (@fromUnit R _ _ K _ _ _ n u) = 1 := by
  rw [← preSelmerToSelmer_unitPreSelmer,
    toClassGroup_preSelmerToSelmer]
  change ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n
        (unitPreSelmer (R := R) (K := K) n u)) = 1
  rw [rootIdealHom_unitPreSelmer, map_one]

@[simp]
theorem fromUnitLift_mk (n : ℕ) [Fact (0 < n)] (u : Rˣ) :
    @fromUnitLift R _ _ K _ _ _ n _
        (QuotientGroup.mk u) =
      @fromUnit R _ _ K _ _ _ n u := by
  unfold fromUnitLift
  rw [MonoidHom.comp_apply]
  change QuotientGroup.kerLift (@fromUnit R _ _ K _ _ _ n)
      ((QuotientGroup.quotientMulEquivOfEq
        (fromUnit_ker (R := R) (K := K))).symm
          (QuotientGroup.mk u)) = _
  rw [show (QuotientGroup.quotientMulEquivOfEq
      (fromUnit_ker (R := R) (K := K))).symm
        (QuotientGroup.mk u) = QuotientGroup.mk u from rfl,
    QuotientGroup.kerLift_mk]

/-- The image of integral units modulo powers lies in the kernel. -/
theorem fromUnitLift_range_le_ker (n : ℕ) [Fact (0 < n)] [NeZero n] :
    (@fromUnitLift R _ _ K _ _ _ n _).range ≤
      (toClassGroup (R := R) (K := K) n).ker := by
  rintro q ⟨a, rfl⟩
  induction a using QuotientGroup.induction_on with
  | _ u =>
      rw [fromUnitLift_mk]
      exact MonoidHom.mem_ker.mpr
        (toClassGroup_fromUnit (R := R) (K := K) n u)

/-- If the root-ideal class of a pre-Selmer representative is trivial,
then its Selmer class comes from an integral unit. -/
theorem preSelmerToSelmer_mem_fromUnitLift_range_of_class_eq_one
    (n : ℕ) [Fact (0 < n)] [NeZero n]
    (x : preSelmer (R := R) (K := K) n)
    (hx : preSelmerClassHom (R := R) (K := K) n x = 1) :
    preSelmerToSelmer (R := R) (K := K) n x ∈
      (@fromUnitLift R _ _ K _ _ _ n _).range := by
  have hclass : ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n x) = 1 := hx
  have hprincipal := (ClassGroup.mk_eq_one_iff).mp hclass
  obtain ⟨a, haIdeal⟩ :=
    (FractionalIdeal.isPrincipal_iff
      (rootIdealHom (R := R) (K := K) n x :
        FractionalIdeal R⁰ K)).mp hprincipal
  have ha : a ≠ 0 := by
    intro ha
    subst a
    rw [FractionalIdeal.spanSingleton_zero] at haIdeal
    exact Units.ne_zero _ haIdeal
  let y : Kˣ := Units.mk0 a ha
  have hroot : rootIdealHom (R := R) (K := K) n x =
      toPrincipalIdeal R K y := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact haIdeal
  have hpow := rootIdealHom_pow (R := R) (K := K) n x
  rw [hroot, ← map_pow] at hpow
  have hspan : FractionalIdeal.spanSingleton R⁰ ((y : K) ^ n) =
      FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) := by
    simpa only [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val] using
      congrArg Units.val hpow
  obtain ⟨u, hu⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  have hxy : (x : Kˣ) =
      Units.map (algebraMap R K : R →+* K) u * y ^ n := by
    apply Units.ext
    change ((x : Kˣ) : K) = algebraMap R K (u : R) * (y : K) ^ n
    simpa only [Units.smul_def, Algebra.smul_def] using hu.symm
  have hyn : QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range) (y ^ n) = 1 := by
    apply (QuotientGroup.eq_one_iff (y ^ n)).mpr
    exact ⟨y, rfl⟩
  have hsel : preSelmerToSelmer (R := R) (K := K) n x =
      @fromUnit R _ _ K _ _ _ n u := by
    apply Subtype.ext
    change QuotientGroup.mk (x : Kˣ) =
      QuotientGroup.mk
        (Units.map (algebraMap R K : R →+* K) u)
    rw [hxy, QuotientGroup.mk_mul, hyn]
    exact mul_one (QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range)
      (Units.map (algebraMap R K : R →+* K) u))
  refine ⟨QuotientGroup.mk u, ?_⟩
  rw [fromUnitLift_mk]
  exact hsel.symm

/-- Every element of the kernel comes from an integral unit modulo powers. -/
theorem ker_le_fromUnitLift_range (n : ℕ)
    [Fact (0 < n)] [NeZero n] :
    (toClassGroup (R := R) (K := K) n).ker ≤
      (@fromUnitLift R _ _ K _ _ _ n _).range := by
  intro q hq
  obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective
    (R := R) (K := K) n q
  apply preSelmerToSelmer_mem_fromUnitLift_range_of_class_eq_one
    (R := R) (K := K) n x
  change toClassGroup (R := R) (K := K) n
      (preSelmerToSelmer (R := R) (K := K) n x) = 1 at hq
  rwa [toClassGroup_preSelmerToSelmer] at hq

/-- Exactness at the empty-support Selmer group: the kernel of the canonical
map to class-group `n`-torsion is precisely the image of integral units
modulo `n`-th powers. -/
theorem fromUnitLift_range_eq_ker (n : ℕ)
    [Fact (0 < n)] [NeZero n] :
    (@fromUnitLift R _ _ K _ _ _ n _).range =
      (toClassGroup (R := R) (K := K) n).ker := by
  apply le_antisymm
  · exact fromUnitLift_range_le_ker (R := R) (K := K) n
  · exact ker_le_fromUnitLift_range (R := R) (K := K) n
/-- Restricting the codomain to class-group torsion does not change the
kernel. -/
theorem toClassGroupTorsion_ker (n : ℕ) [NeZero n] :
    (toClassGroupTorsion (R := R) (K := K) n).ker =
      (toClassGroup (R := R) (K := K) n).ker := by
  ext q
  constructor
  · intro hq
    apply MonoidHom.mem_ker.mpr
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hq)
  · intro hq
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp hq

/-- Exactness of the unit-to-Selmer-to-class-torsion sequence. -/
theorem mulExact_fromUnitLift_toClassGroupTorsion
    (n : ℕ) [Fact (0 < n)] [NeZero n] :
    Function.MulExact
      (@fromUnitLift R _ _ K _ _ _ n _)
      (toClassGroupTorsion (R := R) (K := K) n) := by
  rw [MonoidHom.mulExact_iff, toClassGroupTorsion_ker]
  exact (fromUnitLift_range_eq_ker (R := R) (K := K) n).symm

/-- If an `n`-th power of a fractional ideal is principal, its generator is
a pre-Selmer representative and the selected root ideal is the original
ideal. -/
theorem exists_preSelmer_with_rootIdeal_eq_of_pow_eq
    (n : ℕ) [NeZero n]
    (I : (FractionalIdeal R⁰ K)ˣ) (x : Kˣ)
    (hpow : I ^ n = toPrincipalIdeal R K x) :
    ∃ z : preSelmer (R := R) (K := K) n,
      (z : Kˣ) = x ∧
        rootIdealHom (R := R) (K := K) n z = I := by
  have hdiv : principalDivisor (R := R) (K := K) x =
      (fractionalIdealDivisorMulEquiv (R := R) (K := K) I) ^ n := by
    unfold principalDivisor fractionalIdealDivisorMulEquiv
    change (fractionalIdealDivisor R K).toMultiplicativeRight
        (toPrincipalIdeal R K x) =
      (fractionalIdealDivisor R K).toMultiplicativeRight I ^ n
    rw [← hpow, map_pow]
  have hcoeff (v : HeightOneSpectrum R) :
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
    have hpdiv : (n : ℤ) ∣
        Multiplicative.toAdd
          (principalDivisor (R := R) (K := K) x) v := by
      rw [hdiv]
      refine ⟨Multiplicative.toAdd
        (fractionalIdealDivisorMulEquiv (R := R) (K := K) I) v, ?_⟩
      simp only [toAdd_pow, Finsupp.smul_apply, nsmul_eq_mul]
    rw [principalDivisor_apply] at hpdiv
    exact dvd_neg.mp hpdiv
  have hxPre : x ∈ preSelmer (R := R) (K := K) n := by
    intro v _
    exact (valuationOfNeZeroMod_mk_eq_one_iff v n x).mpr (hcoeff v)
  let z : preSelmer (R := R) (K := K) n := ⟨x, hxPre⟩
  refine ⟨z, rfl, ?_⟩
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  change fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n) z)) = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (rootDivisor (R := R) (K := K) n z) =
    fractionalIdealDivisorMulEquiv (R := R) (K := K) I
  apply Multiplicative.ofAdd.injective
  ext v
  change Multiplicative.toAdd
      (principalDivisor (R := R) (K := K) x) v / (n : ℤ) =
    Multiplicative.toAdd
      (fractionalIdealDivisorMulEquiv (R := R) (K := K) I) v
  have hv := congrArg
    (fun D : Multiplicative (HeightOneSpectrum R →₀ ℤ) =>
      Multiplicative.toAdd D v) hdiv
  rw [hv]
  simp only [toAdd_pow, Finsupp.smul_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr (NeZero.ne n))

/-- Every ideal class has a representative in the chosen fraction field. -/
theorem classGroup_mk_surjective :
    Function.Surjective (ClassGroup.mk K :
      (FractionalIdeal R⁰ K)ˣ →* ClassGroup R) := by
  intro c
  exact ClassGroup.induction K (fun I => ⟨I, rfl⟩) c

/-- The canonical empty-support Selmer map is onto class-group
`n`-torsion. -/
theorem toClassGroupTorsion_surjective (n : ℕ) [NeZero n] :
    Function.Surjective
      (toClassGroupTorsion (R := R) (K := K) n) := by
  intro c
  obtain ⟨I, hI⟩ := classGroup_mk_surjective
    (R := R) (K := K) (c : ClassGroup R)
  have hIpowClass : ClassGroup.mk K (I ^ n) = 1 := by
    rw [map_pow, hI]
    exact c.property
  have hprincipal := (ClassGroup.mk_eq_one_iff).mp hIpowClass
  obtain ⟨a, haIdeal⟩ :=
    (FractionalIdeal.isPrincipal_iff (I ^ n :
      FractionalIdeal R⁰ K)).mp hprincipal
  have ha : a ≠ 0 := by
    intro ha
    subst a
    rw [FractionalIdeal.spanSingleton_zero] at haIdeal
    exact Units.ne_zero (I ^ n) haIdeal
  let x : Kˣ := Units.mk0 a ha
  have hpow : I ^ n = toPrincipalIdeal R K x := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact haIdeal
  obtain ⟨z, _, hzroot⟩ :=
    exists_preSelmer_with_rootIdeal_eq_of_pow_eq
      (R := R) (K := K) n I x hpow
  refine ⟨preSelmerToSelmer (R := R) (K := K) n z, ?_⟩
  apply Subtype.ext
  change toClassGroup (R := R) (K := K) n
      (preSelmerToSelmer (R := R) (K := K) n z) =
    (c : ClassGroup R)
  rw [toClassGroup_preSelmerToSelmer]
  change ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n z) = (c : ClassGroup R)
  rw [hzroot, hI]

/-- The fraction-field unit equivalence induced by a base-ring
automorphism. -/
noncomputable def fieldUnitEquivOfRingEquiv (g : R ≃+* R) : Kˣ ≃* Kˣ :=
  Units.mapEquiv
    (IsFractionRing.ringEquivOfRingEquiv
      (K := K) (L := K) g).toMulEquiv

/-- The nonzero-fractional-ideal equivalence induced by a base-ring
automorphism. -/
noncomputable def fractionalIdealUnitEquivOfRingEquiv
    (g : R ≃+* R) :
    (FractionalIdeal R⁰ K)ˣ ≃* (FractionalIdeal R⁰ K)ˣ :=
  Units.mapEquiv
    (FractionalIdeal.ringEquivOfRingEquiv K K g).toMulEquiv

@[simp]
theorem fractionalIdealUnitEquivOfRingEquiv_toPrincipalIdeal
    (g : R ≃+* R) (x : Kˣ) :
    fractionalIdealUnitEquivOfRingEquiv (R := R) (K := K) g
        (toPrincipalIdeal R K x) =
      toPrincipalIdeal R K
        (fieldUnitEquivOfRingEquiv (R := R) (K := K) g x) := by
  apply Units.ext
  simp only [fractionalIdealUnitEquivOfRingEquiv,
    fieldUnitEquivOfRingEquiv, Units.coe_mapEquiv,
    coe_toPrincipalIdeal]
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton
    (K := K) (L := K) (f := g) (x : K)

theorem fieldUnitEquivOfRingEquiv_mem_preSelmer
    (n : ℕ) [NeZero n] (g : R ≃+* R)
    (x : preSelmer (R := R) (K := K) n) :
    fieldUnitEquivOfRingEquiv (R := R) (K := K) g (x : Kˣ) ∈
      preSelmer (R := R) (K := K) n := by
  let I := fractionalIdealUnitEquivOfRingEquiv
    (R := R) (K := K) g
      (rootIdealHom (R := R) (K := K) n x)
  have hpow := congrArg
    (fractionalIdealUnitEquivOfRingEquiv
      (R := R) (K := K) g)
    (rootIdealHom_pow (R := R) (K := K) n x)
  rw [map_pow,
    fractionalIdealUnitEquivOfRingEquiv_toPrincipalIdeal] at hpow
  obtain ⟨z, hz, _⟩ :=
    exists_preSelmer_with_rootIdeal_eq_of_pow_eq
      (R := R) (K := K) n I
        (fieldUnitEquivOfRingEquiv (R := R) (K := K) g (x : Kˣ)) hpow
  rw [← hz]
  exact z.property

/-- The action induced by a ring automorphism on pre-Selmer
representatives. -/
noncomputable def preSelmerEquivOfRingEquiv
    (n : ℕ) [NeZero n] (g : R ≃+* R) :
    preSelmer (R := R) (K := K) n ≃*
      preSelmer (R := R) (K := K) n where
  toFun x := ⟨fieldUnitEquivOfRingEquiv (R := R) (K := K) g (x : Kˣ),
    fieldUnitEquivOfRingEquiv_mem_preSelmer
      (R := R) (K := K) n g x⟩
  invFun x := ⟨fieldUnitEquivOfRingEquiv (R := R) (K := K) g.symm (x : Kˣ),
    fieldUnitEquivOfRingEquiv_mem_preSelmer
      (R := R) (K := K) n g.symm x⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    change (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) g).symm
      (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) g
        ((x : Kˣ) : K)) = ((x : Kˣ) : K)
    exact RingEquiv.symm_apply_apply _ _
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    change IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) g
      ((IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) g).symm
        ((x : Kˣ) : K)) = ((x : Kˣ) : K)
    exact RingEquiv.apply_symm_apply _ _
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul _ _ _

@[simp]
theorem preSelmerEquivOfRingEquiv_coe
    (n : ℕ) [NeZero n] (g : R ≃+* R)
    (x : preSelmer (R := R) (K := K) n) :
    (preSelmerEquivOfRingEquiv (R := R) (K := K) n g x : Kˣ) =
      fieldUnitEquivOfRingEquiv (R := R) (K := K) g (x : Kˣ) :=
  rfl

theorem fractionalIdeal_pow_injective (n : ℕ) [NeZero n] :
    Function.Injective
      (fun I : (FractionalIdeal R⁰ K)ˣ => I ^ n) := by
  intro I J hIJ
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  have hdiv := congrArg
    (fractionalIdealDivisorMulEquiv (R := R) (K := K)) hIJ
  rw [map_pow, map_pow] at hdiv
  have hdivAdd := congrArg Multiplicative.toAdd hdiv
  change n • Multiplicative.toAdd
      (fractionalIdealDivisorMulEquiv (R := R) (K := K) I) =
    n • Multiplicative.toAdd
      (fractionalIdealDivisorMulEquiv (R := R) (K := K) J) at hdivAdd
  apply Multiplicative.toAdd.injective
  exact nsmul_right_injective (NeZero.ne n) hdivAdd

theorem rootIdealHom_preSelmerEquivOfRingEquiv
    (n : ℕ) [NeZero n] (g : R ≃+* R)
    (x : preSelmer (R := R) (K := K) n) :
    rootIdealHom (R := R) (K := K) n
        (preSelmerEquivOfRingEquiv (R := R) (K := K) n g x) =
      fractionalIdealUnitEquivOfRingEquiv (R := R) (K := K) g
        (rootIdealHom (R := R) (K := K) n x) := by
  apply fractionalIdeal_pow_injective (R := R) (K := K) n
  change rootIdealHom (R := R) (K := K) n
      (preSelmerEquivOfRingEquiv (R := R) (K := K) n g x) ^ n =
    (fractionalIdealUnitEquivOfRingEquiv (R := R) (K := K) g
      (rootIdealHom (R := R) (K := K) n x)) ^ n
  rw [rootIdealHom_pow]
  rw [← map_pow, rootIdealHom_pow,
    fractionalIdealUnitEquivOfRingEquiv_toPrincipalIdeal]
  rfl

omit [IsDedekindDomain R] in
theorem map_powRange_fieldUnitEquivOfRingEquiv
    (n : ℕ) (g : R ≃+* R) :
    Subgroup.map
        (fieldUnitEquivOfRingEquiv (R := R) (K := K) g).toMonoidHom
        (powMonoidHom n : Kˣ →* Kˣ).range =
      (powMonoidHom n : Kˣ →* Kˣ).range := by
  ext z
  constructor
  · rintro ⟨w, ⟨a, ha⟩, rfl⟩
    refine ⟨fieldUnitEquivOfRingEquiv (R := R) (K := K) g a, ?_⟩
    rw [← ha]
    change fieldUnitEquivOfRingEquiv (R := R) (K := K) g a ^ n =
      fieldUnitEquivOfRingEquiv (R := R) (K := K) g (a ^ n)
    exact (map_pow (fieldUnitEquivOfRingEquiv
      (R := R) (K := K) g) a n).symm
  · rintro ⟨a, rfl⟩
    refine ⟨(fieldUnitEquivOfRingEquiv (R := R) (K := K) g).symm a ^ n,
      ⟨(fieldUnitEquivOfRingEquiv (R := R) (K := K) g).symm a, rfl⟩, ?_⟩
    change fieldUnitEquivOfRingEquiv (R := R) (K := K) g
      ((fieldUnitEquivOfRingEquiv (R := R) (K := K) g).symm a ^ n) = a ^ n
    rw [map_pow, MulEquiv.apply_symm_apply]

/-- The automorphism of field units modulo `n`-th powers induced by a
base-ring automorphism. -/
noncomputable def fieldUnitQuotientEquivOfRingEquiv
    (n : ℕ) (g : R ≃+* R) :
    (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ≃*
      (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :=
  QuotientGroup.congr _ _
    (fieldUnitEquivOfRingEquiv (R := R) (K := K) g)
    (map_powRange_fieldUnitEquivOfRingEquiv
      (R := R) (K := K) n g)

omit [IsDedekindDomain R] in
@[simp]
theorem fieldUnitQuotientEquivOfRingEquiv_mk
    (n : ℕ) (g : R ≃+* R) (x : Kˣ) :
    fieldUnitQuotientEquivOfRingEquiv (R := R) (K := K) n g
        (QuotientGroup.mk x) =
      QuotientGroup.mk
        (fieldUnitEquivOfRingEquiv (R := R) (K := K) g x) := by
  rfl

theorem fieldUnitQuotientEquivOfRingEquiv_mem_selmerGroup
    (n : ℕ) [NeZero n] (g : R ≃+* R)
    (q : selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) :
    fieldUnitQuotientEquivOfRingEquiv (R := R) (K := K) n g
        (q : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) := by
  obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective
    (R := R) (K := K) n q
  rw [show (preSelmerToSelmer (R := R) (K := K) n x :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (x : Kˣ) from rfl,
    fieldUnitQuotientEquivOfRingEquiv_mk]
  exact (preSelmerEquivOfRingEquiv (R := R) (K := K) n g x).property

theorem map_selmerGroup_fieldUnitQuotientEquivOfRingEquiv
    (n : ℕ) [NeZero n] (g : R ≃+* R) :
    Subgroup.map
        (fieldUnitQuotientEquivOfRingEquiv
          (R := R) (K := K) n g).toMonoidHom
        (selmerGroup (R := R) (K := K)
          (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) =
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) := by
  apply le_antisymm
  · rintro q ⟨a, ha, rfl⟩
    exact fieldUnitQuotientEquivOfRingEquiv_mem_selmerGroup
      (R := R) (K := K) n g ⟨a, ha⟩
  · intro q hq
    let qs : selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) := ⟨q, hq⟩
    obtain ⟨x, hx⟩ := preSelmerToSelmer_surjective
      (R := R) (K := K) n qs
    let y := preSelmerEquivOfRingEquiv (R := R) (K := K) n g.symm x
    refine ⟨(preSelmerToSelmer (R := R) (K := K) n y :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range),
      (preSelmerToSelmer (R := R) (K := K) n y).property, ?_⟩
    change fieldUnitQuotientEquivOfRingEquiv (R := R) (K := K) n g
      (preSelmerToSelmer (R := R) (K := K) n y :
        Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = q
    rw [show (preSelmerToSelmer (R := R) (K := K) n y :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (y : Kˣ) from rfl,
      fieldUnitQuotientEquivOfRingEquiv_mk]
    change QuotientGroup.mk
      (fieldUnitEquivOfRingEquiv (R := R) (K := K) g
        (fieldUnitEquivOfRingEquiv (R := R) (K := K) g.symm (x : Kˣ))) = q
    have hunit : fieldUnitEquivOfRingEquiv (R := R) (K := K) g
        (fieldUnitEquivOfRingEquiv (R := R) (K := K) g.symm (x : Kˣ)) =
      (x : Kˣ) := by
      apply Units.ext
      exact RingEquiv.apply_symm_apply
        (IsFractionRing.ringEquivOfRingEquiv
          (K := K) (L := K) g) (((x : Kˣ) : K))
    rw [hunit]
    exact congrArg Subtype.val hx

/-- The automorphism of the empty-support Selmer group induced by a
base-ring automorphism. -/
noncomputable def selmerEquivOfRingEquiv
    (n : ℕ) [NeZero n] (g : R ≃+* R) :
    selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) ≃*
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) :=
  ((fieldUnitQuotientEquivOfRingEquiv
    (R := R) (K := K) n g).subgroupMap
      (selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n))).trans
    (MulEquiv.subgroupCongr
      (map_selmerGroup_fieldUnitQuotientEquivOfRingEquiv
        (R := R) (K := K) n g))

@[simp]
theorem selmerEquivOfRingEquiv_coe
    (n : ℕ) [NeZero n] (g : R ≃+* R)
    (q : selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) :
    (selmerEquivOfRingEquiv (R := R) (K := K) n g q :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
    fieldUnitQuotientEquivOfRingEquiv (R := R) (K := K) n g q := by
  rfl

@[simp]
theorem selmerEquivOfRingEquiv_preSelmerToSelmer
    (n : ℕ) [NeZero n] (g : R ≃+* R)
    (x : preSelmer (R := R) (K := K) n) :
    selmerEquivOfRingEquiv (R := R) (K := K) n g
        (preSelmerToSelmer (R := R) (K := K) n x) =
      preSelmerToSelmer (R := R) (K := K) n
        (preSelmerEquivOfRingEquiv (R := R) (K := K) n g x) := by
  apply Subtype.ext
  change fieldUnitQuotientEquivOfRingEquiv (R := R) (K := K) n g
      (QuotientGroup.mk (x : Kˣ)) =
    QuotientGroup.mk
      (fieldUnitEquivOfRingEquiv (R := R) (K := K) g (x : Kˣ))
  exact fieldUnitQuotientEquivOfRingEquiv_mk
    (R := R) (K := K) n g (x : Kˣ)

/-- The Selmer-to-class-group homomorphism is natural under base-ring
automorphisms. -/
theorem classGroupEquiv_toClassGroup
    (n : ℕ) [NeZero n] (g : R ≃+* R)
    (q : selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) :
    classGroupEquiv R K g
        (toClassGroup (R := R) (K := K) n q) =
      toClassGroup (R := R) (K := K) n
        (selmerEquivOfRingEquiv (R := R) (K := K) n g q) := by
  obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective
    (R := R) (K := K) n q
  rw [selmerEquivOfRingEquiv_preSelmerToSelmer,
    toClassGroup_preSelmerToSelmer,
    toClassGroup_preSelmerToSelmer]
  change classGroupEquiv R K g
      (ClassGroup.mk K
        (rootIdealHom (R := R) (K := K) n x)) =
    ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n
        (preSelmerEquivOfRingEquiv (R := R) (K := K) n g x))
  rw [classGroupEquiv_mk,
    rootIdealHom_preSelmerEquivOfRingEquiv]
  rfl

end

end IsDedekindDomain.selmerGroup
