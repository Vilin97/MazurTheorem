/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuotientFiniteClassification
import MazurTorsion.NumberTheory.XOneEighteenQuotientMod17
import MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes

/-!
# Reduction of the `X₁(18)` elliptic quotient at a degree-one prime above seventeen

The coefficient cubic `X³ - 3X - 1` has the root `3` modulo `17`.  Kummer--Dedekind,
with the conductor certificate proved in
`XOneEighteenTwoDivisionSmallPrimes`, therefore constructs a genuine prime
of the full ring of integers of the coefficient field whose residue field
is `ZMod 17`.  At that prime the rational-coefficient quotient model has
good reduction and its special fibre has the already checked cardinality
`21`.

Reduction is injective when the source point group is finite: every source
point is then torsion, while the selected prime is unramified.  This gives
the unconditional cardinality divisor needed by
`XOneEighteenQuotientFiniteClassification` once finiteness has been supplied
by the two-descent.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientReductionAtSeventeen

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid
open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientFiniteClassification
open MazurTorsion.XOneEighteenQuotientMod17
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ## The degree-one prime above seventeen -/

/-- The integral lift of the factor corresponding to `τ ↦ 3`. -/
def coefficientLinearFactorInt : Polynomial ℤ := X - C 3

/-- The degree-one factor of the coefficient cubic modulo seventeen. -/
def coefficientLinearFactor : Polynomial (ZMod 17) := X - C 3

theorem coefficientLinearFactorInt_map :
    coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)) =
      coefficientLinearFactor := by
  simp only [coefficientLinearFactorInt, coefficientLinearFactor,
    Polynomial.map_sub, Polynomial.map_X]
  rw [Polynomial.map_C]
  norm_num

private theorem coefficient_not_dvd_exponent_seventeen :
    ¬ 17 ∣ RingOfIntegers.exponent coefficientInteger := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {(81 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (𝓞 K))
        (conductor ℤ coefficientInteger) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact coefficient_discriminant_mem_conductor
  exact ((Ideal.isCoprime_span_singleton_iff (81 : ℤ) 17).mpr
    (by norm_num)).codisjoint.mono_left hspan

theorem coefficientLinearFactor_mem_monicFactors :
    coefficientLinearFactor ∈
      RingOfIntegers.monicFactorsMod coefficientInteger 17 := by
  change coefficientLinearFactor ∈
    (normalizedFactors
      ((minpoly ℤ coefficientInteger).map
        (Int.castRingHom (ZMod 17)))).toFinset
  rw [Multiset.mem_toFinset, coefficientInteger_minpoly,
    coefficientPolynomialInt_map_zmod]
  apply (Polynomial.mem_normalizedFactors_iff (by
    have hmonic : (coefficientPolynomialMod 17).Monic := by
      simp only [coefficientPolynomialMod]
      monicity <;> norm_num
    exact hmonic.ne_zero)).2
  refine ⟨irreducible_X_sub_C 3, monic_X_sub_C 3, ?_⟩
  rw [coefficientLinearFactor, Polynomial.dvd_iff_isRoot]
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  decide

theorem coefficientLinearFactorInt_mem_monicFactors :
    coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)) ∈
      RingOfIntegers.monicFactorsMod coefficientInteger 17 := by
  rw [coefficientLinearFactorInt_map]
  exact coefficientLinearFactor_mem_monicFactors

/-- The Kummer--Dedekind prime selected by the root `τ ↦ 3`. -/
def coefficientPrimeSeventeenIdeal : Ideal (𝓞 K) :=
  (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_seventeen).symm
    ⟨coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)),
      coefficientLinearFactorInt_mem_monicFactors⟩

theorem coefficientPrimeSeventeen_mem_primesOver :
    coefficientPrimeSeventeenIdeal ∈
      Ideal.primesOver (Ideal.span {(17 : ℤ)}) (𝓞 K) :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_seventeen).symm
    ⟨coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)),
      coefficientLinearFactorInt_mem_monicFactors⟩).property

private instance coefficientPrimeSeventeenIdeal_isPrime :
    coefficientPrimeSeventeenIdeal.IsPrime :=
  coefficientPrimeSeventeen_mem_primesOver.1

private instance coefficientPrimeSeventeenIdeal_liesOver :
    coefficientPrimeSeventeenIdeal.LiesOver
      (Ideal.span {(17 : ℤ)}) :=
  coefficientPrimeSeventeen_mem_primesOver.2

/-- The resulting height-one prime of the coefficient-field integers. -/
def coefficientPrimeSeventeen : HeightOneSpectrum (𝓞 K) :=
  .ofPrime (Ideal.prime_of_mem_primesOver
    (by norm_num) coefficientPrimeSeventeen_mem_primesOver)

@[simp] theorem coefficientPrimeSeventeen_asIdeal :
    coefficientPrimeSeventeen.asIdeal = coefficientPrimeSeventeenIdeal :=
  rfl

theorem coefficientPrimeSeventeenIdeal_eq_span :
    coefficientPrimeSeventeenIdeal =
      Ideal.span {(17 : 𝓞 K),
        Polynomial.aeval coefficientInteger coefficientLinearFactorInt} := by
  exact NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    coefficient_not_dvd_exponent_seventeen
    coefficientLinearFactorInt_mem_monicFactors

/-! ## The residue field -/

/-- The residue field of the selected coefficient-field prime is `F₁₇`. -/
noncomputable def residueSeventeenRingEquiv :
    (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal) ≃+* ZMod 17 :=
  (Ideal.quotEquivOfEq coefficientPrimeSeventeen_asIdeal).trans <|
    (Ideal.quotEquivOfEq coefficientPrimeSeventeenIdeal_eq_span).trans <|
      (RingOfIntegers.ZModXQuotSpanEquivQuotSpanPair
          coefficient_not_dvd_exponent_seventeen
          coefficientLinearFactorInt_mem_monicFactors).symm.trans <|
        (Ideal.quotEquivOfEq (congrArg (fun f ↦ Ideal.span {f})
          coefficientLinearFactorInt_map)).trans <|
          (Polynomial.quotientSpanXSubCAlgEquiv
            (3 : ZMod 17)).toRingEquiv

/-- The residue equivalence, with its canonical integer-algebra structure. -/
noncomputable def residueSeventeenAlgEquiv :
    (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal) ≃ₐ[ℤ] ZMod 17 :=
  AlgEquiv.ofRingEquiv (f := residueSeventeenRingEquiv) fun z ↦ by
    exact map_intCast residueSeventeenRingEquiv z

/-- Under the residue-field identification, the coefficient-field
generator specializes to the chosen root `3`. -/
theorem residueSeventeen_coefficientInteger :
    residueSeventeenAlgEquiv
        (Ideal.Quotient.mk coefficientPrimeSeventeen.asIdeal
          coefficientInteger) = 3 := by
  have hgenerator :
      Polynomial.aeval coefficientInteger coefficientLinearFactorInt ∈
        coefficientPrimeSeventeenIdeal := by
    rw [coefficientPrimeSeventeenIdeal_eq_span]
    exact Ideal.subset_span (by simp)
  have hsub : coefficientInteger - 3 ∈
      coefficientPrimeSeventeen.asIdeal := by
    rw [coefficientPrimeSeventeen_asIdeal]
    simpa only [coefficientLinearFactorInt, aeval_sub, aeval_X,
      aeval_C, map_ofNat] using hgenerator
  have hquot :
      Ideal.Quotient.mk coefficientPrimeSeventeen.asIdeal
          coefficientInteger =
        Ideal.Quotient.mk coefficientPrimeSeventeen.asIdeal 3 := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hsub
  rw [hquot]
  exact map_ofNat residueSeventeenAlgEquiv 3

noncomputable instance coefficientResidueSeventeen_decidableEq :
    DecidableEq (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal) :=
  residueSeventeenAlgEquiv.toEquiv.decidableEq

/-! ## Unramifiedness at the selected prime -/

private theorem coefficientPolynomialMod_seventeen_ne_zero :
    coefficientPolynomialMod 17 ≠ 0 := by
  have hmonic : (coefficientPolynomialMod 17).Monic := by
    simp only [coefficientPolynomialMod]
    monicity <;> norm_num
  exact hmonic.ne_zero

theorem coefficientLinearFactor_multiplicity :
    multiplicity coefficientLinearFactor (coefficientPolynomialMod 17) = 1 := by
  have hroot : Polynomial.IsRoot (coefficientPolynomialMod 17) (3 : ZMod 17) := by
    unfold Polynomial.IsRoot
    simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
      eval_mul, eval_ofNat, eval_one]
    decide
  have hderivative :
      ¬ Polynomial.IsRoot (derivative (coefficientPolynomialMod 17))
        (3 : ZMod 17) := by
    norm_num [Polynomial.IsRoot, coefficientPolynomialMod,
      derivative_sub, derivative_pow, derivative_X, derivative_mul,
      derivative_ofNat, derivative_one]
    decide
  have hpos :
      0 < (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) :=
    (Polynomial.rootMultiplicity_pos coefficientPolynomialMod_seventeen_ne_zero).2 hroot
  have hle :
      (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) ≤ 1 := by
    by_contra h
    have hgt : 1 <
        (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) := by
      omega
    exact hderivative
      ((Polynomial.one_lt_rootMultiplicity_iff_isRoot
        coefficientPolynomialMod_seventeen_ne_zero).mp hgt).2
  have hrootMultiplicity :
      (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) = 1 := by
    omega
  have hm := Polynomial.rootMultiplicity_eq_multiplicity
    (coefficientPolynomialMod 17) (3 : ZMod 17)
  rw [if_neg coefficientPolynomialMod_seventeen_ne_zero] at hm
  rw [coefficientLinearFactor]
  exact hm.symm.trans hrootMultiplicity

/-- The selected degree-one prime is unramified over seventeen. -/
theorem coefficientPrimeSeventeen_ramificationIdx :
    coefficientPrimeSeventeenIdeal.ramificationIdx ℤ = 1 := by
  rw [coefficientPrimeSeventeenIdeal]
  rw [NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
    coefficient_not_dvd_exponent_seventeen
    coefficientLinearFactorInt_mem_monicFactors]
  rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod,
    coefficientLinearFactorInt_map]
  exact coefficientLinearFactor_multiplicity

/-- The ramification bound required by the exact-pin formal-kernel theorem. -/
theorem seventeen_not_mem_prime_pow_sixteen :
    (17 : 𝓞 K) ∉ coefficientPrimeSeventeen.asIdeal ^ (17 - 1) := by
  rw [show 17 - 1 = 16 by norm_num, coefficientPrimeSeventeen_asIdeal]
  intro hmem
  have hdvd : coefficientPrimeSeventeenIdeal ^ 16 ∣
      Ideal.span {(17 : 𝓞 K)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hspan_ne : Ideal.span {(17 : 𝓞 K)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using
      (show (17 : 𝓞 K) ≠ 0 by norm_num)
  have hfinite : FiniteMultiplicity coefficientPrimeSeventeenIdeal
      (Ideal.span {(17 : 𝓞 K)}) :=
    FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_mem_primesOver (by norm_num)
        coefficientPrimeSeventeen_mem_primesOver) hspan_ne
  have hle : 16 ≤ multiplicity coefficientPrimeSeventeenIdeal
      (Ideal.span {(17 : 𝓞 K)}) :=
    hfinite.le_multiplicity_of_pow_dvd hdvd
  have hmap :
      (Ideal.span {(17 : ℤ)}).map (algebraMap ℤ (𝓞 K)) =
        Ideal.span {(17 : 𝓞 K)} := by
    simp [Ideal.map_span]
  have hram := IsDedekindDomain.ramificationIdx_eq_multiplicity
    (Ideal.span {(17 : ℤ)}) coefficientPrimeSeventeenIdeal
    (map_ne_bot_of_ne_bot (by norm_num))
  rw [hmap, coefficientPrimeSeventeen_ramificationIdx] at hram
  omega

/-! ## Integral model and good reduction -/

/-- The rational-coefficient integral model, base changed to the full ring
of integers of the coefficient cubic. -/
def integralRationalModelK : WeierstrassCurve (𝓞 K) :=
  integralRationalModel.map (algebraMap ℤ (𝓞 K))

/-- Its generic fibre is the rational-coefficient quotient model. -/
theorem integralRationalModelK_map_K :
    integralRationalModelK.map (algebraMap (𝓞 K) K) =
      rationalModel := by
  rw [integralRationalModelK, WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq ℤ (𝓞 K) K]
  exact integralRationalModel_map_K

theorem integralRationalModelK_discriminant :
    integralRationalModelK.Δ = (-1062882 : 𝓞 K) := by
  rw [integralRationalModelK, WeierstrassCurve.map_Δ,
    integralRationalModel_discriminant]
  norm_num

/-- The chosen integral model has good reduction at the degree-one prime. -/
instance integralRationalModelK_red_isElliptic :
    (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
      integralRationalModelK).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (integralRationalModelK.map
      (algebraMap (𝓞 K)
        (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal))).Δ ≠ 0
  rw [WeierstrassCurve.map_Δ, integralRationalModelK_discriminant]
  rw [Ne, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem, coefficientPrimeSeventeen_asIdeal]
  intro hmem
  have hbase : (-1062882 : ℤ) ∈ Ideal.span {(17 : ℤ)} := by
    rw [coefficientPrimeSeventeenIdeal.over_def
      (Ideal.span {(17 : ℤ)})]
    change algebraMap ℤ (𝓞 K) (-1062882 : ℤ) ∈
      coefficientPrimeSeventeenIdeal
    simpa using hmem
  rw [Ideal.mem_span_singleton] at hbase
  norm_num at hbase

private theorem integralRationalModelK_map_K_affine :
    (integralRationalModelK.map (algebraMap (𝓞 K) K)).toAffine =
      rationalModel.toAffine := by
  rw [integralRationalModelK_map_K]

/-! ## Identification and cardinality of the special fibre -/

private theorem redCurve_eq_integerBaseChange :
    WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK =
      ((integralRationalModel.toAffine ⁄
          (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal)) :
        WeierstrassCurve _).toAffine := by
  change
    (integralRationalModel.map (algebraMap ℤ (𝓞 K))).map
        (algebraMap (𝓞 K)
          (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal)) =
      integralRationalModel.map
        (algebraMap ℤ
          (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal))
  rw [WeierstrassCurve.map_map,
    IsScalarTower.algebraMap_eq ℤ (𝓞 K)
      (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal)]

private theorem integerBaseChange_modSeventeen :
    ((integralRationalModel.toAffine ⁄ (ZMod 17)) :
      WeierstrassCurve _).toAffine =
        rationalModelModSeventeen.toAffine := by
  ext <;> decide +kernel

/-- The special fibre over the selected coefficient-field prime is the
concrete 21-point curve over `F₁₇`. -/
noncomputable def reducedPointEquiv :
    (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK).Point ≃+
      rationalModelModSeventeen.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.congr redCurve_eq_integerBaseChange).trans <|
    (WeierstrassCurve.Affine.Point.mapEquiv
      (W' := integralRationalModel.toAffine)
      residueSeventeenAlgEquiv).trans <|
        WeierstrassCurve.Affine.Point.congr integerBaseChange_modSeventeen

noncomputable instance reducedPoint_finite :
    Finite (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
      integralRationalModelK).Point :=
  .of_equiv rationalModelModSeventeen.toAffine.Point
    reducedPointEquiv.symm.toEquiv

/-- The special fibre at the selected degree-one prime has 21 points. -/
theorem card_reducedCurve_seventeen :
    Nat.card (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
      integralRationalModelK).Point = 21 := by
  calc
    Nat.card (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK).Point =
        Fintype.card rationalModelModSeventeen.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 21 := card_rationalModelModSeventeen

/-! ## Injective reduction of a finite quotient point group -/

theorem seventeen_mem_prime :
    (17 : 𝓞 K) ∈ coefficientPrimeSeventeen.asIdeal := by
  rw [coefficientPrimeSeventeen_asIdeal]
  change algebraMap ℤ (𝓞 K) (17 : ℤ) ∈ coefficientPrimeSeventeenIdeal
  rw [← Ideal.mem_of_liesOver (P := coefficientPrimeSeventeenIdeal)
    (p := Ideal.span {(17 : ℤ)})]
  exact Ideal.mem_span_singleton_self 17

/-- Reduction on the rational-coefficient model. -/
noncomputable def rationalModelReduction :
    rationalModel.toAffine.Point →+
      (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK).Point :=
  WeierstrassCurve.Affine.redHom coefficientPrimeSeventeen
    integralRationalModelK_map_K_affine

/-- At the unramified prime above seventeen, reduction is injective when
the source point group is finite. -/
theorem rationalModelReduction_injective
    [Finite rationalModel.toAffine.Point] :
    Function.Injective rationalModelReduction := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  have hred :
      WeierstrassCurve.Affine.red coefficientPrimeSeventeen
          integralRationalModelK_map_K_affine (P - Q) = 0 := by
    change rationalModelReduction (P - Q) = 0
    rw [map_sub, hPQ, sub_self]
  exact WeierstrassCurve.Affine.eq_zero_of_isOfFinAddOrder_of_red_eq_zero
    coefficientPrimeSeventeen integralRationalModelK_map_K_affine
    (by norm_num) seventeen_mem_prime
    seventeen_not_mem_prime_pow_sixteen
    (isOfFinAddOrder_of_finite (P - Q)) hred

/-- Reduction of the original real-cubic quotient, transported through the
checked admissible change to the rational-coefficient model. -/
noncomputable def quotientReduction :
    quotientCurve.toAffine.Point →+
      (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK).Point :=
  rationalModelReduction.comp
    MazurTorsion.XOneEighteenQuotientTwoDescentModel.quotientToRationalEquiv.toAddMonoidHom

theorem quotientReduction_injective
    [Finite quotientCurve.toAffine.Point] :
    Function.Injective quotientReduction := by
  letI : Finite rationalModel.toAffine.Point :=
    Finite.of_equiv quotientCurve.toAffine.Point
      MazurTorsion.XOneEighteenQuotientTwoDescentModel.quotientToRationalEquiv.toEquiv
  exact rationalModelReduction_injective.comp
    MazurTorsion.XOneEighteenQuotientTwoDescentModel.quotientToRationalEquiv.injective

/-- The finite quotient point group has cardinality dividing the 21-point
special fibre. -/
theorem quotient_point_card_dvd_twentyOne
    [Finite quotientCurve.toAffine.Point] :
    Nat.card quotientCurve.toAffine.Point ∣ 21 := by
  rw [← card_reducedCurve_seventeen]
  exact AddSubgroup.card_dvd_of_injective quotientReduction
    quotientReduction_injective

/-- The genuine finite-reduction consumer: once the two-descent supplies
finiteness, the checked 21-point reduction and finite-group classification
exclude every noncuspidal rational point. -/
theorem no_noncuspidal_point_of_finite_quotient
    [Finite quotientCurve.toAffine.Point]
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 = MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False :=
  no_noncuspidal_point_of_point_card_dvd_twentyOne
    quotient_point_card_dvd_twentyOne x y hx0 hx1 hcurve

end

end MazurTorsion.XOneEighteenQuotientReductionAtSeventeen
