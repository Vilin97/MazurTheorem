/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import EllipticCurves.Mathlib.Basic
import MazurTorsion.NumberTheory.SelmerClassGroup

/-!
# Cardinality bookkeeping for the `X₁(18)` two-descent

This file supplies the finite-group bookkeeping which turns checked global
square-class data into the cardinalities used by the `X₁(18)` descent.  It
uses the valuation map already attached to a Dedekind Selmer group and the
unit--Selmer--class-group exact sequence from
`MazurTorsion.NumberTheory.SelmerClassGroup`.

There is deliberately no arithmetic oracle here.  The concrete theorem at
the end consumes three independently checkable certificates:

* the cardinality of integral-unit square classes;
* surjectivity of the supported valuation map;
* a splitting of the norm on square classes.

It then proves, rather than assumes, finiteness of every group involved and
the numerical conclusions `256` and `16`.
-/

open IsDedekindDomain

namespace EllipticCurves.X18SelmerCardinality

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Explicit unit-parity certificates -/

/-- Six independent parity coordinates on integral units.  This is the
weakest raw-unit certificate needed by the cardinality argument: unlike an
assumed cardinality, both surjectivity and the square-kernel identity can be
verified on explicit units. -/
abbrev UnitParityTarget :=
  Multiplicative (ZMod 2) × (Fin 5 → Multiplicative (ZMod 2))

structure UnitParityCertificate (R : Type u) [CommRing R] where
  parity : Rˣ →* UnitParityTarget
  surjective : Function.Surjective parity
  ker_eq_squares : parity.ker = (powMonoidHom 2 : Rˣ →* Rˣ).range

/-- The explicit abstract shape `μ₂ × ℤ⁵` of the unit group used by the
X18 certificate. -/
abbrev UnitDecompositionTarget :=
  Multiplicative (ZMod 2) × (Fin 5 → Multiplicative ℤ)

/-- Reduction modulo two on a multiplicative copy of `ℤ`. -/
def intParity : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))

/-- Coordinatewise reduction modulo two on `ℤ⁵`. -/
def freeUnitParity :
    (Fin 5 → Multiplicative ℤ) →* (Fin 5 → Multiplicative (ZMod 2)) where
  toFun z i := intParity (z i)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/-- Parity on `μ₂ × ℤ⁵`: the `μ₂` coordinate is retained and the
five free coordinates are reduced modulo two. -/
def decompositionParity :
    UnitDecompositionTarget →*
      (Multiplicative (ZMod 2) × (Fin 5 → Multiplicative (ZMod 2))) :=
  (MonoidHom.id (Multiplicative (ZMod 2))).prodMap freeUnitParity

private lemma decompositionParity_surjective :
    Function.Surjective decompositionParity := by
  rintro ⟨a, b⟩
  let z : Fin 5 → Multiplicative ℤ :=
    fun i ↦ Multiplicative.ofAdd (b i).toAdd.val
  refine ⟨⟨a, z⟩, ?_⟩
  apply Prod.ext
  · rfl
  · funext i
    apply Multiplicative.toAdd.injective
    simp [decompositionParity, freeUnitParity, intParity, z]

private lemma decompositionParity_sq (z : UnitDecompositionTarget) :
    decompositionParity (z ^ 2) = 1 := by
  change (z.1 ^ 2, fun i ↦ intParity ((z.2 i) ^ 2)) =
    (1, fun _ ↦ 1)
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    simp only [pow_two, toAdd_mul, toAdd_one]
    change z.1.toAdd + z.1.toAdd = 0
    exact CharTwo.add_self_eq_zero (z.1.toAdd)
  · funext i
    apply Multiplicative.toAdd.injective
    simp only [pow_two, toAdd_one]
    change (((z.2 i).toAdd + (z.2 i).toAdd : ℤ) : ZMod 2) = 0
    rw [Int.cast_add]
    exact CharTwo.add_self_eq_zero _

/-- An explicit unit decomposition `Rˣ ≃ μ₂ × ℤ⁵` canonically
produces the six-coordinate parity certificate. -/
noncomputable def UnitParityCertificate.ofDecomposition
    (e : Rˣ ≃* UnitDecompositionTarget) : UnitParityCertificate R where
  parity := decompositionParity.comp e.toMonoidHom
  surjective := decompositionParity_surjective.comp e.surjective
  ker_eq_squares := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hu
      have hfirst : (e u).1 = 1 := by
        have h := congrArg Prod.fst hu
        simpa [decompositionParity] using h
      have heven (i : Fin 5) : Even ((e u).2 i).toAdd := by
        rw [← ZMod.intCast_eq_zero_iff_even]
        have h := congrArg (fun z ↦ Multiplicative.toAdd (z.2 i)) hu
        simpa [decompositionParity, freeUnitParity, intParity] using h
      choose r hr using heven
      let w : UnitDecompositionTarget :=
        ⟨1, fun i ↦ Multiplicative.ofAdd (r i)⟩
      refine ⟨e.symm w, ?_⟩
      apply e.injective
      simp only [powMonoidHom_apply]
      rw [map_pow, e.apply_symm_apply]
      apply Prod.ext
      · change (1 : Multiplicative (ZMod 2)) ^ 2 = (e u).1
        simp [hfirst]
      · funext i
        apply Multiplicative.toAdd.injective
        simp only [w, pow_two, Prod.snd_mul, Pi.mul_apply, toAdd_mul,
          toAdd_ofAdd]
        exact (hr i).symm
    · rintro ⟨w, rfl⟩
      simp only [powMonoidHom_apply, MonoidHom.comp_apply, map_pow]
      rw [← map_pow]
      exact decompositionParity_sq (e w)

/-- The squareclass equivalence certified by six raw-unit parity
coordinates. -/
noncomputable def UnitParityCertificate.squareclassEquiv
    (C : UnitParityCertificate R) :
    Units.modPow R 2 ≃* UnitParityTarget :=
  QuotientGroup.liftEquiv
    (powMonoidHom 2 : Rˣ →* Rˣ).range C.surjective
    C.ker_eq_squares.symm

omit [IsDedekindDomain R] in
/-- A checked six-coordinate unit-parity certificate gives exactly `64`
integral-unit square classes. -/
theorem UnitParityCertificate.natCard_unitsModSq
    (C : UnitParityCertificate R) : Nat.card (Units.modPow R 2) = 64 := by
  rw [Nat.card_congr C.squareclassEquiv.toEquiv, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fun,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  norm_num

private lemma finite_emptySelmer_of_finite_units
    (n : ℕ) [Fact (0 < n)] [NeZero n]
    [Subsingleton (ClassGroup R)] [Finite (Units.modPow R n)] :
    Finite (selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) := by
  let ι := @selmerGroup.fromUnitLift R _ _ K _ _ _ n _
  have hι : Function.Bijective ι := by
    refine ⟨selmerGroup.fromUnitLift_injective (R := R) (K := K), ?_⟩
    intro q
    have hq : q ∈ (selmerGroup.toClassGroup (R := R) (K := K) n).ker := by
      exact MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
    rw [← selmerGroup.fromUnitLift_range_eq_ker
      (R := R) (K := K) n] at hq
    exact hq
  exact Finite.of_surjective ι hι.2

/-- If the class group is trivial, the empty-support Selmer group has the
same cardinality as integral units modulo `n`-th powers.  Finiteness of the
Selmer group is obtained from the displayed unit cardinality, not assumed. -/
theorem natCard_emptySelmer_eq_unitsModPow
    (n : ℕ) [Fact (0 < n)] [NeZero n]
    [Subsingleton (ClassGroup R)] :
    Nat.card (selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) =
      Nat.card (Units.modPow R n) := by
  let ι := @selmerGroup.fromUnitLift R _ _ K _ _ _ n _
  have hι : Function.Bijective ι := by
    refine ⟨selmerGroup.fromUnitLift_injective (R := R) (K := K), ?_⟩
    intro q
    have hq : q ∈ (selmerGroup.toClassGroup (R := R) (K := K) n).ker := by
      exact MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
    rw [← selmerGroup.fromUnitLift_range_eq_ker
      (R := R) (K := K) n] at hq
    exact hq
  exact Nat.card_congr (Equiv.ofBijective ι hι).symm

section Support

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)

abbrev EmptySelmer :=
  selmerGroup (R := R) (K := K)
    (S := (∅ : Set (HeightOneSpectrum R))) (n := n)

abbrev SupportedSelmer :=
  selmerGroup (R := R) (K := K) (S := S) (n := n)

abbrev supportValuation :
    SupportedSelmer (R := R) (K := K) S n →*
      S → Multiplicative (ZMod n) :=
  selmerGroup.valuation

/-- The nontrivial element of the multiplicative copy of `ZMod 2`. -/
def parityOne : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

private lemma eq_one_or_parityOne (z : Multiplicative (ZMod 2)) :
    z = 1 ∨ z = parityOne := by
  cases z with
  | ofAdd z =>
      fin_cases z
      · left
        apply Multiplicative.toAdd.injective
        rfl
      · right
        rfl

/-- Two supported squareclasses whose valuation parities form the identity
matrix generate every two-prime parity vector.  The equivalence `places`
is itself a checked assertion that the support consists of exactly two
primes. -/
theorem supportValuation_surjective_of_two_generators
    (places : Fin 2 ≃ S)
    (g₀ g₁ : SupportedSelmer (R := R) (K := K) S 2)
    (hg₀₀ : supportValuation (R := R) (K := K) S 2 g₀ (places 0) = parityOne)
    (hg₀₁ : supportValuation (R := R) (K := K) S 2 g₀ (places 1) = 1)
    (hg₁₀ : supportValuation (R := R) (K := K) S 2 g₁ (places 0) = 1)
    (hg₁₁ : supportValuation (R := R) (K := K) S 2 g₁ (places 1) = parityOne) :
    Function.Surjective (supportValuation (R := R) (K := K) S 2) := by
  intro y
  rcases eq_one_or_parityOne (y (places 0)) with h₀ | h₀ <;>
    rcases eq_one_or_parityOne (y (places 1)) with h₁ | h₁
  · refine ⟨1, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i <;> simp [h₀, h₁]
  · refine ⟨g₁, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i
    · simp [hg₁₀, h₀]
    · simp [hg₁₁, h₁]
  · refine ⟨g₀, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i
    · simp [hg₀₀, h₀]
    · simp [hg₀₁, h₁]
  · refine ⟨g₀ * g₁, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i
    · calc
        supportValuation (R := R) (K := K) S 2 (g₀ * g₁) (places 0) =
            supportValuation (R := R) (K := K) S 2 g₀ (places 0) *
              supportValuation (R := R) (K := K) S 2 g₁ (places 0) := by
                rw [map_mul, Pi.mul_apply]
        _ = parityOne * 1 := congrArg₂ (fun a b ↦ a * b) hg₀₀ hg₁₀
        _ = parityOne := mul_one _
        _ = y (places 0) := h₀.symm
    · calc
        supportValuation (R := R) (K := K) S 2 (g₀ * g₁) (places 1) =
            supportValuation (R := R) (K := K) S 2 g₀ (places 1) *
              supportValuation (R := R) (K := K) S 2 g₁ (places 1) := by
                rw [map_mul, Pi.mul_apply]
        _ = 1 * parityOne := congrArg₂ (fun a b ↦ a * b) hg₀₁ hg₁₁
        _ = parityOne := one_mul _
        _ = y (places 1) := h₁.symm

private lemma natCard_valuation_ker
    [Finite (EmptySelmer (R := R) (K := K) n)] :
    Nat.card (supportValuation (R := R) (K := K) S n).ker =
      Nat.card (EmptySelmer (R := R) (K := K) n) := by
  let hEmptyS : EmptySelmer (R := R) (K := K) n ≤
      SupportedSelmer (R := R) (K := K) S n :=
    selmerGroup.monotone (Set.empty_subset S)
  rw [selmerGroup.valuation_ker_eq (R := R) (K := K) (S := S) (n := n)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEmptyS).toEquiv

private lemma finite_valuation_ker
    [Finite (EmptySelmer (R := R) (K := K) n)] :
    Finite (supportValuation (R := R) (K := K) S n).ker := by
  rw [selmerGroup.valuation_ker_eq (R := R) (K := K) (S := S) (n := n)]
  let hEmptyS : EmptySelmer (R := R) (K := K) n ≤
      SupportedSelmer (R := R) (K := K) S n :=
    selmerGroup.monotone (Set.empty_subset S)
  exact Finite.of_equiv (EmptySelmer (R := R) (K := K) n)
    (Subgroup.subgroupOfEquivOfLe hEmptyS).symm.toEquiv

/-- Adding finite support `S` multiplies the empty-support Selmer
cardinality by at most `n ^ #S`.  Finiteness of the supported Selmer group
is a consequence of the valuation map and the finite empty-support group. -/
theorem natCard_supportedSelmer_le
    [NeZero n] [Finite S] [Finite (EmptySelmer (R := R) (K := K) n)] :
    Nat.card (SupportedSelmer (R := R) (K := K) S n) ≤
      Nat.card (EmptySelmer (R := R) (K := K) n) * n ^ Nat.card S := by
  let ν := supportValuation (R := R) (K := K) S n
  letI : Finite ν.ker := finite_valuation_ker (R := R) (K := K) S n
  letI : Finite ν.range :=
    Finite.of_injective (fun x : ν.range ↦ (x : S → Multiplicative (ZMod n)))
      Subtype.val_injective
  letI : Finite (SupportedSelmer (R := R) (K := K) S n) :=
    ν.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩
  have hrange : Nat.card ν.range ≤
      Nat.card (S → Multiplicative (ZMod n)) :=
    Nat.card_le_card_of_injective (fun x : ν.range ↦
      (x : S → Multiplicative (ZMod n))) Subtype.val_injective
  calc
    Nat.card (SupportedSelmer (R := R) (K := K) S n)
        = Nat.card ν.ker * Nat.card ν.range := by
            rw [← Subgroup.index_ker ν, ν.ker.card_mul_index]
    _ ≤ Nat.card ν.ker * Nat.card (S → Multiplicative (ZMod n)) :=
      Nat.mul_le_mul_left _ hrange
    _ = Nat.card (EmptySelmer (R := R) (K := K) n) * n ^ Nat.card S := by
      rw [natCard_valuation_ker (R := R) (K := K) S n,
        Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- When all supported valuation classes occur, the support factor is
exactly `n ^ #S`. -/
theorem natCard_supportedSelmer_eq_of_valuation_surjective
    [NeZero n] [Finite S] [Finite (EmptySelmer (R := R) (K := K) n)]
    (hν : Function.Surjective
      (supportValuation (R := R) (K := K) S n)) :
    Nat.card (SupportedSelmer (R := R) (K := K) S n) =
      Nat.card (EmptySelmer (R := R) (K := K) n) * n ^ Nat.card S := by
  let ν := supportValuation (R := R) (K := K) S n
  letI : Finite ν.ker := finite_valuation_ker (R := R) (K := K) S n
  letI : Finite ν.range :=
    Finite.of_injective (fun x : ν.range ↦ (x : S → Multiplicative (ZMod n)))
      Subtype.val_injective
  letI : Finite (SupportedSelmer (R := R) (K := K) S n) :=
    ν.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩
  have hrange : Nat.card ν.range =
      Nat.card (S → Multiplicative (ZMod n)) := by
    rw [MonoidHom.range_eq_top.mpr hν, Subgroup.card_top]
  calc
    Nat.card (SupportedSelmer (R := R) (K := K) S n)
        = Nat.card ν.ker * Nat.card ν.range := by
            rw [← Subgroup.index_ker ν, ν.ker.card_mul_index]
    _ = Nat.card (EmptySelmer (R := R) (K := K) n) *
        Nat.card (S → Multiplicative (ZMod n)) := by
      rw [natCard_valuation_ker (R := R) (K := K) S n, hrange]
    _ = Nat.card (EmptySelmer (R := R) (K := K) n) * n ^ Nat.card S := by
      rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end Support

section SplitNorm

variable {G : Type v} [Group G] {H : Type w} [Group H]

/-- A homomorphism with a right inverse is surjective.  This is the group
theoretic form in which odd-degree restriction/corestriction is used on
square classes. -/
theorem surjective_of_comp_eq_id (N : G →* H) (res : H →* G)
    (hsplit : N.comp res = MonoidHom.id H) : Function.Surjective N := by
  intro h
  refine ⟨res h, ?_⟩
  have := DFunLike.congr_fun hsplit h
  simpa using this

/-- A split quotient of a group of cardinality `256` and cardinality `16`
has kernel of cardinality `16`.  The nonzero cardinality equalities provide
all finiteness instances used in the proof. -/
theorem natCard_ker_eq_sixteen_of_split
    (N : G →* H) (res : H →* G)
    (hsplit : N.comp res = MonoidHom.id H)
    (hG : Nat.card G = 256) (hH : Nat.card H = 16) :
    Nat.card N.ker = 16 := by
  letI : Finite G := Nat.finite_of_card_ne_zero (hG.trans_ne (by norm_num))
  letI : Finite H := Nat.finite_of_card_ne_zero (hH.trans_ne (by norm_num))
  have hsurj : Function.Surjective N := surjective_of_comp_eq_id N res hsplit
  have hrange : Nat.card N.range = Nat.card H :=
    by rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  have hcard : Nat.card N.ker * Nat.card N.range = Nat.card G := by
    rw [← Subgroup.index_ker N]
    exact N.ker.card_mul_index
  rw [hrange, hG, hH] at hcard
  omega

end SplitNorm

section Concrete

variable (S : Set (HeightOneSpectrum R))

/-- The exact cardinality package used by the `X₁(18)` certificate.

The hypotheses are certificate boundaries, not hidden finiteness
assumptions: `hunits` is checked from explicit global square classes,
`hvaluation` from prime generators, and `hsplit` from the odd-degree norm
identity. -/
theorem concrete_twoSelmer_and_splitNorm_kernel
    [Subsingleton (ClassGroup R)]
    (hS : Nat.card S = 2)
    (hunits : Nat.card (Units.modPow R 2) = 64)
    (hvaluation : Function.Surjective
      (supportValuation (R := R) (K := K) S 2))
    {H : Type w} [Group H]
    (N : SupportedSelmer (R := R) (K := K) S 2 →* H)
    (res : H →* SupportedSelmer (R := R) (K := K) S 2)
    (hsplit : N.comp res = MonoidHom.id H)
    (hH : Nat.card H = 16) :
    Nat.card (SupportedSelmer (R := R) (K := K) S 2) = 256 ∧
      Nat.card N.ker = 16 := by
  letI : Finite S := Nat.finite_of_card_ne_zero (hS.trans_ne (by norm_num))
  letI : Fact (0 < (2 : ℕ)) := ⟨by norm_num⟩
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  letI : Finite (Units.modPow R 2) :=
    Nat.finite_of_card_ne_zero (hunits.trans_ne (by norm_num))
  letI : Finite (EmptySelmer (R := R) (K := K) 2) :=
    finite_emptySelmer_of_finite_units (R := R) (K := K) 2
  have hempty : Nat.card (EmptySelmer (R := R) (K := K) 2) = 64 :=
    (natCard_emptySelmer_eq_unitsModPow (R := R) (K := K) 2).trans hunits
  have hsupported : Nat.card (SupportedSelmer (R := R) (K := K) S 2) = 256 := by
    rw [natCard_supportedSelmer_eq_of_valuation_surjective
      (R := R) (K := K) S 2 hvaluation, hempty, hS]
    norm_num
  exact ⟨hsupported,
    natCard_ker_eq_sixteen_of_split N res hsplit hsupported hH⟩

end Concrete

end

end EllipticCurves.X18SelmerCardinality
