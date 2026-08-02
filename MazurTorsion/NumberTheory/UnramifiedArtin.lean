/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The unramified ideal Artin map

This file develops the part of the ideal-theoretic Artin map that follows from
Dedekind factorization and local Frobenius theory.  For a finite Galois
extension of number fields it chooses a prime above every finite prime and
defines the corresponding arithmetic Frobenius.  In an abelian extension the
choice disappears, since Frobenius elements above the same prime are
conjugate.  The local symbols then extend uniquely to a homomorphism from the
group of nonzero fractional ideals.

The construction here is deliberately separate from global reciprocity.  The
two global assertions needed later are that principal ideals lie in the
kernel, and that the resulting Artin map is onto.  Neither assertion is used
in this file.

The divisor equivalence below is the scheme-free Dedekind-domain core of the
construction in Tau Ceti's
`AlgebraicGeometry/WeilDivisor/FractionalIdealDivisor/Basic.lean`; it is
reproved here directly from Mathlib's fractional-ideal factorization API so
this number-theory module does not depend on Picard or Weil-divisor theory.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped IsMulCommutative NumberField nonZeroDivisors Pointwise

namespace NumberTheory.UnramifiedArtin

attribute [local instance] Ideal.Quotient.field

universe u v w w'

/-- A finite prime of a number field, represented by a nonzero prime ideal in
its ring of integers. -/
abbrev FinitePrime (K : Type*) [Field K] :=
  HeightOneSpectrum (NumberField.RingOfIntegers K)

section LocalDecompositionGroup

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [IsGaloisGroup G R S] [IsDomain R] [IsDomain S]
variable [Module.Finite R S] [Module.Flat R S]

/-- At an unramified prime, an arithmetic Frobenius generates the full
decomposition group. -/
theorem stabilizer_eq_zpowers_of_isArithFrobAt
    (p : Ideal R) (Q : Ideal S) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
    [Finite (S ⧸ Q)] [PerfectField p.ResidueField]
    [Algebra.IsUnramifiedAt R Q]
    {σ : G} (hσ : IsArithFrobAt R σ Q) :
    Subgroup.zpowers σ = MulAction.stabilizer G Q := by
  let g : MulAction.stabilizer G Q :=
    ⟨σ, IsArithFrobAt.mem_stabilizer hσ⟩
  haveI : Q.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _
      (Finite.isField_of_domain (S ⧸ Q))
  haveI : Finite (R ⧸ p) := by
    rw [Q.over_def p]
    exact hσ.finite_quotient
  haveI : p.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _
      (Finite.isField_of_domain (R ⧸ p))
  letI : Fintype (R ⧸ p) := Fintype.ofFinite (R ⧸ p)
  letI : Fintype (S ⧸ Q) := Fintype.ofFinite (S ⧸ Q)
  have hfrob : Ideal.Quotient.stabilizerHom Q p G g =
      FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ Q) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk Q
      ((MulSemiringAction.toAlgHom R S σ) x) = _
    rw [hσ.mk_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      ← Q.over_def p, Nat.card_eq_fintype_card]
  have hker : Function.Injective
      (Ideal.Quotient.stabilizerHom Q p G) := by
    rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
    apply Subgroup.card_eq_one.mp
    calc
      Nat.card (Q.inertia (MulAction.stabilizer G Q)) =
          Nat.card (Q.inertia G) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (Ideal.inertia_le_stabilizer (M := G) Q)).toEquiv
      _ = p.ramificationIdxIn S :=
        Ideal.card_inertia_eq_ramificationIdxIn p Q
      _ = Q.ramificationIdx R :=
        Ideal.ramificationIdxIn_eq_ramificationIdx p Q G
      _ = 1 := Ideal.ramificationIdx_eq_one Q R
  have horder : orderOf g = Q.inertiaDeg R := by
    rw [← orderOf_injective (Ideal.Quotient.stabilizerHom Q p G) hker g,
      hfrob, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact (Ideal.inertiaDeg_eq_of_isMaximal p Q).symm
  have hcard : Nat.card (MulAction.stabilizer G Q) = Q.inertiaDeg R := by
    rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank p Q,
      Ideal.card_inertia_eq_ramificationIdxIn p Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx p Q G,
      Ideal.ramificationIdx_eq_one Q R, one_mul]
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (MulAction.stabilizer G Q).zpow_mem g.2 n
  · rw [Nat.card_zpowers, hcard, ← horder, ← orderOf_submonoid g]

end LocalDecompositionGroup

section Frobenius

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- An arbitrary prime of `L` above the finite prime `v` of `K`. -/
noncomputable def primeAbove (v : FinitePrime K) :
    Ideal.primesOver v.asIdeal (NumberField.RingOfIntegers L) :=
  Classical.choice v.asIdeal.nonempty_primesOver

/-- The chosen arithmetic Frobenius at a finite prime of the base number
field. -/
noncomputable def frobeniusAt (v : FinitePrime K) : Gal(L/K) :=
  arithFrobAt (S := NumberField.RingOfIntegers L)
    (NumberField.RingOfIntegers K) Gal(L/K)
    (primeAbove (K := K) (L := L) v).1

/-- The chosen element really is an arithmetic Frobenius at the chosen prime
above `v`. -/
theorem frobeniusAt_isArithFrobAt (v : FinitePrime K) :
    IsArithFrobAt (NumberField.RingOfIntegers K)
      (frobeniusAt (K := K) (L := L) v)
      (primeAbove (K := K) (L := L) v).1 :=
  IsArithFrobAt.arithFrobAt (S := NumberField.RingOfIntegers L)
    (NumberField.RingOfIntegers K) Gal(L/K)
    (primeAbove (K := K) (L := L) v).1

/-- In an abelian extension, the Frobenius at `v` is independent of the prime
of `L` chosen above `v`. -/
theorem frobeniusAt_eq_arithFrobAt [IsMulCommutative Gal(L/K)]
    (v : FinitePrime K)
    (Q : Ideal.primesOver v.asIdeal (NumberField.RingOfIntegers L)) :
    frobeniusAt (K := K) (L := L) v =
      arithFrobAt (NumberField.RingOfIntegers K) Gal(L/K) Q.1 := by
  apply isConj_iff_eq.mp
  apply isConj_arithFrobAt (R := NumberField.RingOfIntegers K)
    (S := NumberField.RingOfIntegers L)
  rw [← Ideal.over_def (p := v.asIdeal)
      (P := (primeAbove (K := K) (L := L) v).1),
    ← Ideal.over_def (p := v.asIdeal) (P := Q.1)]

/-- At an unramified finite prime, an arithmetic Frobenius at a fixed prime
above it is unique.  This is the strongest local uniqueness statement needed
by the ideal Artin construction. -/
theorem arithFrobAt_unique_of_unramified
    (v : FinitePrime K)
    (hunramified : Algebra.IsUnramifiedIn
      (NumberField.RingOfIntegers L) v.asIdeal)
    (Q : Ideal.primesOver v.asIdeal (NumberField.RingOfIntegers L))
    (τ : Gal(L/K))
    (hτ : IsArithFrobAt (NumberField.RingOfIntegers K) τ Q.1) :
    τ = arithFrobAt (NumberField.RingOfIntegers K) Gal(L/K) Q.1 := by
  letI : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.1 :=
    hunramified Q.1 inferInstance Q.2.2
  letI : FaithfulSMul Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.faithful (A := NumberField.RingOfIntegers K)
  apply MulSemiringAction.toAlgHom_injective
    (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
  exact hτ.eq_of_isUnramifiedAt
    (IsArithFrobAt.arithFrobAt
      (NumberField.RingOfIntegers K) Gal(L/K) Q.1)
    Q.1.primeCompl_le_nonZeroDivisors

end Frobenius

section SemilinearFrobenius

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S]

/-- Conjugate an `R`-algebra endomorphism by a ring equivalence of `S` that
is semilinear for a ring equivalence of `R`.  The two semilinear twists cancel,
so the conjugate is again `R`-linear. -/
def semilinearConjugate (eR : R ≃+* R) (eS : S ≃+* S)
    (hsemilinear : ∀ r : R,
      eS (algebraMap R S r) = algebraMap R S (eR r))
    (f : S →ₐ[R] S) : S →ₐ[R] S where
  toRingHom := eS.toRingHom.comp (f.toRingHom.comp eS.symm.toRingHom)
  commutes' r := by
    have hinv : eS.symm (algebraMap R S r) =
        algebraMap R S (eR.symm r) := by
      apply eS.injective
      rw [eS.apply_symm_apply, hsemilinear, eR.apply_symm_apply]
    change eS (f (eS.symm (algebraMap R S r))) = algebraMap R S r
    rw [hinv, f.commutes, hsemilinear, eR.apply_symm_apply]

/-- Pointwise formula for semilinear conjugation. -/
@[simp]
theorem semilinearConjugate_apply (eR : R ≃+* R) (eS : S ≃+* S)
    (hsemilinear : ∀ r : R,
      eS (algebraMap R S r) = algebraMap R S (eR r))
    (f : S →ₐ[R] S) (x : S) :
    semilinearConjugate eR eS hsemilinear f x =
      eS (f (eS.symm x)) :=
  rfl

/-- Under a semilinear equivalence of an algebra, transporting a prime of the
extension transports its underlying base prime by the base equivalence. -/
theorem under_map_semilinear (eR : R ≃+* R) (eS : S ≃+* S)
    (hsemilinear : ∀ r : R,
      eS (algebraMap R S r) = algebraMap R S (eR r))
    (Q : Ideal S) :
    (Q.map eS).under R = (Q.under R).map eR := by
  ext r
  change algebraMap R S r ∈ Q.map eS ↔ r ∈ (Q.under R).map eR
  rw [← Ideal.symm_apply_mem_of_equiv_iff,
    ← Ideal.symm_apply_mem_of_equiv_iff]
  have hinv : eS.symm (algebraMap R S r) =
      algebraMap R S (eR.symm r) := by
    apply eS.injective
    rw [eS.apply_symm_apply, hsemilinear, eR.apply_symm_apply]
  rw [hinv]
  rfl

/-- A semilinear transport preserves the cardinality of the base residue
field below a prime. -/
theorem card_quotient_under_map_semilinear
    (eR : R ≃+* R) (eS : S ≃+* S)
    (hsemilinear : ∀ r : R,
      eS (algebraMap R S r) = algebraMap R S (eR r))
    (Q : Ideal S) :
    Nat.card (R ⧸ (Q.map eS).under R) =
      Nat.card (R ⧸ Q.under R) := by
  rw [under_map_semilinear eR eS hsemilinear Q]
  exact (Nat.card_congr
    (Ideal.quotientEquiv (Q.under R) ((Q.under R).map eR)
      eR rfl).toEquiv).symm

/-- Arithmetic Frobenius congruences are preserved by compatible semilinear
transport of the base and extension rings. -/
theorem isArithFrobAt_semilinearConjugate
    (eR : R ≃+* R) (eS : S ≃+* S)
    (hsemilinear : ∀ r : R,
      eS (algebraMap R S r) = algebraMap R S (eR r))
    {f : S →ₐ[R] S} {Q : Ideal S}
    (hf : f.IsArithFrobAt Q) :
    (semilinearConjugate eR eS hsemilinear f).IsArithFrobAt
      (Q.map eS) := by
  intro x
  rw [← Ideal.symm_apply_mem_of_equiv_iff]
  simp only [map_sub, semilinearConjugate_apply,
    eS.symm_apply_apply, map_pow]
  change f (eS.symm x) -
      (eS.symm x) ^ Nat.card (R ⧸ (Q.map eS).under R) ∈ Q
  rw [card_quotient_under_map_semilinear eR eS hsemilinear Q]
  exact hf (eS.symm x)

omit [Algebra R S] in
/-- Transporting a height-one prime along a ring equivalence maps its ideal to
the image ideal. -/
theorem asIdeal_equivOfRingEquiv (e : R ≃+* R)
    (v : HeightOneSpectrum R) :
    (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal =
      Ideal.map e v.asIdeal := by
  ext x
  change e.symm x ∈ v.asIdeal ↔ x ∈ Ideal.map e v.asIdeal
  exact Ideal.symm_apply_mem_of_equiv_iff

end SemilinearFrobenius

section FractionalIdeals

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The semilinear fractional-ideal equivalence induced by a ring
automorphism sends an integral ideal to its ordinary image ideal. -/
theorem ringEquivOfRingEquiv_coeIdeal (g : R ≃+* R) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K K g
        (I : FractionalIdeal R⁰ K) =
      (Ideal.map g I : Ideal R) := by
  letI : RingHomInvPair (g : R →+* R) g.symm :=
    RingHomInvPair.of_ringEquiv g
  letI : RingHomInvPair (g.symm : R →+* R) g :=
    RingHomInvPair.of_ringEquiv_symm g
  ext x
  rw [FractionalIdeal.ringEquivOfRingEquiv_apply]
  change x ∈ Submodule.map
      (IsFractionRing.semilinearEquivOfRingEquiv K K g).toLinearMap
        ((I : FractionalIdeal R⁰ K).val) ↔
    x ∈ ((Ideal.map g I : Ideal R) : FractionalIdeal R⁰ K)
  rw [Submodule.mem_map]
  simp only [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨g r, Ideal.mem_map_of_mem g hr, ?_⟩
    exact (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap
      K K g r).symm
  · rintro ⟨r, hr, rfl⟩
    refine ⟨algebraMap R K (g.symm r), ?_, ?_⟩
    · exact ⟨g.symm r,
        Ideal.symm_apply_mem_of_equiv_iff.mpr hr, rfl⟩
    · exact
        (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap
          K K g (g.symm r)).trans
            (congrArg (algebraMap R K) (g.apply_symm_apply r))

/-- The finitely supported multiplicity divisor of an invertible fractional
ideal. -/
noncomputable def fractionalIdealDivisor :
    Additive (FractionalIdeal R⁰ K)ˣ →+ (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Finsupp.ofSupportFinite
    (fun x => FractionalIdeal.count K x (Units.val (Additive.toMul I)))
    (by
      simpa only [Function.support] using Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors (Units.val (Additive.toMul I))))
  map_zero' := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.ofSupportFinite_coe]
    simp only [toMul_zero, Units.val_one, Finsupp.coe_zero, Pi.zero_apply]
    exact FractionalIdeal.count_one K x
  map_add' I J := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.add_apply, Finsupp.ofSupportFinite_coe,
      Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe]
    simp only [toMul_add, Units.val_mul]
    exact FractionalIdeal.count_mul K x (Units.ne_zero _) (Units.ne_zero _)

/-- The coefficient of the fractional-ideal divisor is Mathlib's local
multiplicity. -/
@[simp]
theorem fractionalIdealDivisor_apply
    (I : Additive (FractionalIdeal R⁰ K)ˣ) (x : HeightOneSpectrum R) :
    fractionalIdealDivisor R K I x =
      FractionalIdeal.count K x (Units.val (Additive.toMul I)) := by
  simp only [fractionalIdealDivisor, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finsupp.ofSupportFinite_coe]

/-- A nonzero fractional ideal is recovered from all of its finite-prime
multiplicities. -/
theorem fractionalIdealDivisor_injective :
    Function.Injective (fractionalIdealDivisor R K) := by
  intro I J h
  have hcount : ∀ x,
      FractionalIdeal.count K x (Units.val (Additive.toMul I)) =
        FractionalIdeal.count K x (Units.val (Additive.toMul J)) := by
    intro x
    have hx := DFunLike.congr_fun h x
    simpa using hx
  have hval : Units.val (Additive.toMul I) =
      Units.val (Additive.toMul J) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul I)),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul J))]
    exact finprod_congr fun x => by rw [hcount x]
  exact Additive.toMul.injective (Units.ext hval)

/-- The fractional ideal attached to a finitely supported integer divisor is
nonzero. -/
theorem prod_asIdeal_zpow_ne_zero (D : HeightOneSpectrum R →₀ ℤ) :
    (D.prod fun x e => (x.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun x _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot)

/-- Every finitely supported integer divisor is the divisor of a nonzero
fractional ideal. -/
theorem fractionalIdealDivisor_surjective :
    Function.Surjective (fractionalIdealDivisor R K) := by
  intro D
  refine ⟨Additive.ofMul (Units.mk0
    (D.prod fun x e => (x.asIdeal : FractionalIdeal R⁰ K) ^ e)
    (prod_asIdeal_zpow_ne_zero R K D)), ?_⟩
  apply Finsupp.ext
  intro x
  rw [fractionalIdealDivisor_apply]
  simp only [toMul_ofMul, Units.val_mk0]
  exact FractionalIdeal.count_finsuppProd K x D

/-- Nonzero fractional ideals form the free abelian group on the finite
primes of a Dedekind domain. -/
noncomputable def fractionalIdealDivisorAddEquiv :
    Additive (FractionalIdeal R⁰ K)ˣ ≃+ (HeightOneSpectrum R →₀ ℤ) :=
  AddEquiv.ofBijective (fractionalIdealDivisor R K)
    ⟨fractionalIdealDivisor_injective R K,
      fractionalIdealDivisor_surjective R K⟩

variable {R K}

/-- The divisor of a prime fractional ideal is the corresponding standard
basis divisor. -/
@[simp]
theorem fractionalIdealDivisor_prime (x : HeightOneSpectrum R) :
    fractionalIdealDivisor R K
      (Additive.ofMul (Units.mk0 (x.asIdeal : FractionalIdeal R⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot))) =
      Finsupp.single x 1 := by
  apply Finsupp.ext
  intro y
  rw [fractionalIdealDivisor_apply]
  simp only [toMul_ofMul, Units.val_mk0]
  by_cases h : x = y
  · subst h
    simp [FractionalIdeal.count_self]
  · rw [FractionalIdeal.count_maximal_coprime K y h]
    simp [h]

variable {M : Type w} [CommGroup M]

/-- The multiplicative form of the divisor equivalence for nonzero
fractional ideals. -/
noncomputable def fractionalIdealDivisorMulEquiv :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  (fractionalIdealDivisorAddEquiv R K).toMultiplicativeRight

/-- The unit of the fractional-ideal monoid represented by a finite prime. -/
noncomputable def primeFractionalIdealUnit (x : HeightOneSpectrum R) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (x.asIdeal : FractionalIdeal R⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot)

/-- Under the multiplicative divisor equivalence, a finite prime is its
standard basis divisor. -/
@[simp]
theorem fractionalIdealDivisorMulEquiv_prime (x : HeightOneSpectrum R) :
    fractionalIdealDivisorMulEquiv (R := R) (K := K)
      (primeFractionalIdealUnit (K := K) x) =
      Multiplicative.ofAdd (Finsupp.single x 1) := by
  unfold fractionalIdealDivisorMulEquiv primeFractionalIdealUnit
  change Multiplicative.ofAdd
    (fractionalIdealDivisor R K (Additive.ofMul _)) = _
  rw [fractionalIdealDivisor_prime]

/-- Homomorphisms out of the fractional-ideal group are determined by their
values on finite prime ideals. -/
theorem fractionalIdealMonoidHom_ext
    {f g : (FractionalIdeal R⁰ K)ˣ →* M}
    (h : ∀ x : HeightOneSpectrum R,
      f (primeFractionalIdealUnit (K := K) x) =
        g (primeFractionalIdealUnit (K := K) x)) : f = g := by
  let e := fractionalIdealDivisorMulEquiv (R := R) (K := K)
  have hcomp : f.comp e.symm.toMonoidHom = g.comp e.symm.toMonoidHom := by
    apply Multiplicative.monoidHom_ext
    apply Finsupp.addHom_ext'
    intro x
    apply AddMonoidHom.ext_int
    change f (e.symm (Multiplicative.ofAdd (Finsupp.single x 1))) =
      g (e.symm (Multiplicative.ofAdd (Finsupp.single x 1)))
    rw [← fractionalIdealDivisorMulEquiv_prime (R := R) (K := K) x,
      e.symm_apply_apply]
    exact h x
  apply MonoidHom.ext
  intro I
  have hi := DFunLike.congr_fun hcomp (e I)
  change f (e.symm (e I)) = g (e.symm (e I)) at hi
  rwa [e.symm_apply_apply] at hi

/-- Extend a family of values on the generators of a free abelian group to a
homomorphism. -/
noncomputable def freeAbelianHom (c : HeightOneSpectrum R → M) :
    Multiplicative (HeightOneSpectrum R →₀ ℤ) →* M :=
  AddMonoidHom.toMultiplicativeLeft
    (Finsupp.liftAddHom fun x =>
      (zmultiplesHom (Additive M)) (Additive.ofMul (c x)))

omit [IsDedekindDomain R] in
/-- The free extension takes a standard basis divisor to its prescribed
value. -/
@[simp]
theorem freeAbelianHom_single (c : HeightOneSpectrum R → M)
    (x : HeightOneSpectrum R) :
    freeAbelianHom c (Multiplicative.ofAdd (Finsupp.single x 1)) = c x := by
  simp [freeAbelianHom]

omit [IsDedekindDomain R] in
/-- The free extension is the finite product of the prescribed generator
values raised to their integer multiplicities. -/
theorem freeAbelianHom_apply (c : HeightOneSpectrum R → M)
    (D : HeightOneSpectrum R →₀ ℤ) :
    freeAbelianHom c (Multiplicative.ofAdd D) =
      D.prod fun x n => c x ^ n := by
  rfl

variable {N : Type w'} [CommGroup N]

omit [IsDedekindDomain R] in
/-- Extending values on generators commutes with a homomorphism of target
groups. -/
theorem freeAbelianHom_comp (f : M →* N) (c : HeightOneSpectrum R → M) :
    f.comp (freeAbelianHom c) =
      freeAbelianHom (fun x => f (c x)) := by
  ext x
  simp [freeAbelianHom]

/-- The homomorphism from nonzero fractional ideals obtained by prescribing a
value at every finite prime. -/
noncomputable def fractionalIdealHom (c : HeightOneSpectrum R → M) :
    (FractionalIdeal R⁰ K)ˣ →* M :=
  (freeAbelianHom c).comp
    (fractionalIdealDivisor R K).toMultiplicativeRight

/-- The fractional-ideal homomorphism has the prescribed value on each prime
ideal. -/
@[simp]
theorem fractionalIdealHom_prime (c : HeightOneSpectrum R → M)
    (x : HeightOneSpectrum R) :
    fractionalIdealHom c
      (Units.mk0 (x.asIdeal : FractionalIdeal R⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot)) = c x := by
  rw [fractionalIdealHom, MonoidHom.comp_apply]
  change freeAbelianHom c (Multiplicative.ofAdd
    (fractionalIdealDivisor R K (Additive.ofMul _))) = _
  rw [fractionalIdealDivisor_prime, freeAbelianHom_single]

/-- The fractional-ideal homomorphism is the finite Artin product over the
prime factorization of the ideal. -/
theorem fractionalIdealHom_apply (c : HeightOneSpectrum R → M)
    (I : (FractionalIdeal R⁰ K)ˣ) :
    fractionalIdealHom c I =
      (fractionalIdealDivisor R K (Additive.ofMul I)).prod
        (fun x n => c x ^ n) := by
  rfl

/-- Postcomposition of a fractional-ideal homomorphism is computed locally on
its prime symbols. -/
theorem fractionalIdealHom_comp (f : M →* N)
    (c : HeightOneSpectrum R → M) :
    f.comp (fractionalIdealHom (R := R) (K := K) c) =
      fractionalIdealHom (R := R) (K := K) (fun x => f (c x)) := by
  rw [fractionalIdealHom, fractionalIdealHom, ← MonoidHom.comp_assoc,
    freeAbelianHom_comp]

/-- The image of a fractional-ideal homomorphism is exactly the subgroup
generated by its finite-prime symbols. -/
theorem fractionalIdealHom_range (c : HeightOneSpectrum R → M) :
    (fractionalIdealHom (R := R) (K := K) c).range =
      Subgroup.closure (Set.range c) := by
  apply le_antisymm
  · rintro m ⟨I, rfl⟩
    rw [fractionalIdealHom_apply, Finsupp.prod]
    apply Subgroup.prod_mem
    intro x hx
    exact Subgroup.zpow_mem _
      (Subgroup.subset_closure (Set.mem_range_self x)) _
  · rw [Subgroup.closure_le]
    rintro m ⟨x, rfl⟩
    exact ⟨Units.mk0 (x.asIdeal : FractionalIdeal R⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot),
      fractionalIdealHom_prime c x⟩

/-- Surjectivity of the fractional-ideal homomorphism is equivalent to
generation of the target by its finite-prime symbols. -/
theorem fractionalIdealHom_surjective_iff (c : HeightOneSpectrum R → M) :
    Function.Surjective (fractionalIdealHom (R := R) (K := K) c) ↔
      Subgroup.closure (Set.range c) = ⊤ := by
  rw [← MonoidHom.range_eq_top, fractionalIdealHom_range]

end FractionalIdeals

section ClassGroup

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
variable {M : Type w} [CommGroup M]

/-- The class-group automorphism induced by a ring automorphism, expressed in
the chosen fraction field `K`.  This computational form agrees with the
canonical construction but has a direct formula on `ClassGroup.mk K`. -/
noncomputable def classGroupEquiv (g : R ≃+* R) :
    ClassGroup R ≃* ClassGroup R :=
  (ClassGroup.equiv K).trans
    ((QuotientGroup.congr (toPrincipalIdeal R K).range
      (toPrincipalIdeal R K).range
      (Units.mapEquiv
        (FractionalIdeal.ringEquivOfRingEquiv K K g).toMulEquiv)
      (FractionalIdeal.map_ringEquivOfRingEquiv_toPrincipalIdeal g)).trans
      (ClassGroup.equiv K).symm)

/-- Formula for the induced class-group automorphism on a represented
fractional ideal. -/
theorem classGroupEquiv_mk (g : R ≃+* R)
    (I : (FractionalIdeal R⁰ K)ˣ) :
    classGroupEquiv R K g (ClassGroup.mk K I) =
      ClassGroup.mk K
        ((Units.mapEquiv
          (FractionalIdeal.ringEquivOfRingEquiv K K g).toMulEquiv) I) := by
  apply (ClassGroup.equiv K).injective
  simp only [classGroupEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, ClassGroup.equiv_mk]
  simp [FractionalIdeal.canonicalEquiv_self]
  rfl

/-- The exact conductor-one reciprocity condition needed for an ideal
homomorphism to descend to the ordinary ideal class group. -/
def KillsPrincipalIdeals (φ : (FractionalIdeal R⁰ K)ˣ →* M) : Prop :=
  ∀ x : Kˣ, φ (toPrincipalIdeal R K x) = 1

/-- The principal fractional-ideal subgroup lies in the kernel of an ideal
homomorphism satisfying conductor-one reciprocity. -/
theorem principalIdeals_le_ker (φ : (FractionalIdeal R⁰ K)ˣ →* M)
    (hprincipal : KillsPrincipalIdeals R K φ) :
    (toPrincipalIdeal R K).range ≤ φ.ker := by
  rintro I ⟨x, rfl⟩
  exact MonoidHom.mem_ker.mpr (hprincipal x)

/-- Descend an ideal homomorphism that kills principal ideals to the ordinary
ideal class group. -/
noncomputable def classGroupHom (φ : (FractionalIdeal R⁰ K)ˣ →* M)
    (hprincipal : KillsPrincipalIdeals R K φ) : ClassGroup R →* M :=
  (QuotientGroup.lift (toPrincipalIdeal R K).range φ
    (principalIdeals_le_ker R K φ hprincipal)).comp
      (ClassGroup.equiv K).toMonoidHom

/-- The descended class-group map agrees with the original ideal map on the
canonical class of a fractional ideal. -/
theorem classGroupHom_mk (φ : (FractionalIdeal R⁰ K)ˣ →* M)
    (hprincipal : KillsPrincipalIdeals R K φ)
    (I : (FractionalIdeal R⁰ K)ˣ) :
    classGroupHom R K φ hprincipal (ClassGroup.mk K I) = φ I := by
  change QuotientGroup.lift (toPrincipalIdeal R K).range φ
    (principalIdeals_le_ker R K φ hprincipal)
      (ClassGroup.equiv K (ClassGroup.mk K I)) = _
  rw [ClassGroup.equiv_mk]
  change φ
    ((Units.mapEquiv (FractionalIdeal.canonicalEquiv R⁰ K K).toMulEquiv) I) = _
  congr 1
  apply Units.ext
  simp

/-- Surjectivity of an ideal homomorphism passes to its class-group descent. -/
theorem classGroupHom_surjective (φ : (FractionalIdeal R⁰ K)ˣ →* M)
    (hprincipal : KillsPrincipalIdeals R K φ)
    (hsurjective : Function.Surjective φ) :
    Function.Surjective (classGroupHom R K φ hprincipal) := by
  intro m
  obtain ⟨I, rfl⟩ := hsurjective m
  exact ⟨ClassGroup.mk K I, classGroupHom_mk R K φ hprincipal I⟩

/-- The class-group descent is onto exactly when the original fractional-ideal
homomorphism is onto. -/
theorem classGroupHom_surjective_iff
    (φ : (FractionalIdeal R⁰ K)ˣ →* M)
    (hprincipal : KillsPrincipalIdeals R K φ) :
    Function.Surjective (classGroupHom R K φ hprincipal) ↔
      Function.Surjective φ := by
  constructor
  · intro hsurjective m
    obtain ⟨c, hc⟩ := hsurjective m
    obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c
    refine ⟨FractionalIdeal.mk0 K J, ?_⟩
    rw [← classGroupHom_mk R K φ hprincipal, ClassGroup.mk_mk0, hJ]
    exact hc
  · exact classGroupHom_surjective R K φ hprincipal

/-- After principal reciprocity, the class-group map is onto exactly when its
finite-prime symbols generate the target.  This identifies the precise
Frobenius-generation input supplied classically by Chebotarev or the global
Artin existence theorem. -/
theorem classGroupHom_surjective_iff_generators
    (c : HeightOneSpectrum R → M)
    (hprincipal : KillsPrincipalIdeals R K
      (fractionalIdealHom (R := R) (K := K) c)) :
    Function.Surjective
        (classGroupHom R K (fractionalIdealHom c) hprincipal) ↔
      Subgroup.closure (Set.range c) = ⊤ :=
  (classGroupHom_surjective_iff R K _ hprincipal).trans
    (fractionalIdealHom_surjective_iff c)

end ClassGroup

section Artin

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- The ideal-theoretic arithmetic Frobenius homomorphism of an abelian
extension, before applying global reciprocity to principal ideals. -/
noncomputable def fractionalArtin [IsMulCommutative Gal(L/K)] :
    (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ →* Gal(L/K) :=
  fractionalIdealHom (frobeniusAt (K := K) (L := L))

/-- The fractional Artin map sends a prime ideal to its arithmetic
Frobenius. -/
@[simp]
theorem fractionalArtin_prime [IsMulCommutative Gal(L/K)]
    (x : FinitePrime K) :
    fractionalArtin (K := K) (L := L)
      (Units.mk0
        (x.asIdeal : FractionalIdeal
          (NumberField.RingOfIntegers K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot)) =
      frobeniusAt (K := K) (L := L) x :=
  fractionalIdealHom_prime _ x

end Artin

end NumberTheory.UnramifiedArtin
