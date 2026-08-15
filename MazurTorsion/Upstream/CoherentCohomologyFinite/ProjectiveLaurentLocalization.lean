/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCech
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceStandardCover

/-!
# Laurent monomials in homogeneous coordinate localizations

This file identifies the degree-zero homogeneous localization of the
standard polynomial ring away from a product of coordinates with the free
module on the corresponding admissible Laurent monomials.

The proof embeds the ordinary localization into the full Laurent monomial
algebra.  It gives explicit homogeneous fractions for Laurent basis
vectors, proves linear independence in the Laurent algebra, and proves
spanning by expanding an arbitrary homogeneous numerator into monomials.
-/

open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

variable {ι k : Type*} [Fintype ι] [DecidableEq ι]

/-- Embed a natural multi-exponent into the group of integer multi-exponents. -/
def naturalExponent : (ι →₀ ℕ) →+ ProjectiveExponent ι where
  toFun a i := a i
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp]
lemma naturalExponent_apply (a : ι →₀ ℕ) (i : ι) :
    naturalExponent a i = a i := rfl

lemma naturalExponent_injective :
    Function.Injective (naturalExponent (ι := ι)) := by
  intro a b h
  ext i
  have hi := congrFun h i
  change (a i : ℤ) = (b i : ℤ) at hi
  exact_mod_cast hi

/-- The full Laurent monomial algebra. -/
abbrev LaurentAlgebra (k : Type*) [Semiring k] (ι : Type*) :=
  AddMonoidAlgebra k (ProjectiveExponent ι)

/-- Polynomial monomials map to Laurent monomials by coercing all
exponents from naturals to integers. -/
def polynomialToLaurent [CommSemiring k] :
    MvPolynomial ι k →+* LaurentAlgebra k ι :=
  AddMonoidAlgebra.mapDomainRingHom k (naturalExponent (ι := ι))

lemma polynomialToLaurent_injective [CommSemiring k] :
    Function.Injective (polynomialToLaurent (ι := ι) (k := k)) :=
  AddMonoidAlgebra.mapDomain_injective naturalExponent_injective

@[simp]
lemma polynomialToLaurent_monomial
    [CommSemiring k] (a : ι →₀ ℕ) (r : k) :
    polynomialToLaurent (ι := ι) (k := k)
        (MvPolynomial.monomial a r) =
      AddMonoidAlgebra.single (naturalExponent a) r :=
  AddMonoidAlgebra.mapDomain_single

@[simp]
lemma polynomialToLaurent_C [CommSemiring k] (r : k) :
    polynomialToLaurent (ι := ι) (k := k) (MvPolynomial.C r) =
      algebraMap k (LaurentAlgebra k ι) r := by
  change
    polynomialToLaurent (ι := ι) (k := k)
        (MvPolynomial.monomial 0 r) =
      AddMonoidAlgebra.single 0 r
  rw [polynomialToLaurent_monomial]
  congr

/-- Product of the variables indexed by a finite set. -/
def variableProduct [CommSemiring k] (I : Finset ι) :
    MvPolynomial ι k :=
  ∏ i ∈ I, MvPolynomial.X i

/-- The exponent vector of a squarefree product of variables. -/
def indicatorExponent (I : Finset ι) : ProjectiveExponent ι :=
  fun i => if i ∈ I then 1 else 0

@[simp]
lemma indicatorExponent_apply (I : Finset ι) (i : ι) :
    indicatorExponent I i = if i ∈ I then 1 else 0 := rfl

lemma polynomialToLaurent_variableProduct [CommSemiring k]
    (I : Finset ι) :
    polynomialToLaurent (ι := ι) (k := k) (variableProduct (k := k) I) =
      AddMonoidAlgebra.single (indicatorExponent I) 1 := by
  classical
  rw [variableProduct, map_prod]
  simp only [MvPolynomial.X, polynomialToLaurent_monomial]
  rw [AddMonoidAlgebra.prod_single]
  congr 1
  · funext i
    simp only [Finset.sum_apply, naturalExponent_apply,
      indicatorExponent_apply]
    by_cases hi : i ∈ I <;>
      simp [Finsupp.single_apply, hi]
  · simp

/-- The inverse Laurent monomial to the image of a variable product. -/
def variableProductInverse [CommSemiring k] (I : Finset ι) :
    LaurentAlgebra k ι :=
  AddMonoidAlgebra.single (-indicatorExponent I) 1

/-- A Laurent monomial is a unit, with inverse indexed by the negated
exponent. -/
def laurentMonomialUnit [CommSemiring k]
    (a : ProjectiveExponent ι) : Units (LaurentAlgebra k ι) where
  val := AddMonoidAlgebra.single a 1
  inv := AddMonoidAlgebra.single (-a) 1
  val_inv := by
    rw [AddMonoidAlgebra.single_mul_single]
    simpa only [add_neg_cancel, mul_one] using
      (AddMonoidAlgebra.one_def :
        (1 : LaurentAlgebra k ι) = AddMonoidAlgebra.single 0 1).symm
  inv_val := by
    rw [AddMonoidAlgebra.single_mul_single]
    simpa only [neg_add_cancel, mul_one] using
      (AddMonoidAlgebra.one_def :
        (1 : LaurentAlgebra k ι) = AddMonoidAlgebra.single 0 1).symm

@[simp]
lemma laurentMonomialUnit_val [CommSemiring k]
    (a : ProjectiveExponent ι) :
    (laurentMonomialUnit (k := k) a :
      LaurentAlgebra k ι) = AddMonoidAlgebra.single a 1 := rfl

lemma polynomialToLaurent_variableProduct_mul_inverse
    [CommSemiring k] (I : Finset ι) :
    polynomialToLaurent (ι := ι) (k := k) (variableProduct (k := k) I) *
        variableProductInverse (k := k) I = 1 := by
  rw [polynomialToLaurent_variableProduct]
  simpa only [variableProductInverse, laurentMonomialUnit_val,
    laurentMonomialUnit] using
    (laurentMonomialUnit (k := k)
      (indicatorExponent I)).val_inv

lemma polynomialToLaurent_variableProduct_isUnit
    [CommSemiring k] (I : Finset ι) :
    IsUnit
      (polynomialToLaurent (ι := ι) (k := k)
        (variableProduct (k := k) I)) := by
  rw [polynomialToLaurent_variableProduct]
  exact (laurentMonomialUnit (k := k)
    (indicatorExponent I)).isUnit

/-- The ordinary localization away from a squarefree product embeds in
the full Laurent monomial algebra. -/
def localizationToLaurent [CommSemiring k] (I : Finset ι) :
    Localization.Away (variableProduct (k := k) I) →+*
      LaurentAlgebra k ι :=
  Localization.awayLift
    (polynomialToLaurent (ι := ι) (k := k))
    (variableProduct (k := k) I)
    (isUnit_iff_exists_inv.mpr
      ⟨variableProductInverse (k := k) I,
        polynomialToLaurent_variableProduct_mul_inverse I⟩)

lemma localizationToLaurent_mk
    [CommSemiring k] (I : Finset ι) (p : MvPolynomial ι k)
    (n : ℕ) :
    localizationToLaurent (k := k) I
        (Localization.mk p
          ⟨variableProduct (k := k) I ^ n, n, rfl⟩) =
      polynomialToLaurent p *
        variableProductInverse (k := k) I ^ n := by
  simpa only [localizationToLaurent] using
    Localization.awayLift_mk
      (polynomialToLaurent (ι := ι) (k := k))
      (variableProduct (k := k) I) p
      (variableProductInverse (k := k) I)
      (polynomialToLaurent_variableProduct_mul_inverse I) n

@[simp]
lemma localizationToLaurent_algebraMap
    [CommSemiring k] (I : Finset ι) (p : MvPolynomial ι k) :
    localizationToLaurent (k := k) I
        (algebraMap (MvPolynomial ι k)
          (Localization.Away (variableProduct (k := k) I)) p) =
      polynomialToLaurent p := by
  simpa only [localizationToLaurent, Localization.awayLift] using
    IsLocalization.Away.lift_eq
      (variableProduct (k := k) I)
      (isUnit_iff_exists_inv.mpr
        ⟨variableProductInverse (k := k) I,
          polynomialToLaurent_variableProduct_mul_inverse I⟩)
      p

lemma variableProduct_ne_zero [CommRing k] [NoZeroDivisors k]
    [Nontrivial k] (I : Finset ι) :
    variableProduct (k := k) I ≠ 0 := by
  rw [variableProduct, Finset.prod_ne_zero_iff]
  exact fun i _ => MvPolynomial.X_ne_zero i

/-- A product of polynomial variables is regular even when the
coefficient ring has zero divisors.  This is the input needed to embed
the corresponding localization into the Laurent algebra over an
arbitrary affine base. -/
lemma variableProduct_isRegular [CommRing k] (I : Finset ι) :
    IsRegular (variableProduct (k := k) I) := by
  simpa only [variableProduct] using
    (MvPolynomial.isRegular_prod_X (R := k) I)

theorem localizationToLaurent_injective
    [CommRing k] (I : Finset ι) :
    Function.Injective (localizationToLaurent (k := k) I) := by
  change Function.Injective
    (IsLocalization.lift
      (M := Submonoid.powers (variableProduct (k := k) I)) _)
  rw [IsLocalization.lift_injective_iff]
  intro p q
  have hpowers :
      Submonoid.powers (variableProduct (k := k) I) ≤
        nonZeroDivisors (MvPolynomial ι k) := by
    intro x hx
    obtain ⟨n, rfl⟩ :=
      (Submonoid.mem_powers_iff x
        (variableProduct (k := k) I)).mp hx
    exact ((variableProduct_isRegular I).pow n).mem_nonZeroDivisors
  let hloc :
      Function.Injective
        (algebraMap (MvPolynomial ι k)
          (Localization.Away (variableProduct (k := k) I))) :=
    IsLocalization.injective _ hpowers
  constructor
  · intro h
    exact congrArg polynomialToLaurent (hloc h)
  · intro h
    exact congrArg
      (algebraMap (MvPolynomial ι k)
        (Localization.Away (variableProduct (k := k) I)))
      (polynomialToLaurent_injective h)

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {d : ℕ}

/-- A denominator power large enough to clear all negative exponents. -/
def clearingPower (I : Finset ι)
    (a : AdmissibleExponent (ι := ι) 0 I) : ℕ :=
  Finset.univ.sup fun i => Int.toNat (-a.1 i)

lemma negExponent_toNat_le_clearingPower
    (I : Finset ι) (a : AdmissibleExponent (ι := ι) 0 I)
    (i : ι) :
    Int.toNat (-a.1 i) ≤ clearingPower I a :=
  Finset.le_sup (f := fun i => Int.toNat (-a.1 i))
    (Finset.mem_univ i)

/-- Adding the clearing power on the inverted coordinates makes every
exponent nonnegative. -/
lemma add_clearingPower_nonnegative
    (I : Finset ι) (a : AdmissibleExponent (ι := ι) 0 I)
    (i : ι) :
    0 ≤ a.1 i + if i ∈ I then (clearingPower I a : ℤ) else 0 := by
  by_cases hi : i ∈ I
  · simp only [hi, if_true]
    by_cases hai : 0 ≤ a.1 i
    · omega
    · have hneg : 0 ≤ -a.1 i := by omega
      have hcast :
          (Int.toNat (-a.1 i) : ℤ) = -a.1 i :=
        Int.toNat_of_nonneg hneg
      have hleNat :=
        negExponent_toNat_le_clearingPower I a i
      have hleInt :
          (Int.toNat (-a.1 i) : ℤ) ≤
            (clearingPower I a : ℤ) := by
        exact_mod_cast hleNat
      omega
  · simp only [hi, if_false, add_zero]
    exact
      (ProjectiveExponent.admissibleOn_iff_nonnegative_outside
        a.1 I).mp a.2.2 i hi

/-- The natural exponent vector obtained after clearing denominators. -/
def clearedExponent (I : Finset ι)
    (a : AdmissibleExponent (ι := ι) 0 I) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i =>
    Int.toNat
      (a.1 i +
        if i ∈ I then (clearingPower I a : ℤ) else 0)

@[simp]
lemma clearedExponent_apply (I : Finset ι)
    (a : AdmissibleExponent (ι := ι) 0 I) (i : ι) :
    clearedExponent I a i =
      Int.toNat
        (a.1 i +
          if i ∈ I then (clearingPower I a : ℤ) else 0) :=
  rfl

lemma naturalExponent_clearedExponent
    (I : Finset ι) (a : AdmissibleExponent (ι := ι) 0 I) :
    naturalExponent (clearedExponent I a) =
      a.1 + (clearingPower I a) • indicatorExponent I := by
  funext i
  rw [naturalExponent_apply, clearedExponent_apply,
    Int.toNat_of_nonneg (add_clearingPower_nonnegative I a i)]
  by_cases hi : i ∈ I <;>
    simp [indicatorExponent, hi]

lemma totalDegree_naturalExponent (e : ι →₀ ℕ) :
    ProjectiveExponent.totalDegree (naturalExponent e) =
      (e.degree : ℤ) := by
  simp [ProjectiveExponent.totalDegree, Finsupp.degree_eq_sum,
    naturalExponent]

lemma totalDegree_indicatorExponent (I : Finset ι) :
    ProjectiveExponent.totalDegree (indicatorExponent I) =
      (I.card : ℤ) := by
  simp [ProjectiveExponent.totalDegree, indicatorExponent]

lemma totalDegree_nsmul (n : ℕ) (a : ProjectiveExponent ι) :
    ProjectiveExponent.totalDegree (n • a) =
      (n : ℤ) * ProjectiveExponent.totalDegree a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [add_nsmul,
        ProjectiveExponent.totalDegree_add, ih]
      push_cast
      ring

lemma clearedExponent_degree
    (I : Finset ι) (a : AdmissibleExponent (ι := ι) 0 I) :
    (clearedExponent I a).degree =
      clearingPower I a * I.card := by
  apply Nat.cast_injective (R := ℤ)
  calc
    ((clearedExponent I a).degree : ℤ) =
        ProjectiveExponent.totalDegree
          (naturalExponent (clearedExponent I a)) := by
      rw [totalDegree_naturalExponent]
    _ =
        ProjectiveExponent.totalDegree
          (a.1 + (clearingPower I a) • indicatorExponent I) := by
      rw [naturalExponent_clearedExponent]
    _ =
        ProjectiveExponent.totalDegree a.1 +
          (clearingPower I a : ℤ) *
            ProjectiveExponent.totalDegree (indicatorExponent I) := by
      rw [ProjectiveExponent.totalDegree_add, totalDegree_nsmul]
    _ = (clearingPower I a * I.card : ℕ) := by
      rw [a.2.1, totalDegree_indicatorExponent]
      norm_num

/-- The product of the variables in `I` is homogeneous of degree
`I.card`. -/
lemma variableProduct_mem_degreeCard [CommRing k]
    (I : Finset (Fin (d + 1))) :
    variableProduct (k := k) I ∈ homogeneousGrading k d I.card := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  simpa [variableProduct] using
    MvPolynomial.IsHomogeneous.prod I
      (fun i : Fin (d + 1) => MvPolynomial.X i)
      (fun _ => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X k i)

/-- The homogeneous localization inherits the coefficient-module structure
through its injective map to the ordinary localization. -/
noncomputable instance homogeneousAwayModule [CommRing k]
    (I : Finset (Fin (d + 1))) :
    Module k
      (HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I)) := by
  apply Function.Injective.module k
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I))
      (Localization.Away
        (variableProduct (k := k) I))).toAddMonoidHom
    (HomogeneousLocalization.val_injective
      (Submonoid.powers (variableProduct (k := k) I)))
  intro r x
  exact
    HomogeneousLocalization.val_smul
      (Submonoid.powers (variableProduct (k := k) I)) r x

/-- The compatible coefficient algebra structure on the homogeneous
localization. -/
noncomputable instance homogeneousAwayAlgebra [CommRing k]
    (I : Finset (Fin (d + 1))) :
    Algebra k
      (HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I)) :=
  Algebra.ofModule
    (fun r x y => by
      apply HomogeneousLocalization.val_injective
      simp only [HomogeneousLocalization.val_mul,
        HomogeneousLocalization.val_smul]
      exact Algebra.smul_mul_assoc r x.val y.val)
    (fun r x y => by
      apply HomogeneousLocalization.val_injective
      simp only [HomogeneousLocalization.val_mul,
        HomogeneousLocalization.val_smul]
      exact Algebra.mul_smul_comm r x.val y.val)

/-- The homogeneous fraction represented by one admissible degree-zero
Laurent exponent. -/
def degreeZeroFraction [CommRing k]
    (I : Finset (Fin (d + 1)))
    (a : AdmissibleExponent (ι := Fin (d + 1)) 0 I) :
    HomogeneousLocalization.Away
      (homogeneousGrading k d)
      (variableProduct (k := k) I) :=
  HomogeneousLocalization.Away.mk
    (homogeneousGrading k d)
    (variableProduct_mem_degreeCard I)
    (clearingPower I a)
    (MvPolynomial.monomial (clearedExponent I a) 1)
    (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      apply MvPolynomial.isHomogeneous_monomial
      simpa [clearedExponent_degree])

/-- Embed the degree-zero homogeneous localization into the full Laurent
monomial algebra. -/
def homogeneousAwayToLaurent [CommRing k]
    (I : Finset (Fin (d + 1))) :
    HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I) →+*
      LaurentAlgebra k (Fin (d + 1)) :=
  (localizationToLaurent (k := k) I).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I))
      (Localization.Away (variableProduct (k := k) I)))

theorem homogeneousAwayToLaurent_injective
    [CommRing k] (I : Finset (Fin (d + 1))) :
    Function.Injective (homogeneousAwayToLaurent (k := k) (d := d) I) := by
  intro x y h
  apply HomogeneousLocalization.val_injective
  apply localizationToLaurent_injective I
  exact h

lemma homogeneousAwayToLaurent_smul
    [CommRing k] (I : Finset (Fin (d + 1))) (r : k)
    (x :
      HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I)) :
    homogeneousAwayToLaurent (k := k) (d := d) I (r • x) =
      r • homogeneousAwayToLaurent (k := k) (d := d) I x := by
  change
    localizationToLaurent (k := k) I
        (HomogeneousLocalization.val (r • x)) =
      r • localizationToLaurent (k := k) I
        (HomogeneousLocalization.val x)
  rw [HomogeneousLocalization.val_smul
    (Submonoid.powers (variableProduct (k := k) I))]
  rw [Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply k
      (MvPolynomial (Fin (d + 1)) k)
      (Localization.Away (variableProduct (k := k) I)),
    localizationToLaurent_algebraMap]
  change
    polynomialToLaurent (ι := Fin (d + 1)) (k := k)
        (MvPolynomial.C r) *
        localizationToLaurent (k := k) I x.val =
      r • localizationToLaurent (k := k) I x.val
  rw [polynomialToLaurent_C, ← Algebra.smul_def]

@[simp]
lemma homogeneousAwayToLaurent_algebraMap
    [CommRing k] (I : Finset (Fin (d + 1))) (r : k) :
    homogeneousAwayToLaurent (k := k) (d := d) I
        (algebraMap k
          (HomogeneousLocalization.Away
            (homogeneousGrading k d)
            (variableProduct (k := k) I)) r) =
      algebraMap k (LaurentAlgebra k (Fin (d + 1))) r := by
  calc
    homogeneousAwayToLaurent (k := k) (d := d) I
        (algebraMap k
          (HomogeneousLocalization.Away
            (homogeneousGrading k d)
            (variableProduct (k := k) I)) r) =
        homogeneousAwayToLaurent (k := k) (d := d) I
          (r • 1) := by
            rw [Algebra.algebraMap_eq_smul_one]
    _ = r • homogeneousAwayToLaurent (k := k) (d := d) I 1 :=
      homogeneousAwayToLaurent_smul I r 1
    _ = r • 1 := by rw [map_one]
    _ = algebraMap k (LaurentAlgebra k (Fin (d + 1))) r :=
      (Algebra.algebraMap_eq_smul_one r).symm

/-- The Laurent embedding as a coefficient-linear map. -/
def homogeneousAwayToLaurentLinearMap [CommRing k]
    (I : Finset (Fin (d + 1))) :
    HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I) →ₗ[k]
      LaurentAlgebra k (Fin (d + 1)) where
  toFun := homogeneousAwayToLaurent (k := k) (d := d) I
  map_add' := map_add (homogeneousAwayToLaurent (k := k) (d := d) I)
  map_smul' := homogeneousAwayToLaurent_smul I

/-- The Laurent embedding as a coefficient-linear algebra map. -/
def homogeneousAwayToLaurentAlgHom [CommRing k]
    (I : Finset (Fin (d + 1))) :
    HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I) →ₐ[k]
      LaurentAlgebra k (Fin (d + 1)) where
  __ := homogeneousAwayToLaurent (k := k) (d := d) I
  commutes' := homogeneousAwayToLaurent_algebraMap I

lemma naturalExponent_cleared_add_inverse
    (I : Finset ι) (a : AdmissibleExponent (ι := ι) 0 I) :
    naturalExponent (clearedExponent I a) +
        (clearingPower I a) • (-indicatorExponent I) =
      a.1 := by
  rw [naturalExponent_clearedExponent]
  module

@[simp]
lemma homogeneousAwayToLaurent_degreeZeroFraction
    [CommRing k] (I : Finset (Fin (d + 1)))
    (a : AdmissibleExponent (ι := Fin (d + 1)) 0 I) :
    homogeneousAwayToLaurent (k := k) (d := d) I
        (degreeZeroFraction (k := k) I a) =
      AddMonoidAlgebra.single a.1 1 := by
  change
    localizationToLaurent (k := k) I
        (HomogeneousLocalization.val
          (degreeZeroFraction (k := k) I a)) =
      AddMonoidAlgebra.single a.1 1
  rw [degreeZeroFraction, HomogeneousLocalization.Away.val_mk,
    localizationToLaurent_mk, polynomialToLaurent_monomial,
    variableProductInverse,
    AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single]
  congr 1
  · exact naturalExponent_cleared_add_inverse I a
  · simp

/-- Interpret a finitely supported Laurent coefficient family as a
linear combination of homogeneous fractions. -/
def degreeZeroFractionLinearMap [CommRing k]
    (I : Finset (Fin (d + 1))) :
    MonomialModule (ι := Fin (d + 1)) k 0 I →ₗ[k]
      HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I) :=
  Finsupp.linearCombination k (degreeZeroFraction (k := k) I)

@[simp]
lemma degreeZeroFractionLinearMap_single [CommRing k]
    (I : Finset (Fin (d + 1)))
    (a : AdmissibleExponent (ι := Fin (d + 1)) 0 I)
    (r : k) :
    degreeZeroFractionLinearMap (k := k) I (Finsupp.single a r) =
      r • degreeZeroFraction (k := k) I a := by
  rw [degreeZeroFractionLinearMap,
    Finsupp.linearCombination_single]

/-- Forget the degree and admissibility proofs on a Laurent exponent. -/
def admissibleExponentEmbedding
    (I : Finset ι) :
    AdmissibleExponent (ι := ι) 0 I ↪ ProjectiveExponent ι :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Extend a Laurent coefficient family by zero from the admissible
degree-zero exponents to all Laurent exponents. -/
def admissibleExponentLinearMap [CommRing k]
    (I : Finset (Fin (d + 1))) :
    MonomialModule (ι := Fin (d + 1)) k 0 I →ₗ[k]
      LaurentAlgebra k (Fin (d + 1)) where
  toFun f := AddMonoidAlgebra.ofCoeff
    (Finsupp.embDomain (admissibleExponentEmbedding I) f)
  map_add' f g := by
    ext b
    classical
    simp [Finsupp.embDomain_apply]
  map_smul' r f := by
    ext b
    classical
    simp [Finsupp.embDomain_apply]

lemma admissibleExponentLinearMap_apply [CommRing k]
    (I : Finset (Fin (d + 1)))
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    admissibleExponentLinearMap (k := k) I f =
      AddMonoidAlgebra.ofCoeff
        (Finsupp.embDomain (admissibleExponentEmbedding I) f) := by
  rfl

lemma homogeneousAwayToLaurent_comp_fractionLinearMap
    [CommRing k] (I : Finset (Fin (d + 1)))
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    homogeneousAwayToLaurentLinearMap (k := k) (d := d) I
        (degreeZeroFractionLinearMap (k := k) I f) =
      AddMonoidAlgebra.ofCoeff
        (Finsupp.embDomain (admissibleExponentEmbedding I) f) := by
  have hmaps :
      (homogeneousAwayToLaurentLinearMap (k := k) (d := d) I).comp
          (degreeZeroFractionLinearMap (k := k) I) =
        admissibleExponentLinearMap (k := k) I := by
    apply Finsupp.lhom_ext
    intro a r
    rw [LinearMap.comp_apply, degreeZeroFractionLinearMap_single,
      (homogeneousAwayToLaurentLinearMap
        (k := k) (d := d) I).map_smul,
      admissibleExponentLinearMap_apply,
      Finsupp.embDomain_single]
    ext b
    change
      r *
          (homogeneousAwayToLaurent (k := k) (d := d) I
            (degreeZeroFraction (k := k) I a)).coeff b =
        Finsupp.single ((admissibleExponentEmbedding I) a) r b
    rw [homogeneousAwayToLaurent_degreeZeroFraction]
    classical
    by_cases h : (a : ProjectiveExponent (Fin (d + 1))) = b <;>
      simp [admissibleExponentEmbedding, Finsupp.single_apply, h]
  have := DFunLike.congr_fun hmaps f
  rw [LinearMap.comp_apply, admissibleExponentLinearMap_apply] at this
  exact this

theorem degreeZeroFractionLinearMap_injective
    [CommRing k] (I : Finset (Fin (d + 1))) :
    Function.Injective (degreeZeroFractionLinearMap (k := k) I) := by
  intro f g hfg
  have hemb :
      AddMonoidAlgebra.ofCoeff
          (Finsupp.embDomain (admissibleExponentEmbedding I) f) =
        AddMonoidAlgebra.ofCoeff
          (Finsupp.embDomain (admissibleExponentEmbedding I) g) := by
    calc
      _ = homogeneousAwayToLaurentLinearMap (k := k) (d := d) I
            (degreeZeroFractionLinearMap (k := k) I f) :=
        (homogeneousAwayToLaurent_comp_fractionLinearMap I f).symm
      _ = homogeneousAwayToLaurentLinearMap (k := k) (d := d) I
            (degreeZeroFractionLinearMap (k := k) I g) :=
        congrArg
          (homogeneousAwayToLaurentLinearMap (k := k) (d := d) I)
          hfg
      _ = _ :=
        homogeneousAwayToLaurent_comp_fractionLinearMap I g
  exact Finsupp.embDomain_injective (admissibleExponentEmbedding I)
    (congrArg AddMonoidAlgebra.coeff hemb)

/-- The Laurent exponent obtained from a polynomial numerator monomial
after dividing by the `n`th power of the product of the variables in `I`. -/
def numeratorLaurentExponent (I : Finset ι) (n : ℕ)
    (e : ι →₀ ℕ) : ProjectiveExponent ι :=
  naturalExponent e - n • indicatorExponent I

@[simp]
lemma numeratorLaurentExponent_apply (I : Finset ι) (n : ℕ)
    (e : ι →₀ ℕ) (i : ι) :
    numeratorLaurentExponent I n e i =
      (e i : ℤ) - n * if i ∈ I then 1 else 0 := by
  simp [numeratorLaurentExponent, indicatorExponent]

lemma numeratorLaurentExponent_totalDegree
    (I : Finset ι) (n : ℕ) (e : ι →₀ ℕ)
    (he : e.degree = n * I.card) :
    ProjectiveExponent.totalDegree
        (numeratorLaurentExponent I n e) = 0 := by
  rw [numeratorLaurentExponent,
    ProjectiveExponent.totalDegree_sub,
    totalDegree_naturalExponent, totalDegree_nsmul,
    totalDegree_indicatorExponent, he]
  push_cast
  ring

lemma numeratorLaurentExponent_admissible
    (I : Finset ι) (n : ℕ) (e : ι →₀ ℕ) :
    ProjectiveExponent.AdmissibleOn
      (numeratorLaurentExponent I n e) I := by
  rw [ProjectiveExponent.admissibleOn_iff_nonnegative_outside]
  intro i hi
  simp [numeratorLaurentExponent_apply, hi]

/-- Package a homogeneous numerator exponent as an admissible
degree-zero Laurent exponent. -/
def admissibleNumeratorExponent
    (I : Finset ι) (n : ℕ) (e : ι →₀ ℕ)
    (he : e.degree = n * I.card) :
    AdmissibleExponent (ι := ι) 0 I :=
  ⟨numeratorLaurentExponent I n e,
    numeratorLaurentExponent_totalDegree I n e he,
    numeratorLaurentExponent_admissible I n e⟩

@[simp]
lemma admissibleNumeratorExponent_val
    (I : Finset ι) (n : ℕ) (e : ι →₀ ℕ)
    (he : e.degree = n * I.card) :
    (admissibleNumeratorExponent I n e he).1 =
      numeratorLaurentExponent I n e :=
  rfl

lemma homogeneousNumerator_support_degree [CommRing k]
    (I : Finset (Fin (d + 1))) (n : ℕ)
    (p : MvPolynomial (Fin (d + 1)) k)
    (hp :
      p ∈ homogeneousGrading k d (n • I.card))
    {e : Fin (d + 1) →₀ ℕ} (he : e ∈ p.support) :
    e.degree = n * I.card := by
  have hhom : p.IsHomogeneous (n * I.card) := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp
    simpa [nsmul_eq_mul] using hp
  rw [Finsupp.degree_apply]
  exact (hhom.degree_eq_sum_deg_support he).symm

/-- The Laurent coefficient family represented by a homogeneous
polynomial numerator divided by a power of the variable product. -/
noncomputable def homogeneousNumeratorPreimage [CommRing k]
    (I : Finset (Fin (d + 1))) (n : ℕ)
    (p : MvPolynomial (Fin (d + 1)) k)
    (hp : p ∈ homogeneousGrading k d (n • I.card)) :
    MonomialModule (ι := Fin (d + 1)) k 0 I :=
  ∑ e ∈ p.support.attach,
    Finsupp.single
      (admissibleNumeratorExponent I n e.1
        (homogeneousNumerator_support_degree I n p hp
          e.2))
      (MvPolynomial.coeff e.1 p)

lemma admissibleExponentLinearMap_homogeneousNumeratorPreimage
    [CommRing k]
    (I : Finset (Fin (d + 1))) (n : ℕ)
    (p : MvPolynomial (Fin (d + 1)) k)
    (hp : p ∈ homogeneousGrading k d (n • I.card)) :
    admissibleExponentLinearMap (k := k) I
        (homogeneousNumeratorPreimage I n p hp) =
      ∑ e ∈ p.support.attach,
        AddMonoidAlgebra.single (numeratorLaurentExponent I n e.1)
          (MvPolynomial.coeff e.1 p) := by
  simp only [homogeneousNumeratorPreimage, map_sum,
    admissibleExponentLinearMap_apply, Finsupp.embDomain_single,
    admissibleNumeratorExponent_val]
  rfl

lemma homogeneousAwayToLaurent_mk_eq_support_sum [CommRing k]
    (I : Finset (Fin (d + 1))) (n : ℕ)
    (p : MvPolynomial (Fin (d + 1)) k)
    (hp : p ∈ homogeneousGrading k d (n • I.card)) :
    homogeneousAwayToLaurent (k := k) (d := d) I
        (HomogeneousLocalization.Away.mk
          (homogeneousGrading k d)
          (variableProduct_mem_degreeCard I)
          n p hp) =
      ∑ e ∈ p.support.attach,
        AddMonoidAlgebra.single (numeratorLaurentExponent I n e.1)
          (MvPolynomial.coeff e.1 p) := by
  change
    localizationToLaurent (k := k) I
        (HomogeneousLocalization.val
          (HomogeneousLocalization.Away.mk
            (homogeneousGrading k d)
            (variableProduct_mem_degreeCard I)
            n p hp)) = _
  rw [HomogeneousLocalization.Away.val_mk,
    localizationToLaurent_mk]
  have hp_sum :
      p = ∑ e ∈ p.support.attach,
        MvPolynomial.monomial e.1
          (MvPolynomial.coeff e.1 p) := by
    calc
      p = ∑ e ∈ p.support,
          MvPolynomial.monomial e
            (MvPolynomial.coeff e p) :=
        MvPolynomial.as_sum p
      _ = ∑ e ∈ p.support.attach,
          MvPolynomial.monomial e.1
            (MvPolynomial.coeff e.1 p) :=
        (Finset.sum_attach p.support
          (fun e => MvPolynomial.monomial e
            (MvPolynomial.coeff e p))).symm
  nth_rw 1 [hp_sum]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [polynomialToLaurent_monomial, variableProductInverse,
    AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single]
  congr 1
  · simp [numeratorLaurentExponent, sub_eq_add_neg]
  · simp

lemma degreeZeroFractionLinearMap_homogeneousNumeratorPreimage
    [CommRing k] (I : Finset (Fin (d + 1))) (n : ℕ)
    (p : MvPolynomial (Fin (d + 1)) k)
    (hp : p ∈ homogeneousGrading k d (n • I.card)) :
    degreeZeroFractionLinearMap (k := k) I
        (homogeneousNumeratorPreimage I n p hp) =
      HomogeneousLocalization.Away.mk
        (homogeneousGrading k d)
        (variableProduct_mem_degreeCard I)
        n p hp := by
  apply homogeneousAwayToLaurent_injective I
  change
    homogeneousAwayToLaurentLinearMap (k := k) (d := d) I
        (degreeZeroFractionLinearMap (k := k) I
          (homogeneousNumeratorPreimage I n p hp)) =
      homogeneousAwayToLaurent (k := k) (d := d) I
        (HomogeneousLocalization.Away.mk
          (homogeneousGrading k d)
          (variableProduct_mem_degreeCard I)
          n p hp)
  rw [homogeneousAwayToLaurent_comp_fractionLinearMap,
    ← admissibleExponentLinearMap_apply,
    admissibleExponentLinearMap_homogeneousNumeratorPreimage,
    homogeneousAwayToLaurent_mk_eq_support_sum]

theorem degreeZeroFractionLinearMap_surjective
    [CommRing k] (I : Finset (Fin (d + 1))) :
    Function.Surjective
      (degreeZeroFractionLinearMap (k := k) I) := by
  intro x
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (𝒜 := homogeneousGrading k d)
      (f := variableProduct (k := k) I)
      (variableProduct_mem_degreeCard I) x
  exact
    ⟨homogeneousNumeratorPreimage I n p hp,
      degreeZeroFractionLinearMap_homogeneousNumeratorPreimage
        I n p hp⟩

/-- The degree-zero part of the homogeneous localization away from a
coordinate product has the expected Laurent monomial basis. -/
noncomputable def degreeZeroFractionLinearEquiv
    [CommRing k] (I : Finset (Fin (d + 1))) :
    MonomialModule (ι := Fin (d + 1)) k 0 I ≃ₗ[k]
      HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) I) :=
  LinearEquiv.ofBijective
    (degreeZeroFractionLinearMap (k := k) I)
    ⟨degreeZeroFractionLinearMap_injective I,
      degreeZeroFractionLinearMap_surjective I⟩

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
