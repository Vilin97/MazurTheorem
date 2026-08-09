/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellQuadratic

/-!
# The quadratic endomorphism arithmetic at level thirteen

The diamond operator on the Jacobian of `X₁(13)` satisfies
`γ² - γ + 1 = 0`.  This file isolates the elementary additive-group
calculation behind the factorization

`(3 + 2γ)(5 - 2γ) = 19`.

Nothing here constructs a Jacobian or asserts that a particular geometric
endomorphism satisfies the relation.  A later curve-specific construction can
use `prime_comp_conjugate` and `conjugate_comp_prime` without repeating this
arithmetic.
-/

namespace MazurTorsion.XOneThirteenEndomorphismArithmetic

variable {A : Type*} [AddCommGroup A]

/-- Pointwise form of the quadratic relation `γ² - γ + 1 = 0`. -/
def SatisfiesQuadraticRelation (γ : A →+ A) : Prop :=
  ∀ x, γ (γ x) = γ x - x

/-- The prime-over-`19` additive endomorphism `3 + 2γ`. -/
def primeEndomorphism (γ : A →+ A) : A →+ A :=
  3 • AddMonoidHom.id A + 2 • γ

/-- The conjugate prime-over-`19` additive endomorphism `5 - 2γ`. -/
def conjugatePrimeEndomorphism (γ : A →+ A) : A →+ A :=
  5 • AddMonoidHom.id A - 2 • γ

@[simp]
theorem primeEndomorphism_apply (γ : A →+ A) (x : A) :
    primeEndomorphism γ x = 3 • x + 2 • γ x := by
  simp [primeEndomorphism]

@[simp]
theorem conjugatePrimeEndomorphism_apply (γ : A →+ A) (x : A) :
    conjugatePrimeEndomorphism γ x = 5 • x - 2 • γ x := by
  simp [conjugatePrimeEndomorphism]

/-- The two conjugate endomorphisms multiply to `[19]`. -/
theorem prime_comp_conjugate
    (γ : A →+ A) (hγ : SatisfiesQuadraticRelation γ) :
    (primeEndomorphism γ).comp (conjugatePrimeEndomorphism γ) =
      19 • AddMonoidHom.id A := by
  ext x
  simp only [AddMonoidHom.comp_apply, primeEndomorphism_apply,
    conjugatePrimeEndomorphism_apply, map_sub, map_nsmul,
    AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]
  rw [hγ x]
  abel

/-- The factorization is commutative for the two polynomials in `γ`. -/
theorem conjugate_comp_prime
    (γ : A →+ A) (hγ : SatisfiesQuadraticRelation γ) :
    (conjugatePrimeEndomorphism γ).comp (primeEndomorphism γ) =
      19 • AddMonoidHom.id A := by
  ext x
  simp only [AddMonoidHom.comp_apply, primeEndomorphism_apply,
    conjugatePrimeEndomorphism_apply, map_add, map_nsmul,
    AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]
  rw [hγ x]
  abel

/-- The first prime factor kills an eigenvector with eigenvalue `8`, once
that vector is killed by `19`. -/
theorem primeEndomorphism_eq_zero_of_eigenvalue_eight
    (γ : A →+ A) (D : A) (hγD : γ D = 8 • D)
    (hD : 19 • D = 0) :
    primeEndomorphism γ D = 0 := by
  rw [primeEndomorphism_apply, hγD]
  rw [show 3 • D + 2 • (8 • D) = 19 • D by abel, hD]

/-- The conjugate prime factor kills an eigenvector with eigenvalue `12`,
once that vector is killed by `19`. -/
theorem conjugatePrimeEndomorphism_eq_zero_of_eigenvalue_twelve
    (γ : A →+ A) (D : A) (hγD : γ D = 12 • D)
    (hD : 19 • D = 0) :
    conjugatePrimeEndomorphism γ D = 0 := by
  rw [conjugatePrimeEndomorphism_apply, hγD]
  rw [show 5 • D - 2 • (12 • D) = -((19 • D) : A) by abel,
    hD, neg_zero]

end MazurTorsion.XOneThirteenEndomorphismArithmetic
