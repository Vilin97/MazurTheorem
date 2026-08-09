/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenEndomorphismArithmetic
import MazurTorsion.GroupTheory.IndexNSmulFG
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# The finitely generated endpoint of the level-thirteen prime descent

This file records the abstract group-theoretic endpoint of the Mazur--Tate
prime-over-`19` argument.  Suppose an endomorphism `gamma` satisfies
`gamma^2 - gamma + 1 = 0`, and an additive equivalence `tau` sends `gamma` to
its conjugate `1 - gamma`.  Then `tau` transports surjectivity of
`3 + 2 * gamma` to its conjugate `5 - 2 * gamma`.  Their product is
multiplication by `19`, so multiplication by `19` is surjective.

For a finitely generated abelian group, the index formula for multiplication
by `19` then forces the free rank to vanish.  The group is consequently
finite.  Involutivity of `tau`, as supplied by geometric complex conjugation,
is stronger than this argument needs: bijectivity and the displayed
intertwining identity suffice.

This is deliberately only an abstract endpoint.  It neither constructs the
Jacobian of `X_1(13)` nor asserts the required geometric surjectivity.
-/

namespace MazurTorsion.XOneThirteenEndomorphismArithmetic

variable {A : Type*} [AddCommGroup A]

/-- An additive equivalence conjugates `gamma` to `1 - gamma` when it
intertwines the two actions in this pointwise form. -/
def ConjugatesQuadraticEndomorphism
    (gamma : A →+ A) (tau : A ≃+ A) : Prop :=
  ∀ x, tau (gamma x) = tau x - gamma (tau x)

/-- Conjugating `gamma` to `1 - gamma` carries `3 + 2 * gamma` to
`5 - 2 * gamma`. -/
theorem map_primeEndomorphism_eq_conjugatePrimeEndomorphism_map
    (gamma : A →+ A) (tau : A ≃+ A)
    (htau : ConjugatesQuadraticEndomorphism gamma tau) (x : A) :
    tau (primeEndomorphism gamma x) =
      conjugatePrimeEndomorphism gamma (tau x) := by
  rw [primeEndomorphism_apply, conjugatePrimeEndomorphism_apply,
    map_add]
  simp only [map_nsmul]
  rw [htau]
  abel

/-- Surjectivity of the prime-over-`19` factor is transported to its
conjugate by the additive equivalence. -/
theorem conjugatePrimeEndomorphism_surjective_of_prime
    (gamma : A →+ A) (tau : A ≃+ A)
    (htau : ConjugatesQuadraticEndomorphism gamma tau)
    (hprime : Function.Surjective (primeEndomorphism gamma)) :
    Function.Surjective (conjugatePrimeEndomorphism gamma) := by
  intro y
  obtain ⟨z, rfl⟩ := tau.surjective y
  obtain ⟨x, hx⟩ := hprime z
  refine ⟨tau x, ?_⟩
  rw [← map_primeEndomorphism_eq_conjugatePrimeEndomorphism_map
    gamma tau htau x, hx]

/-- If the prime factor is surjective, conjugation and the norm
factorization make multiplication by `19` surjective. -/
theorem nineteen_nsmul_surjective_of_prime
    (gamma : A →+ A) (tau : A ≃+ A)
    (hgamma : SatisfiesQuadraticRelation gamma)
    (htau : ConjugatesQuadraticEndomorphism gamma tau)
    (hprime : Function.Surjective (primeEndomorphism gamma)) :
    Function.Surjective (nsmulAddMonoidHom (α := A) 19) := by
  have hconjugate :
      Function.Surjective (conjugatePrimeEndomorphism gamma) :=
    conjugatePrimeEndomorphism_surjective_of_prime gamma tau htau hprime
  have hcomposition :
      Function.Surjective
        ((primeEndomorphism gamma).comp
          (conjugatePrimeEndomorphism gamma)) :=
    hprime.comp hconjugate
  rw [prime_comp_conjugate gamma hgamma] at hcomposition
  have hscalar :
      19 • AddMonoidHom.id A = nsmulAddMonoidHom (α := A) 19 := by
    ext x
    simp
  rw [hscalar] at hcomposition
  exact hcomposition

/-- Surjectivity of multiplication by `19` forces the free rank of a
finitely generated abelian group to vanish. -/
theorem finrank_eq_zero_of_nineteen_nsmul_surjective
    [AddGroup.FG A]
    (hnineteen : Function.Surjective
      (nsmulAddMonoidHom (α := A) 19)) :
    Module.finrank ℤ A = 0 := by
  have hrange :
      (nsmulAddMonoidHom (α := A) 19).range = ⊤ :=
    (nsmulAddMonoidHom (α := A) 19).range_eq_top_of_surjective
      hnineteen
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg A
      (by norm_num : (19 : ℕ) ≠ 0)
  rw [hrange, AddSubgroup.index_top] at hformula
  have hpower : 19 ^ Module.finrank ℤ A = 1 :=
    (mul_eq_one.mp hformula.symm).1
  simpa using hpower

/-- The complete finitely-generated-group endpoint: a surjective
prime-over-`19` factor, together with quadratic conjugation, makes the group
finite. -/
theorem finite_of_primeEndomorphism_surjective
    [AddGroup.FG A]
    (gamma : A →+ A) (tau : A ≃+ A)
    (hgamma : SatisfiesQuadraticRelation gamma)
    (htau : ConjugatesQuadraticEndomorphism gamma tau)
    (hprime : Function.Surjective (primeEndomorphism gamma)) :
    Finite A := by
  letI : Module.Finite ℤ A :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG A)
  have hrank : Module.finrank ℤ A = 0 :=
    finrank_eq_zero_of_nineteen_nsmul_surjective
      (nineteen_nsmul_surjective_of_prime
        gamma tau hgamma htau hprime)
  have hmoduleTorsion : Module.IsTorsion ℤ A :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp hrank
  exact AddCommGroup.finite_of_fg_torsion A
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

end MazurTorsion.XOneThirteenEndomorphismArithmetic
