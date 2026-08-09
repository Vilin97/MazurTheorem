/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.RingTheory.Etale.Finite

/-!
# The arithmetic obstruction for constant-prime finite-étale torsors over `Spec ℤ`

A torsor under the constant prime group over `Spec ℤ` is finite étale.  If it is nontrivial,
prime-order transitivity should make it connected; its coordinate algebra would then be a domain
of rank equal to that prime.  This file closes the arithmetic endpoint of that argument.

Mathlib's ramification theorem says that a finite unramified domain over `ℤ` is `ℤ`.  Since a
finite étale algebra is unramified, we promote that result to an actual algebra equivalence.
Consequently no domain finite étale `ℤ`-algebra has prime rank, with concrete endpoints at five
and eleven.

This does not yet prove that global fppf `H¹` of the represented constant group is trivial.  The
repository has no checked effective-descent construction taking an arbitrary global Čech class
to its finite-étale torsor algebra, nor the connected-or-trivial dichotomy for a prime-order
torsor.  Those geometric premises are not replaced here by certificates.
-/

noncomputable section

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

universe u

variable (A : Type u) [CommRing A] [Module.Finite ℤ A] [Algebra.Etale ℤ A]
  [IsDomain A]

/-- The structural map of a domain finite étale algebra over `ℤ` is bijective.  This is the
arithmetic no-unramified-extension theorem applied to the actual finite-étale object. -/
theorem algebraMap_bijective : Function.Bijective (algebraMap ℤ A) :=
  bijective_algebraMap_int_of_finite_of_unramified

/-- A domain finite étale algebra over `ℤ` is actually equivalent to `ℤ` as a `ℤ`-algebra. -/
noncomputable def intAlgEquiv : ℤ ≃ₐ[ℤ] A :=
  AlgEquiv.ofBijective (Algebra.ofId ℤ A) (algebraMap_bijective A)

/-- A domain finite étale `ℤ`-algebra has module rank one. -/
theorem finrank_eq_one : Module.finrank ℤ A = 1 := by
  rw [← (intAlgEquiv A).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- There is no domain finite étale `ℤ`-algebra of prime module rank.  This is the precise
arithmetic contradiction required once a nontrivial constant-prime torsor has been shown to
produce a connected finite-étale algebra. -/
theorem not_isDomain_of_finrank_eq_prime
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (p : ℕ) (hp : p.Prime)
    (hrank : Module.finrank ℤ B = p) : ¬ IsDomain B := by
  intro hB
  letI : IsDomain B := hB
  exact hp.ne_one (((finrank_eq_one B).symm.trans hrank).symm)

/-- A connected constant-order-five torsor algebra cannot be a domain finite étale algebra of
its expected rank. -/
theorem not_isDomain_of_finrank_eq_five
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 5) : ¬ IsDomain B :=
  not_isDomain_of_finrank_eq_prime B 5 (by decide) hrank

/-- A connected constant-order-eleven torsor algebra cannot be a domain finite étale algebra of
its expected rank. -/
theorem not_isDomain_of_finrank_eq_eleven
    (B : Type u) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 11) : ¬ IsDomain B :=
  not_isDomain_of_finrank_eq_prime B 11 (by decide) hrank

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale
