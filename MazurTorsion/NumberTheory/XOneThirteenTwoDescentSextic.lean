/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenFiniteField
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ReduceModChar

/-!
# The sextic algebra for a two-descent on `X₁(13)`

This file isolates the concrete degree-six algebra used before a two-descent
on the genus-two model

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

The descent framework is Michael Stoll, *Implementing 2-descent for
Jacobians of hyperelliptic curves*, Acta Arithmetica 98 (2001), 245–277,
§5, DOI 10.4064/aa98-3-4.  The official publisher download used for the
audit is licensed CC BY.  The concrete polynomial certificates below were
independently recomputed exactly; no third-party source code is retained in
this file.
-/

namespace MazurTorsion.XOneThirteenTwoDescentSextic

open Polynomial

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The integral sextic defining the concrete `X₁(13)` model. -/
def sextic : ℤ[X] :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- The reduction of the integral sextic modulo `3`. -/
def sexticModThree : (ZMod 3)[X] :=
  sextic.map (Int.castRingHom (ZMod 3))

theorem sextic_isMonicOfDegree : IsMonicOfDegree sextic 6 := by
  rw [isMonicOfDegree_iff']
  constructor
  · simp only [sextic]
    compute_degree!
  · simp only [sextic]
    monicity!

theorem sextic_monic : sextic.Monic :=
  sextic_isMonicOfDegree.monic

theorem sexticModThree_eq_finiteFieldSextic :
    sexticModThree = XOneThirteenFiniteField.sextic := by
  simp [sexticModThree, sextic, XOneThirteenFiniteField.sextic]

private def cyclotomicQuotientA : (ZMod 3)[X] :=
  X ^ 66 - X ^ 64 + X ^ 62 - X ^ 61 + X ^ 59 + X ^ 57 -
    X ^ 56 - X ^ 55 + X ^ 52 + X ^ 50

private def cyclotomicQuotientB : (ZMod 3)[X] :=
  -X ^ 48 - X ^ 47 - X ^ 45 - X ^ 44 + X ^ 43 - X ^ 41 -
    X ^ 40 - X ^ 39 - X ^ 38 + X ^ 36

private def cyclotomicQuotientC : (ZMod 3)[X] :=
  -X ^ 35 - X ^ 33 - X ^ 32 - X ^ 31 + X ^ 30 - X ^ 29 +
    X ^ 28 + X ^ 25 + X ^ 24

private def cyclotomicQuotientD : (ZMod 3)[X] :=
  -X ^ 23 + X ^ 22 + X ^ 20 - X ^ 18 - X ^ 16 + X ^ 14 +
    X ^ 13 + X ^ 12

private def cyclotomicQuotientE : (ZMod 3)[X] :=
  -X ^ 11 - X ^ 7 - X ^ 6 + X ^ 5 + X ^ 4 - X ^ 3 -
    X ^ 2 + X + 1

/-- The explicitly checked cofactor of the sextic inside the reduction of
the ninety-first cyclotomic polynomial. -/
private def cyclotomicQuotient : (ZMod 3)[X] :=
  cyclotomicQuotientA + cyclotomicQuotientB + cyclotomicQuotientC +
    cyclotomicQuotientD + cyclotomicQuotientE

private theorem sexticModThree_mul_cyclotomicQuotient_mul_cyclotomic_thirteen :
    (sexticModThree * cyclotomicQuotient) * cyclotomic 13 (ZMod 3) =
      expand (ZMod 3) 7 (cyclotomic 13 (ZMod 3)) := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  rw [cyclotomic_prime]
  simp only [map_sum, map_pow, expand_X]
  simp [sexticModThree, sextic, cyclotomicQuotient,
    cyclotomicQuotientA, cyclotomicQuotientB, cyclotomicQuotientC,
    cyclotomicQuotientD, cyclotomicQuotientE, Finset.sum_range_succ]
  ring_nf
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- Exact divisibility certificate inside `Φ₉₁` over `ZMod 3`. -/
theorem sexticModThree_dvd_cyclotomic_ninetyOne :
    sexticModThree ∣ cyclotomic 91 (ZMod 3) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hExpand := cyclotomic_expand_eq_cyclotomic_mul
    (p := 7) (n := 13) (by decide) (by decide) (ZMod 3)
  have hmul :
      (sexticModThree * cyclotomicQuotient) * cyclotomic 13 (ZMod 3) =
        cyclotomic 91 (ZMod 3) * cyclotomic 13 (ZMod 3) :=
    sexticModThree_mul_cyclotomicQuotient_mul_cyclotomic_thirteen.trans hExpand
  have hfactor :
      sexticModThree * cyclotomicQuotient = cyclotomic 91 (ZMod 3) :=
    mul_right_cancel₀ (cyclotomic_ne_zero 13 (ZMod 3)) hmul
  exact ⟨cyclotomicQuotient, hfactor.symm⟩

theorem sexticModThree_natDegree : sexticModThree.natDegree = 6 := by
  rw [sexticModThree, sextic_monic.natDegree_map,
    sextic_isMonicOfDegree.natDegree_eq]

private theorem orderOf_three_mod_ninetyOne :
    orderOf (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 91)) = 6 := by
  rw [orderOf_eq_iff (by decide : 0 < 6)]
  constructor
  · apply Units.ext
    decide
  · intro m hm hpos
    interval_cases m <;> apply_fun Units.val <;> decide

/-- The mod-`3` sextic is irreducible.  The certificate is finite: it is a
degree-six factor of `Φ₉₁`, and `3` has multiplicative order six modulo
`91`. -/
theorem sexticModThree_irreducible : Irreducible sexticModThree := by
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree
    (p := 3) (n := 91) (by decide) sexticModThree_dvd_cyclotomic_ninetyOne
  rw [sexticModThree_natDegree]
  exact orderOf_three_mod_ninetyOne.symm

/-- Irreducibility over the integers, lifted from reduction modulo `3`. -/
theorem sextic_irreducible : Irreducible sextic := by
  apply sextic_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 3)) sextic
  exact sexticModThree_irreducible

/-- The integral sextic is squarefree. -/
theorem sextic_squarefree : Squarefree sextic :=
  sextic_irreducible.squarefree

/-- The defining polynomial after extension of scalars to the rationals. -/
def rationalSextic : ℚ[X] :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

theorem rationalSextic_eq_map :
    rationalSextic = sextic.map (algebraMap ℤ ℚ) := by
  simp [rationalSextic, sextic]

/-- Irreducibility of the sextic over `ℚ`. -/
theorem rationalSextic_irreducible : Irreducible rationalSextic := by
  rw [rationalSextic_eq_map]
  exact sextic_monic.irreducible_iff_irreducible_map_fraction_map.mp
    sextic_irreducible

/-- Squarefreeness over `ℚ`, the hypothesis needed by the étale-algebra
stage of a two-descent. -/
theorem rationalSextic_squarefree : Squarefree rationalSextic :=
  rationalSextic_irreducible.squarefree

/-- The integral polynomial whose value at a root of the sextic generates
the visible quadratic subfield. -/
def quadraticElementPolynomial : ℤ[X] :=
  4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + 8 * X ^ 2 + 22 * X + 9

/-- The quotient in the exact quadratic-subfield certificate. -/
def quadraticCertificateQuotient : ℤ[X] :=
  16 * X ^ 4 + 16 * X ^ 3 + 4 * X ^ 2 + 32 * X + 80

/-- The exact integral certificate behind the quadratic subfield. -/
theorem quadraticElementPolynomial_spec :
    quadraticElementPolynomial ^ 2 - 2 * quadraticElementPolynomial + 17 =
      quadraticCertificateQuotient * sextic := by
  simp only [quadraticElementPolynomial, quadraticCertificateQuotient, sextic]
  ring

/-- The degree-six field cut out by the rational sextic. -/
abbrev SexticField := AdjoinRoot rationalSextic

/-- The distinguished root of the defining sextic. -/
def theta : SexticField :=
  AdjoinRoot.root rationalSextic

theorem theta_spec :
    theta ^ 6 + 2 * theta ^ 5 + theta ^ 4 + 2 * theta ^ 3 +
      6 * theta ^ 2 + 4 * theta + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root rationalSextic
  change Polynomial.eval₂ (AdjoinRoot.of rationalSextic)
      (AdjoinRoot.root rationalSextic)
      (X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
        6 * X ^ 2 + 4 * X + 1 : ℚ[X]) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat,
    Polynomial.eval₂_one] at h
  simpa only [theta] using h

/-- The concrete element returned by the exact subfield calculation. -/
def quadraticElement : SexticField :=
  4 * theta ^ 5 + 6 * theta ^ 4 + 2 * theta ^ 3 +
    8 * theta ^ 2 + 22 * theta + 9

/-- The concrete element satisfies `u² - 2u + 17 = 0`. -/
theorem quadraticElement_spec :
    quadraticElement ^ 2 - 2 * quadraticElement + 17 = 0 := by
  calc
    quadraticElement ^ 2 - 2 * quadraticElement + 17 =
        (16 * theta ^ 4 + 16 * theta ^ 3 + 4 * theta ^ 2 +
          32 * theta + 80) *
        (theta ^ 6 + 2 * theta ^ 5 + theta ^ 4 + 2 * theta ^ 3 +
          6 * theta ^ 2 + 4 * theta + 1) := by
      simp only [quadraticElement]
      ring
    _ = 0 := by rw [theta_spec, mul_zero]

/-- The resulting square root of `-1` in the sextic field. -/
def sqrtNegOne : SexticField := by
  letI : Fact (Irreducible rationalSextic) :=
    ⟨rationalSextic_irreducible⟩
  exact (quadraticElement - 1) / 4

theorem sqrtNegOne_sq : sqrtNegOne ^ 2 = -1 := by
  letI : Fact (Irreducible rationalSextic) :=
    ⟨rationalSextic_irreducible⟩
  have hu := quadraticElement_spec
  have hdiff : (quadraticElement - 1) ^ 2 = -16 := by
    linear_combination hu
  rw [sqrtNegOne, div_pow, hdiff]
  norm_num

end

end MazurTorsion.XOneThirteenTwoDescentSextic
