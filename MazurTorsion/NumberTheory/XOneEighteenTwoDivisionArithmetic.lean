/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenRealCubicQuotient
import EllipticCurves.Mathlib.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Exact arithmetic for the `X₁(18)` two-division algebra

This file records the exact algebraic-number certificates used by the
two-descent on the real-cubic elliptic quotient.  The rational cubic

`S³ - 3S - 10`

is proved irreducible by reduction modulo `11`.  We then form its relative
base change to the real cubic field `K = ℚ(τ)`.  All displayed relative
norm identities are checked in the kernel by the resultant formula for a
monogenic cubic algebra.

The relative object is deliberately called an algebra here: its field
structure is supplied only after a separate primitive-element certificate
proves that the two cubic fields are linearly disjoint.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

namespace Q

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K
abbrev tau := MazurTorsion.XOneEighteenRealCubicQuotient.tau
abbrev cubicPolynomial :=
  MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial
theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial :=
  MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial_irreducible
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 :=
  MazurTorsion.XOneEighteenRealCubicQuotient.tau_cubic

end Q

/-- The real cyclic coefficient cubic has positive power-basis
discriminant `81`. -/
theorem coefficientPolynomial_discriminant :
    Q.cubicPolynomial.discr = 81 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      coeff_sub, coeff_add, coeff_mul,
      coeff_X_pow, coeff_X, coeff_one]
  · have hdegree : Q.cubicPolynomial.natDegree = 3 := by
      simp only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
      compute_degree!
    rw [degree_eq_natDegree Q.cubicPolynomial_irreducible.ne_zero, hdegree]
    norm_num

/-! ## The rational two-division cubic -/

private def twoDivisionPolynomialInt : Polynomial ℤ :=
  X ^ 3 - 3 * X - 10

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

private theorem twoDivisionPolynomialInt_monic :
    twoDivisionPolynomialInt.Monic := by
  simp only [twoDivisionPolynomialInt]
  monicity <;> norm_num

private theorem twoDivisionPolynomialInt_mod_eleven :
    twoDivisionPolynomialInt.map (Int.castRingHom (ZMod 11)) =
      (X ^ 3 + 8 * X + 1 : Polynomial (ZMod 11)) := by
  norm_num [twoDivisionPolynomialInt]
  have hthree : (3 : ZMod 11) = -8 := by decide
  have hten : (10 : ZMod 11) = -1 := by decide
  rw [← Polynomial.C_ofNat 3, ← Polynomial.C_ofNat 10,
    ← Polynomial.C_ofNat 8, ← Polynomial.C_1]
  rw [hthree, hten]
  simp only [map_neg]
  ring

private theorem twoDivisionPolynomial_mod_eleven_irreducible :
    Irreducible (X ^ 3 + 8 * X + 1 : Polynomial (ZMod 11)) := by
  have hdegree :
      (X ^ 3 + 8 * X + 1 : Polynomial (ZMod 11)).natDegree = 3 := by
    compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := (X ^ 3 + 8 * X + 1 : Polynomial (ZMod 11))) ?_ ?_
  · rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    rw [eval_add, eval_add, eval_pow, eval_X, eval_mul, eval_ofNat, eval_X,
      eval_one]
    fin_cases z <;> decide

private theorem twoDivisionPolynomialInt_irreducible :
    Irreducible twoDivisionPolynomialInt := by
  apply twoDivisionPolynomialInt_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 11))
  simpa only [twoDivisionPolynomialInt_mod_eleven] using
    twoDivisionPolynomial_mod_eleven_irreducible

/-- The irreducible rational cubic governing the nontrivial two-torsion of
the rational model `[1,-1,1,25,1]`. -/
def twoDivisionPolynomial : Polynomial ℚ :=
  X ^ 3 - 3 * X - 10

private theorem twoDivisionPolynomial_eq_map_int :
    twoDivisionPolynomialInt.map (algebraMap ℤ ℚ) =
      twoDivisionPolynomial := by
  norm_num [twoDivisionPolynomialInt, twoDivisionPolynomial]

/-- Irreducibility of `S³ - 3S - 10` over `ℚ`. -/
theorem twoDivisionPolynomial_irreducible :
    Irreducible twoDivisionPolynomial := by
  rw [← twoDivisionPolynomial_eq_map_int]
  exact
    (twoDivisionPolynomialInt_monic.irreducible_iff_irreducible_map_fraction_map
      (K := ℚ)).mp twoDivisionPolynomialInt_irreducible

instance twoDivisionPolynomial_irreducibleFact :
    Fact (Irreducible twoDivisionPolynomial) :=
  ⟨twoDivisionPolynomial_irreducible⟩

theorem twoDivisionPolynomial_natDegree :
    twoDivisionPolynomial.natDegree = 3 := by
  simp only [twoDivisionPolynomial]
  compute_degree!

/-- The negative power-basis discriminant which distinguishes this cubic
field from the real cyclic cubic coefficient field. -/
theorem twoDivisionPolynomial_discriminant :
    twoDivisionPolynomial.discr = -2592 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [twoDivisionPolynomial, coeff_sub, coeff_add, coeff_mul,
      coeff_X_pow, coeff_X, coeff_one]
  · rw [degree_eq_natDegree (twoDivisionPolynomial_irreducible.ne_zero),
      twoDivisionPolynomial_natDegree]
    norm_num

/-- The rational cubic two-division field. -/
abbrev F := AdjoinRoot twoDivisionPolynomial

/-- Its distinguished generator. -/
def sigma : F :=
  AdjoinRoot.root twoDivisionPolynomial

/-- The defining relation for `sigma`. -/
theorem sigma_cubic : sigma ^ 3 = 3 * sigma + 10 := by
  have h : AdjoinRoot.mk twoDivisionPolynomial twoDivisionPolynomial = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk twoDivisionPolynomial
    (X ^ 3 - 3 * X - 10 : Polynomial ℚ) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_ofNat,
    AdjoinRoot.mk_X] at h
  have h' : sigma ^ 3 - 3 * sigma - 10 = 0 := by
    simpa only [sigma] using h
  linear_combination h'

/-- The rational cubic field has degree `3`. -/
theorem finrank_F_over_rat : Module.finrank ℚ F = 3 := by
  rw [AdjoinRoot.finrank_eq_natDegree
    (twoDivisionPolynomial_irreducible.ne_zero),
    twoDivisionPolynomial_natDegree]

/-- The integral scaled abscissa of a nonzero two-torsion point. -/
def twoDivisionZ : F :=
  3 * sigma ^ 2 - 6 * sigma - 5

/-- `twoDivisionZ` satisfies the scaled completed two-division cubic. -/
theorem twoDivisionZ_cubic :
    twoDivisionZ ^ 3 - 3 * twoDivisionZ ^ 2 +
        408 * twoDivisionZ + 80 = 0 := by
  simp only [twoDivisionZ]
  linear_combination
    (27 * sigma ^ 3 - 162 * sigma ^ 2 + 243 * sigma + 216) *
      (sigma_cubic)

/-- Dividing the scaled coordinate by `4` gives a root of
`4X³ - 3X² + 102X + 5`, the completed two-division polynomial of the
rational model. -/
theorem twoDivisionX_cubic :
    4 * (twoDivisionZ / 4) ^ 3 - 3 * (twoDivisionZ / 4) ^ 2 +
        102 * (twoDivisionZ / 4) + 5 = 0 := by
  linear_combination (1 / 16 : F) * twoDivisionZ_cubic

/-! ## The relative cubic algebra over the quotient field -/

/-- The base-changed two-division polynomial over the real cubic field. -/
def relativePolynomial : Polynomial Q.K :=
  X ^ 3 - 3 * X - 10

theorem relativePolynomial_monic : relativePolynomial.Monic := by
  simp only [relativePolynomial]
  monicity <;> norm_num

theorem relativePolynomial_natDegree : relativePolynomial.natDegree = 3 := by
  simp only [relativePolynomial]
  compute_degree!

theorem relativePolynomial_discriminant :
    relativePolynomial.discr = -2592 := by
  rw [Polynomial.discr_of_degree_eq_three]
  · norm_num [relativePolynomial, coeff_sub, coeff_add, coeff_mul,
      coeff_X_pow, coeff_X, coeff_one]
  · rw [degree_eq_natDegree relativePolynomial_monic.ne_zero,
      relativePolynomial_natDegree]
    norm_num

/-- The relative cubic two-division algebra `K[S]/(S³-3S-10)`.

It is not declared to be a field in this module: that conclusion requires
the independent primitive-element/linear-disjointness certificate. -/
abbrev M := AdjoinRoot relativePolynomial

/-- The relative generator. -/
def s : M :=
  AdjoinRoot.root relativePolynomial

/-- The image of the real-cubic generator in the relative algebra. -/
def t : M :=
  algebraMap Q.K M Q.tau

/-- The coefficient-field relation remains exact after base change. -/
theorem t_cubic : t ^ 3 = 3 * t + 1 := by
  simpa only [t, map_pow, map_mul, map_ofNat, map_add, map_one] using
    congrArg (algebraMap Q.K M) Q.tau_cubic

/-- The defining relation in the relative cubic algebra. -/
theorem s_cubic : s ^ 3 = 3 * s + 10 := by
  have h : AdjoinRoot.mk relativePolynomial relativePolynomial = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk relativePolynomial
    (X ^ 3 - 3 * X - 10 : Polynomial Q.K) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_ofNat,
    AdjoinRoot.mk_X] at h
  have h' : s ^ 3 - 3 * s - 10 = 0 := by
    simpa only [s] using h
  linear_combination h'

/-- The relative cubic algebra has the expected rank `3` over `K`, without
using irreducibility. -/
theorem finrank_M_over_K : Module.finrank Q.K M = 3 := by
  rw [(AdjoinRoot.powerBasis' relativePolynomial_monic).finrank]
  exact relativePolynomial_natDegree

/-- Scaled completed two-division coordinate in the relative algebra. -/
def relativeTwoDivisionZ : M :=
  3 * s ^ 2 - 6 * s - 5

theorem relativeTwoDivisionZ_cubic :
    relativeTwoDivisionZ ^ 3 - 3 * relativeTwoDivisionZ ^ 2 +
        408 * relativeTwoDivisionZ + 80 = 0 := by
  simp only [relativeTwoDivisionZ]
  linear_combination
    (27 * s ^ 3 - 162 * s ^ 2 + 243 * s + 216) * s_cubic

/-! ## Exact relative norm certificates -/

/-- The canonical quadratic representative in the monogenic relative
cubic algebra. -/
def quadraticElement (a b c : Q.K) : M :=
  AdjoinRoot.mk relativePolynomial
    (C a * X ^ 2 + C b * X + C c)

theorem quadraticElement_eq (a b c : Q.K) :
    quadraticElement a b c =
      algebraMap Q.K M a * s ^ 2 + algebraMap Q.K M b * s +
        algebraMap Q.K M c := by
  simp [quadraticElement, s]

/-- The explicit power basis, reindexed by `Fin 3`. -/
def relativeBasis : Basis (Fin 3) Q.K M :=
  (AdjoinRoot.powerBasis' relativePolynomial_monic).basis.reindex
    (finCongr relativePolynomial_natDegree)

private theorem s_pow_four : s ^ 4 = 3 * s ^ 2 + 10 * s := by
  calc
    s ^ 4 = s * s ^ 3 := by ring
    _ = s * (3 * s + 10) := by rw [s_cubic]
    _ = 3 * s ^ 2 + 10 * s := by ring

/-- Closed formula for the relative norm of a quadratic representative.
This is the determinant of multiplication in the basis `1,s,s²`. -/
theorem norm_quadraticElement (a b c : Q.K) :
    Algebra.norm Q.K (quadraticElement a b c) =
      100 * a ^ 3 - 30 * a ^ 2 * b + 9 * a ^ 2 * c -
        30 * a * b * c + 6 * a * c ^ 2 + 10 * b ^ 3 -
        3 * b ^ 2 * c + c ^ 3 := by
  let pb := AdjoinRoot.powerBasis' relativePolynomial_monic
  rw [quadraticElement_eq, Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_add, map_mul, map_pow]
  rw [(Algebra.leftMulMatrix pb.basis).commutes a,
    (Algebra.leftMulMatrix pb.basis).commutes b,
    (Algebra.leftMulMatrix pb.basis).commutes c]
  have hs : s = pb.gen := rfl
  rw [hs, pb.leftMulMatrix]
  have hmin : pb.minpolyGen = relativePolynomial := by
    dsimp [pb]
    rw [PowerBasis.minpolyGen_eq,
      AdjoinRoot.powerBasis'_gen,
      AdjoinRoot.minpoly_root relativePolynomial_monic.ne_zero,
      relativePolynomial_monic.leadingCoeff, inv_one, C_1, mul_one]
  rw [hmin]
  have hdim : pb.dim = 3 := relativePolynomial_natDegree
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) Q.K :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -relativePolynomial.coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) a *
          companion ^ 2 +
        algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) b *
          companion +
      algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) c) = _
  have hcompanion :
      Matrix.reindexAlgEquiv Q.K Q.K e companion =
        !![0, 0, 10; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, relativePolynomial, coeff_sub,
        coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv Q.K (R := Q.K) e]
  rw [map_add, map_add, map_mul, map_pow, map_mul]
  rw [(Matrix.reindexAlgEquiv Q.K Q.K e).commutes a,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes b,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes c]
  rw [hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring

/-- A generator above the first dyadic prime of the compositum. -/
def alpha : M :=
  quadraticElement
    ((2 * Q.tau ^ 2 - Q.tau - 1) / 18)
    ((-4 * Q.tau ^ 2 - Q.tau + 11) / 18)
    ((-4 * Q.tau ^ 2 + 2 * Q.tau + 14) / 18)

/-- A generator above the second dyadic prime of the compositum. -/
def beta : M :=
  quadraticElement
    ((-Q.tau ^ 2 + 2 * Q.tau + 2) / 18)
    ((-Q.tau ^ 2 + 2 * Q.tau + 8) / 18)
    ((8 * Q.tau ^ 2 + 8 * Q.tau - 10) / 18)

/-- A generator above the prime over `3`. -/
def rho : M :=
  quadraticElement (-Q.tau / 6) ((Q.tau - 2) / 6)
    ((2 * Q.tau ^ 2 + 2 * Q.tau - 8) / 6)

/-- First norm-one squareclass generator. -/
def h1 : M :=
  quadraticElement
    ((-Q.tau ^ 2 + 2 * Q.tau + 2) / 18)
    ((-Q.tau ^ 2 + 2 * Q.tau + 8) / 18)
    ((4 * Q.tau ^ 2 - 5 * Q.tau - 5) / 9)

/-- Second norm-one squareclass generator. -/
def h2 : M :=
  quadraticElement (1 / 6) (1 / 6)
    ((Q.tau ^ 2 + Q.tau) / 3 - 1)

/-- First generator of relative norm `4`. -/
def h3 : M :=
  quadraticElement
    ((2 * Q.tau ^ 2 - Q.tau + 2) / 18)
    ((2 * Q.tau ^ 2 - 7 * Q.tau + 14) / 18)
    ((4 * Q.tau ^ 2 - 5 * Q.tau + 4) / 9)

/-- Second generator whose norm is an explicit square in `K`. -/
def h4 : M :=
  quadraticElement ((-Q.tau ^ 2 + 3) / 6)
    ((Q.tau ^ 2 + 1) / 6) (Q.tau ^ 2 - 5 / 3)

end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic
