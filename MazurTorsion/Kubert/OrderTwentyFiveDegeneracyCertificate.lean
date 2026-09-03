/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Rat.Defs
import Lean.Elab.Tactic.Omega

/-!
# Checked bivariate certificates for the order-twenty-five degeneracy map

The large identities needed for the order-twenty-five degeneracy comparison
are checked coefficientwise.  A certificate is a little-endian table of
integer coefficients together with a small expression tree built from such
tables.  Closed `decide` proofs compare bounded batches of coefficients; the
results below lift those checks first to bivariate polynomials and then to
rational evaluations.

This deliberately small interface was reviewed for the three named downstream
consumers `OrderTwentyFiveDegeneracyPairCertificate`,
`OrderTwentyFiveDegeneracyPowerCertificate`, and
`OrderTwentyFiveDegeneracyFinalCertificate`.  Keeping evaluation separate from
the generated data lets those modules share one proof of certificate
soundness.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDegeneracyCertificate

open Polynomial

/-- A dense bivariate coefficient table.  Outer chunks contain eight rows;
each row is split into chunks of sixteen coefficients. -/
structure CoefficientTable where
  outerLength : ℕ
  innerLength : ℕ
  chunks : List (List (List (List ℤ)))
deriving DecidableEq

/-- Unchecked lookup in a chunked coefficient table, returning zero for any
missing chunk or entry. -/
def rawCoefficient (data : CoefficientTable) (outer inner : ℕ) : ℤ :=
  let outerChunk := data.chunks[outer / 8]?.getD []
  let row := outerChunk[outer % 8]?.getD []
  let innerChunk := row[inner / 16]?.getD []
  innerChunk[inner % 16]?.getD 0

/-- Coefficient lookup with the declared rectangular bounds enforced. -/
def tableCoefficient (data : CoefficientTable) (outer inner : ℕ) : ℤ :=
  if outer < data.outerLength ∧ inner < data.innerLength then
    rawCoefficient data outer inner
  else
    0

/-- The bivariate polynomial represented by a coefficient table.  The outer
polynomial variable is evaluated at the raw chart coordinate `r`; the inner
one is evaluated at `s`. -/
noncomputable def tablePolynomial (data : CoefficientTable) :
    Polynomial (Polynomial ℤ) :=
  Polynomial.ofFn data.outerLength fun outer =>
    Polynomial.ofFn data.innerLength fun inner =>
      tableCoefficient data outer inner

private theorem coeff_finset_sum
    {R : Type*} [Semiring R]
    (data : Finset ℕ) (value : ℕ → Polynomial R) (n : ℕ) :
    (∑ i ∈ data, value i).coeff n = ∑ i ∈ data, (value i).coeff n := by
  let coefficientHom : Polynomial R →+ R := {
    toFun := fun polynomial => polynomial.coeff n
    map_zero' := Polynomial.coeff_zero n
    map_add' := fun left right => Polynomial.coeff_add left right n
  }
  exact map_sum coefficientHom value data

/-- Coefficients of `tablePolynomial` are exactly the bounded table lookup. -/
theorem tablePolynomial_coeff_coeff
    (data : CoefficientTable) (outer inner : ℕ) :
    ((tablePolynomial data).coeff outer).coeff inner =
      tableCoefficient data outer inner := by
  unfold tablePolynomial
  by_cases ho : outer < data.outerLength
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ ho]
    by_cases hi : inner < data.innerLength
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
      simp [tableCoefficient, hi]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt ho)]
    simp [tableCoefficient, ho]

/-- A table polynomial as the corresponding explicit double monomial sum. -/
theorem tablePolynomial_eq_sum (data : CoefficientTable) :
    tablePolynomial data =
      ∑ outer ∈ Finset.range data.outerLength,
        Polynomial.monomial outer
          (∑ inner ∈ Finset.range data.innerLength,
            Polynomial.monomial inner
              (tableCoefficient data outer inner)) := by
  classical
  apply Polynomial.ext
  intro outer
  unfold tablePolynomial
  rw [coeff_finset_sum]
  by_cases ho : outer < data.outerLength
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ ho]
    simp only [Polynomial.coeff_monomial]
    simp only [Finset.sum_ite_eq', Finset.mem_range, ho, if_true]
    apply Polynomial.ext
    intro inner
    rw [coeff_finset_sum]
    by_cases hi : inner < data.innerLength
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
      simp only [Polynomial.coeff_monomial]
      simp [hi]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
      simp only [Polynomial.coeff_monomial]
      simp [hi]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt ho)]
    simp only [Polynomial.coeff_monomial]
    simp [ho]

/-- Arithmetic expressions whose atoms are bivariate coefficient tables. -/
inductive Expression where
  | atom : CoefficientTable → Expression
  | add : Expression → Expression → Expression
  | neg : Expression → Expression
  | scale : ℤ → Expression → Expression
  | mul : Expression → Expression → Expression

/-- A strict upper bound for the outer support of an expression. -/
def Expression.outerBound : Expression → ℕ
  | .atom data => data.outerLength
  | .add left right => max left.outerBound right.outerBound
  | .neg value => value.outerBound
  | .scale _ value => value.outerBound
  | .mul left right => left.outerBound + right.outerBound

/-- A strict upper bound for the inner support of an expression. -/
def Expression.innerBound : Expression → ℕ
  | .atom data => data.innerLength
  | .add left right => max left.innerBound right.innerBound
  | .neg value => value.innerBound
  | .scale _ value => value.innerBound
  | .mul left right => left.innerBound + right.innerBound

/-- Computable bivariate coefficient extraction for expression trees. -/
def expressionCoefficient : Expression → ℕ → ℕ → ℤ
  | .atom data, outer, inner => tableCoefficient data outer inner
  | .add left right, outer, inner =>
      expressionCoefficient left outer inner +
        expressionCoefficient right outer inner
  | .neg value, outer, inner => -expressionCoefficient value outer inner
  | .scale scalar value, outer, inner =>
      scalar * expressionCoefficient value outer inner
  | .mul left right, outer, inner =>
      ∑ leftOuter ∈ Finset.range (min (outer + 1) left.outerBound),
        ∑ leftInner ∈ Finset.range (min (inner + 1) left.innerBound),
          expressionCoefficient left leftOuter leftInner *
            expressionCoefficient right
              (outer - leftOuter) (inner - leftInner)

/-- Polynomial interpretation of a certificate expression. -/
noncomputable def expressionPolynomial : Expression →
    Polynomial (Polynomial ℤ)
  | .atom data => tablePolynomial data
  | .add left right => expressionPolynomial left + expressionPolynomial right
  | .neg value => -expressionPolynomial value
  | .scale scalar value => scalar • expressionPolynomial value
  | .mul left right => expressionPolynomial left * expressionPolynomial right

private theorem sum_range_min_eq_sum_range_of_eq_zero
    {M : Type*} [AddCommMonoid M] (value : ℕ → M) (n bound : ℕ)
    (hzero : ∀ i, bound ≤ i → value i = 0) :
    ∑ i ∈ Finset.range (min n bound), value i =
      ∑ i ∈ Finset.range n, value i := by
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hiNot
    apply hzero
    simp only [Finset.mem_range] at hi hiNot
    omega

private theorem expressionCoefficient_zero_of_outer_ge_aux
    (value : Expression) (outer inner : ℕ)
    (houter : value.outerBound ≤ outer) :
    expressionCoefficient value outer inner = 0 := by
  induction value generalizing outer inner with
  | atom data =>
      change data.outerLength ≤ outer at houter
      simp [expressionCoefficient, tableCoefficient,
        Nat.not_lt_of_ge houter]
  | add left right ihl ihr =>
      simp only [Expression.outerBound] at houter
      simp [expressionCoefficient,
        ihl outer inner (le_trans (le_max_left _ _) houter),
        ihr outer inner (le_trans (le_max_right _ _) houter)]
  | neg value ih => simp [expressionCoefficient, ih outer inner houter]
  | scale scalar value ih =>
      simp [expressionCoefficient, ih outer inner houter]
  | mul left right ihl ihr =>
      simp only [expressionCoefficient]
      apply Finset.sum_eq_zero
      intro leftOuter hleftOuter
      apply Finset.sum_eq_zero
      intro leftInner hleftInner
      by_cases hleft : left.outerBound ≤ leftOuter
      · rw [ihl leftOuter leftInner hleft]
        simp
      · have hright : right.outerBound ≤ outer - leftOuter := by
          simp only [Expression.outerBound] at houter
          omega
        rw [ihr (outer - leftOuter) (inner - leftInner) hright]
        simp

private theorem expressionCoefficient_zero_of_inner_ge_aux
    (value : Expression) (outer inner : ℕ)
    (hinner : value.innerBound ≤ inner) :
    expressionCoefficient value outer inner = 0 := by
  induction value generalizing outer inner with
  | atom data =>
      change data.innerLength ≤ inner at hinner
      simp [expressionCoefficient, tableCoefficient,
        Nat.not_lt_of_ge hinner]
  | add left right ihl ihr =>
      simp only [Expression.innerBound] at hinner
      simp [expressionCoefficient,
        ihl outer inner (le_trans (le_max_left _ _) hinner),
        ihr outer inner (le_trans (le_max_right _ _) hinner)]
  | neg value ih => simp [expressionCoefficient, ih outer inner hinner]
  | scale scalar value ih =>
      simp [expressionCoefficient, ih outer inner hinner]
  | mul left right ihl ihr =>
      simp only [expressionCoefficient]
      apply Finset.sum_eq_zero
      intro leftOuter hleftOuter
      apply Finset.sum_eq_zero
      intro leftInner hleftInner
      by_cases hleft : left.innerBound ≤ leftInner
      · rw [ihl leftOuter leftInner hleft]
        simp
      · have hright : right.innerBound ≤ inner - leftInner := by
          simp only [Expression.innerBound] at hinner
          omega
        rw [ihr (outer - leftOuter) (inner - leftInner) hright]
        simp

/-- The computable convolution agrees with coefficients of the polynomial
interpretation. -/
theorem expressionPolynomial_coeff_coeff
    (value : Expression) (outer inner : ℕ) :
    ((expressionPolynomial value).coeff outer).coeff inner =
      expressionCoefficient value outer inner := by
  induction value generalizing outer inner with
  | atom data => exact tablePolynomial_coeff_coeff data outer inner
  | add left right ihl ihr =>
      simp [expressionPolynomial, expressionCoefficient, ihl, ihr]
  | neg value ih =>
      simp [expressionPolynomial, expressionCoefficient, ih]
  | scale scalar value ih =>
      simp [expressionPolynomial, expressionCoefficient, ih]
  | mul left right ihl ihr =>
      rw [expressionPolynomial, Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        coeff_finset_sum]
      simp only [Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        expressionCoefficient]
      simp_rw [ihl, ihr]
      symm
      calc
        (∑ leftOuter ∈ Finset.range (min (outer + 1) left.outerBound),
            ∑ leftInner ∈ Finset.range (min (inner + 1) left.innerBound),
              expressionCoefficient left leftOuter leftInner *
                expressionCoefficient right
                  (outer - leftOuter) (inner - leftInner)) =
            ∑ leftOuter ∈ Finset.range (min (outer + 1) left.outerBound),
              ∑ leftInner ∈ Finset.range (inner + 1),
                expressionCoefficient left leftOuter leftInner *
                  expressionCoefficient right
                    (outer - leftOuter) (inner - leftInner) := by
          apply Finset.sum_congr rfl
          intro leftOuter hleftOuter
          apply sum_range_min_eq_sum_range_of_eq_zero
          intro leftInner hleftInner
          rw [expressionCoefficient_zero_of_inner_ge_aux
            left leftOuter leftInner hleftInner]
          simp
        _ =
            ∑ leftOuter ∈ Finset.range (outer + 1),
              ∑ leftInner ∈ Finset.range (inner + 1),
                expressionCoefficient left leftOuter leftInner *
                  expressionCoefficient right
                    (outer - leftOuter) (inner - leftInner) := by
          apply sum_range_min_eq_sum_range_of_eq_zero
          intro leftOuter hleftOuter
          apply Finset.sum_eq_zero
          intro leftInner hleftInner
          rw [expressionCoefficient_zero_of_outer_ge_aux
            left leftOuter leftInner hleftOuter]
          simp

/-- Coefficients outside the outer support bound vanish. -/
theorem expressionCoefficient_zero_of_outer_ge
    (value : Expression) (outer inner : ℕ)
    (houter : value.outerBound ≤ outer) :
    expressionCoefficient value outer inner = 0 :=
  expressionCoefficient_zero_of_outer_ge_aux value outer inner houter

/-- Coefficients outside the inner support bound vanish. -/
theorem expressionCoefficient_zero_of_inner_ge
    (value : Expression) (outer inner : ℕ)
    (hinner : value.innerBound ≤ inner) :
    expressionCoefficient value outer inner = 0 :=
  expressionCoefficient_zero_of_inner_ge_aux value outer inner hinner

/-- Evaluate a bivariate integer polynomial at rational chart coordinates. -/
noncomputable def evaluatePolynomial (r s : ℚ)
    (value : Polynomial (Polynomial ℤ)) : ℚ :=
  Polynomial.eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom ℚ) s) r value

/-- Direct evaluation of a coefficient table at rational chart coordinates. -/
def evaluateTableSum (data : CoefficientTable) (r s : ℚ) : ℚ :=
  ∑ outer ∈ Finset.range data.outerLength,
    ∑ inner ∈ Finset.range data.innerLength,
      (tableCoefficient data outer inner : ℚ) * s ^ inner * r ^ outer

/-- Polynomial and direct evaluations of a table agree. -/
theorem evaluatePolynomial_tablePolynomial
    (data : CoefficientTable) (r s : ℚ) :
    evaluatePolynomial r s (tablePolynomial data) =
      evaluateTableSum data r s := by
  rw [tablePolynomial_eq_sum]
  unfold evaluatePolynomial evaluateTableSum
  change (Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Int.castRingHom ℚ) s) r) _ = _
  rw [map_sum]
  simp_rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  simp_rw [map_sum]
  simp_rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro outer houter
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro inner hinner
  rw [Int.coe_castRingHom]

/-- Direct rational evaluation of an expression tree. -/
def evaluateExpression (value : Expression) (r s : ℚ) : ℚ :=
  match value with
  | .atom data => evaluateTableSum data r s
  | .add left right =>
      evaluateExpression left r s + evaluateExpression right r s
  | .neg value => -evaluateExpression value r s
  | .scale scalar value => scalar • evaluateExpression value r s
  | .mul left right =>
      evaluateExpression left r s * evaluateExpression right r s

/-- Polynomial and direct evaluations of an expression agree. -/
theorem evaluatePolynomial_expressionPolynomial
    (value : Expression) (r s : ℚ) :
    evaluatePolynomial r s (expressionPolynomial value) =
      evaluateExpression value r s := by
  induction value with
  | atom data => exact evaluatePolynomial_tablePolynomial data r s
  | add left right ihl ihr =>
      simpa [evaluatePolynomial, expressionPolynomial, evaluateExpression,
        Polynomial.eval₂_add] using congrArg₂ (· + ·) ihl ihr
  | neg value ih =>
      simpa [evaluatePolynomial, expressionPolynomial, evaluateExpression,
        Polynomial.eval₂_neg] using congrArg Neg.neg ih
  | scale scalar value ih =>
      simp only [expressionPolynomial, evaluateExpression]
      unfold evaluatePolynomial
      change (Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (Int.castRingHom ℚ) s) r)
          (scalar • expressionPolynomial value) = _
      unfold evaluatePolynomial at ih
      rw [map_zsmul]
      change scalar • Polynomial.eval₂
        (Polynomial.eval₂RingHom (Int.castRingHom ℚ) s) r
          (expressionPolynomial value) = _
      rw [ih]
  | mul left right ihl ihr =>
      simpa [evaluatePolynomial, expressionPolynomial, evaluateExpression,
        Polynomial.eval₂_mul] using congrArg₂ (· * ·) ihl ihr

end MazurTorsion.Kubert.OrderTwentyFiveDegeneracyCertificate
