/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial
import Mathlib.Data.List.GetD
import Lean.Elab.Tactic.Omega

/-!
# Structural support bounds for dense order-twenty-five certificates

Large generated coefficient tables should not have to normalize their integer
coefficients merely to prove a degree bound.  This leaf records support bounds
for the elementary dense-list operations.  Downstream certificate modules can
therefore establish row widths from the widths of their input tables, while
the actual coefficients remain checked separately by the Lean kernel.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialSupport

open OrderTwentyFiveDensePolynomial

/-- Every coefficient row of a bivariate dense table has length at most
`inner`. -/
def HasInnerSupport (inner : ℕ) (p : Two) : Prop :=
  ∀ row ∈ p, row.length ≤ inner

/-- A computable check for the row-width predicate.  It inspects only list
spines and row lengths; coefficient values are never normalized. -/
def hasInnerSupportCheck (inner : ℕ) (p : Two) : Bool :=
  p.all fun row => decide (row.length ≤ inner)

/-- A successful structural check proves the corresponding support
predicate.  This is the small kernel-checked entry point for literal input
tables. -/
theorem hasInnerSupport_of_check {inner : ℕ} {p : Two}
    (h : hasInnerSupportCheck inner p = true) :
    HasInnerSupport inner p := by
  intro row hrow
  have hall : ∀ q ∈ p, decide (q.length ≤ inner) = true := by
    simpa only [hasInnerSupportCheck, List.all_eq_true] using h
  exact of_decide_eq_true (hall row hrow)

private theorem length_addWith (add : α → α → α) : ∀ p q : List α,
    (addWith add p q).length = max p.length q.length := by
  intro p
  induction p with
  | nil => simp [addWith]
  | cons a p ih =>
      intro q
      cases q with
      | nil => simp [addWith]
      | cons b q =>
          simp only [addWith, List.length_cons, ih]
          omega

private theorem length_scaleWith (mul : α → α → α) (a : α) :
    ∀ p : List α, (scaleWith mul a p).length = p.length := by
  intro p
  induction p with
  | nil => rfl
  | cons b p ih => simp [scaleWith, ih]

private theorem length_mulWith_of_nonempty
    (zero : α) (add mul : α → α → α) : ∀ p q : List α,
    p ≠ [] → q ≠ [] →
      (mulWith zero add mul p q).length = p.length + q.length - 1 := by
  intro p
  induction p with
  | nil => simp
  | cons a p ih =>
      intro q _ hq
      cases q with
      | nil => simp at hq
      | cons b q =>
          cases p with
          | nil =>
              simp [mulWith, length_addWith, length_scaleWith]
          | cons c p =>
              have h := ih (b :: q) (by simp) (by simp)
              rw [show
                mulWith zero add mul (a :: c :: p) (b :: q) =
                  addWith add (scaleWith mul a (b :: q))
                    (zero :: mulWith zero add mul (c :: p) (b :: q))
                from rfl]
              rw [length_addWith, length_scaleWith]
              simp only [List.length_cons]
              rw [h]
              simp only [List.length_cons]
              omega

private theorem length_mulWith_le (zero : α) (add mul : α → α → α)
    (p q : List α) :
    (mulWith zero add mul p q).length ≤ p.length + q.length - 1 := by
  cases p with
  | nil => simp [mulWith]
  | cons a p =>
      cases q with
      | nil => simp [mulWith]
      | cons b q =>
          exact (length_mulWith_of_nonempty zero add mul
            (a :: p) (b :: q) (by simp) (by simp)).le

private theorem one_add_length_le {p q : One} {inner : ℕ}
    (hp : p.length ≤ inner) (hq : q.length ≤ inner) :
    (One.add p q).length ≤ inner := by
  simp only [One.add, length_addWith]
  omega

private theorem one_mul_length_le {p q : One} {left right : ℕ}
    (hp : p.length ≤ left) (hq : q.length ≤ right) :
    (One.mul p q).length ≤ left + right - 1 := by
  refine (length_mulWith_le 0 (· + ·) (· * ·) p q).trans ?_
  omega

private theorem hasInnerSupport_addWith (inner : ℕ) : ∀ p q : Two,
    HasInnerSupport inner p →
      HasInnerSupport inner q →
        HasInnerSupport inner (addWith One.add p q) := by
  intro p
  induction p with
  | nil =>
      intro q _ hq
      simpa [addWith] using hq
  | cons a p ih =>
      intro q hp hq
      cases q with
      | nil => simpa [addWith] using hp
      | cons b q =>
          intro row hrow
          simp only [addWith, List.mem_cons] at hrow
          rcases hrow with rfl | hrow
          · apply one_add_length_le
            · exact hp a (by simp)
            · exact hq b (by simp)
          · apply ih q
              (fun x hx => hp x (by simp [hx]))
              (fun x hx => hq x (by simp [hx]))
              row hrow

private theorem hasInnerSupport_scaleWith
    (left right : ℕ) (a : One) (q : Two)
    (ha : a.length ≤ left) (hq : HasInnerSupport right q) :
    HasInnerSupport (left + right - 1) (scaleWith One.mul a q) := by
  intro row hrow
  induction q with
  | nil => simp [scaleWith] at hrow
  | cons b q ih =>
      simp only [scaleWith, List.mem_cons] at hrow
      rcases hrow with rfl | hrow
      · exact one_mul_length_le ha (hq b (by simp))
      · exact ih (fun x hx => hq x (by simp [hx])) hrow

/-- Dense addition preserves a common inner support bound. -/
theorem hasInnerSupport_add (inner : ℕ) (p q : Two)
    (hp : HasInnerSupport inner p) (hq : HasInnerSupport inner q) :
    HasInnerSupport inner (Two.add p q) := by
  exact hasInnerSupport_addWith inner p q hp hq

/-- Dense multiplication adds inner degrees: multiplying tables of widths
`left` and `right` has width at most `left + right - 1`. -/
theorem hasInnerSupport_mul (left right : ℕ) : ∀ p q : Two,
    HasInnerSupport left p →
      HasInnerSupport right q →
        HasInnerSupport (left + right - 1) (Two.mul p q) := by
  intro p
  induction p with
  | nil =>
      intro q _ _
      simp [Two.mul, mulWith, HasInnerSupport]
  | cons a p ih =>
      intro q hp hq
      cases q with
      | nil => simp [Two.mul, mulWith, HasInnerSupport]
      | cons b q =>
          simp only [Two.mul, mulWith]
          apply hasInnerSupport_addWith
          · exact hasInnerSupport_scaleWith left right a (b :: q)
              (hp a (by simp)) hq
          · intro row hrow
            simp only [List.mem_cons] at hrow
            rcases hrow with rfl | hrow
            · simp
            · exact ih (b :: q)
                (fun x hx => hp x (by simp [hx])) hq row hrow

/-- A row selected with `getD` inherits a global inner support bound. -/
theorem getD_length_le {inner : ℕ} {p : Two}
    (hp : HasInnerSupport inner p) (i : ℕ) :
    (p.getD i []).length ≤ inner := by
  by_cases hi : i < p.length
  · exact hp (p.getD i []) (by
      rw [List.getD_eq_getElem?_getD]
      simp [hi])
  · have hget : p.getD i [] = [] :=
      List.getD_eq_default p [] (by omega)
    rw [hget]
    simp

end MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialSupport
