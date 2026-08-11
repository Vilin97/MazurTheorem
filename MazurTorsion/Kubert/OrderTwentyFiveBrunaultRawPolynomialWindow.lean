/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate

/-!
# Window lemmas for the raw order-twenty-five polynomial certificate

These structural lemmas let large dense certificates check a bounded
convolution window without changing the polynomial product being certified.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

theorem getD_drop_window (xs : List α) (d n : ℕ) (z : α) :
    (xs.drop d).getD n z = xs.getD (d + n) z := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- A scalar coefficient exposed through lazy outer and inner list windows. -/
def windowCoeff (p : Two) (i j : ℕ) : ℤ :=
  (((p.drop i).getD 0 []).drop j).getD 0 0

theorem windowCoeff_eq_getD (p : Two) (i j : ℕ) :
    windowCoeff p i j = (p.getD i []).getD j 0 := by
  simp only [windowCoeff, getD_drop_window, Nat.add_zero]

private theorem oneAdd_nil (p : One) : One.add p [] = p := by
  cases p <;> rfl

private theorem oneMul_nil (p : One) : One.mul p [] = [] := by
  cases p <;> rfl

private theorem mulRow_nil_right : ∀ (p : Two) (n : ℕ),
    mulRow p [] n = []
  | [], _n => rfl
  | _a :: _as, _n => rfl

private theorem mulRow_cons_zero (a : One) (as q : Two) :
    mulRow (a :: as) q 0 = One.mul a (q.getD 0 []) := by
  cases q with
  | nil => simp [mulRow, oneMul_nil]
  | cons b q => rfl

private theorem mulRow_cons_succ (a : One) (as q : Two) (n : ℕ) :
    mulRow (a :: as) q (n + 1) =
      One.add (One.mul a (q.getD (n + 1) [])) (mulRow as q n) := by
  cases q with
  | nil => simp [mulRow, oneMul_nil, mulRow_nil_right, oneAdd_nil]
  | cons b q => rfl

private theorem mulRow_singleton (a : One) (q : Two) (n : ℕ) :
    mulRow [a] q n = One.mul a (q.getD n []) := by
  cases n with
  | zero => exact mulRow_cons_zero a [] q
  | succ n =>
      rw [mulRow_cons_succ]
      simp only [mulRow, oneAdd_nil]

theorem mulRow_drop_window : ∀ (p q : Two) (d k : ℕ),
    p.length ≤ k + 1 →
      mulRow p q (d + k) = mulRow p (q.drop d) k
  | [], _q, _d, _k, _h => by simp [mulRow]
  | a :: as, q, d, 0, h => by
      have hasLength : as.length = 0 := by
        simp only [List.length_cons] at h
        omega
      have has : as = [] := List.eq_nil_of_length_eq_zero hasLength
      subst as
      rw [Nat.add_zero, mulRow_singleton, mulRow_singleton,
        getD_drop_window, Nat.add_zero]
  | a :: as, q, d, k + 1, h => by
      rw [Nat.add_succ, mulRow_cons_succ, mulRow_cons_succ,
        getD_drop_window, Nat.add_succ]
      congr 1
      apply mulRow_drop_window as q d k
      simp only [List.length_cons] at h
      omega

private theorem mulCoeff_nil_right : ∀ (p : One) (n : ℕ),
    mulCoeff p [] n = 0
  | [], _n => rfl
  | _a :: _as, _n => rfl

private theorem mulCoeff_cons_succ (a : ℤ) (as q : One) (n : ℕ) :
    mulCoeff (a :: as) q (n + 1) =
      a * q.getD (n + 1) 0 + mulCoeff as q n := by
  cases q with
  | nil => simp [mulCoeff, mulCoeff_nil_right]
  | cons _b _q => rfl

private theorem mulCoeff_singleton (a : ℤ) (q : One) (n : ℕ) :
    mulCoeff [a] q n = a * q.getD n 0 := by
  cases q <;> cases n <;> simp [mulCoeff]

/-- A bounded inner convolution window for one dense coefficient row. -/
theorem mulCoeff_drop_window : ∀ (p q : One) (d k : ℕ),
    p.length ≤ k + 1 →
      mulCoeff p q (d + k) = mulCoeff p (q.drop d) k
  | [], _q, _d, _k, _h => by simp [mulCoeff]
  | a :: as, q, d, 0, h => by
      have hasLength : as.length = 0 := by
        simp only [List.length_cons] at h
        omega
      have has : as = [] := List.eq_nil_of_length_eq_zero hasLength
      subst as
      rw [Nat.add_zero, mulCoeff_singleton, mulCoeff_singleton,
        getD_drop_window, Nat.add_zero]
  | a :: as, q, d, k + 1, h => by
      rw [Nat.add_succ, mulCoeff_cons_succ, mulCoeff_cons_succ,
        getD_drop_window, Nat.add_succ]
      congr 1
      apply mulCoeff_drop_window as q d k
      simp only [List.length_cons] at h
      omega

/-- Drop a fixed inner prefix from every row of a dense bivariate table. -/
def dropInner (d : ℕ) (q : Two) : Two :=
  q.map (fun row => row.drop d)

theorem getD_dropInner (q : Two) (d n : ℕ) :
    (dropInner d q).getD n [] = (q.getD n []).drop d := by
  induction q generalizing n with
  | nil => simp [dropInner]
  | cons row q ih =>
      cases n with
      | zero => rfl
      | succ n => simpa [dropInner] using ih n

/-- Lift the bounded inner window through every outer convolution row. -/
theorem mulCoeffTwo_dropInner_window (p q : Two) (n d k : ℕ)
    (h : ∀ row ∈ p, row.length ≤ k + 1) :
    mulCoeffTwo p q n (d + k) =
      mulCoeffTwo p (dropInner d q) n k := by
  induction p generalizing q n with
  | nil => simp [mulCoeffTwo]
  | cons a p ih =>
      have ha : a.length ≤ k + 1 := h a (by simp)
      have hp : ∀ row ∈ p, row.length ≤ k + 1 := by
        intro row hr
        exact h row (by simp [hr])
      cases q with
      | nil => simp [mulCoeffTwo, dropInner]
      | cons b q =>
          cases n with
          | zero =>
              change mulCoeff a b (d + k) = mulCoeff a (b.drop d) k
              exact mulCoeff_drop_window a b d k ha
          | succ n =>
              change
                mulCoeff a ((b :: q).getD (n + 1) []) (d + k) +
                    mulCoeffTwo p (b :: q) n (d + k) =
                  mulCoeff a ((dropInner d (b :: q)).getD (n + 1) []) k +
                    mulCoeffTwo p (dropInner d (b :: q)) n k
              rw [getD_dropInner,
                mulCoeff_drop_window a ((b :: q).getD (n + 1) []) d k ha,
                ih (q := b :: q) (n := n) hp]

/-- Expose a bounded outer convolution window at a fixed inner coefficient. -/
theorem mulCoeffTwo_outerDrop_window (p q : Two)
    (d k j : ℕ) (h : p.length ≤ k + 1) :
    mulCoeffTwo p q (d + k) j = mulCoeffTwo p (q.drop d) k j := by
  rw [mulCoeffTwo_eq_getD, mulRow_drop_window p q d k h,
    ← mulCoeffTwo_eq_getD]

/-- Simultaneously expose bounded outer and inner convolution windows. -/
theorem mulCoeffTwo_window (p q : Two)
    (outerOffset outerIndex innerOffset innerIndex : ℕ)
    (hOuter : p.length ≤ outerIndex + 1)
    (hInner : ∀ row ∈ p, row.length ≤ innerIndex + 1) :
    mulCoeffTwo p q (outerOffset + outerIndex) (innerOffset + innerIndex) =
      mulCoeffTwo p (dropInner innerOffset (q.drop outerOffset))
        outerIndex innerIndex := by
  rw [mulCoeffTwo_outerDrop_window p q outerOffset outerIndex
      (innerOffset + innerIndex) hOuter,
    mulCoeffTwo_dropInner_window p (q.drop outerOffset)
      outerIndex innerOffset innerIndex hInner]

private theorem length_addWith (add : α → α → α) : ∀ xs ys,
    (addWith add xs ys).length = max xs.length ys.length
  | [], ys => by simp [addWith]
  | _x :: xs, [] => rfl
  | _x :: xs, _y :: ys => by
      simp only [addWith, List.length_cons, length_addWith add xs ys,
        Nat.succ_max_succ]

private theorem length_scaleWith (mul : α → α → α) (a : α) : ∀ xs,
    (scaleWith mul a xs).length = xs.length
  | [] => rfl
  | _x :: xs => by simp [scaleWith, length_scaleWith mul a xs]

theorem length_mulWith_of_ne_nil (zero : α)
    (add mul : α → α → α) : ∀ xs ys,
    xs ≠ [] → ys ≠ [] →
      (mulWith zero add mul xs ys).length = xs.length + ys.length - 1
  | [], _ys, hxs, _hys => (hxs rfl).elim
  | _xs, [], _hxs, hys => (hys rfl).elim
  | x :: [], y :: ys, _hxs, _hys => by
      simp only [mulWith, length_addWith, length_scaleWith, List.length_cons,
        List.length_nil]
      omega
  | x :: x' :: xs, y :: ys, _hxs, _hys => by
      rw [mulWith, length_addWith, length_scaleWith] <;> try exact _hys
      simp only [List.length_cons]
      rw [length_mulWith_of_ne_nil zero add mul (x' :: xs) (y :: ys)
        (List.cons_ne_nil x' xs) _hys]
      simp only [List.length_cons]
      rw [Nat.max_eq_right (by omega)]
      omega

theorem rectangularize_length_of_le (outer inner : ℕ) (p : Two)
    (h : p.length ≤ outer) :
    (rectangularize outer inner p).length = outer := by
  simp only [rectangularize, List.length_append, List.length_map,
    List.length_replicate]
  omega

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
