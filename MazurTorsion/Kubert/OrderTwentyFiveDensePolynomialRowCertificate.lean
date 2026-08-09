/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRectangular

/-!
# Row-local checking for dense order-twenty-five polynomial products

`mulRow` computes one complete outer coefficient of a bivariate product.  The
structural theorem below identifies it with the corresponding row of the
kernel-checked dense multiplication.  Large generated certificates can thus
check one full padded row at a time without repeatedly reducing all preceding
rows of the product.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular

def mulRow : Two → Two → ℕ → One
  | [], _, _ => []
  | _, [], _ => []
  | a :: _as, q, 0 => One.mul a (q.getD 0 [])
  | a :: as, q, n + 1 =>
      One.add (One.mul a (q.getD (n + 1) [])) (mulRow as q n)

private theorem oneAdd_nil (p : One) : One.add p [] = p := by
  cases p <;> rfl

private theorem oneMul_nil (p : One) : One.mul p [] = [] := by
  cases p <;> rfl

private theorem getD_scaleWith (a : One) : ∀ q n,
    (scaleWith One.mul a q).getD n [] = One.mul a (q.getD n []) := by
  intro q
  induction q with
  | nil =>
      intro n
      simp [scaleWith, oneMul_nil]
  | cons b q ih =>
      intro n
      cases n with
      | zero => rfl
      | succ n => simpa [scaleWith] using ih n

private theorem getD_addWith : ∀ p q n,
    (addWith One.add p q).getD n [] =
      One.add (p.getD n []) (q.getD n []) := by
  intro p
  induction p with
  | nil =>
      intro q n
      simp [addWith, One.add]
  | cons a p ih =>
      intro q n
      cases q with
      | nil => simp [addWith, oneAdd_nil]
      | cons b q =>
          cases n with
          | zero => rfl
          | succ n => simpa [addWith] using ih q n

theorem mulRow_eq_getD : ∀ p q n,
    mulRow p q n = (Two.mul p q).getD n [] := by
  intro p
  induction p with
  | nil =>
      intro q n
      simp [mulRow, Two.mul, mulWith]
  | cons a p ih =>
      intro q n
      cases q with
      | nil => simp [mulRow, Two.mul, mulWith]
      | cons b q =>
          cases n with
          | zero =>
              change One.mul a b =
                (addWith One.add (scaleWith One.mul a (b :: q))
                  ([] :: Two.mul p (b :: q))).getD 0 []
              rw [getD_addWith, getD_scaleWith]
              simp [oneAdd_nil]
          | succ n =>
              change
                One.add (One.mul a ((b :: q).getD (n + 1) []))
                    (mulRow p (b :: q) n) =
                  (addWith One.add (scaleWith One.mul a (b :: q))
                    ([] :: Two.mul p (b :: q))).getD (n + 1) []
              rw [getD_addWith, getD_scaleWith]
              simp only [List.getD_cons_succ]
              rw [ih (b :: q) n]

def mulCoeff : One → One → ℕ → ℤ
  | [], _, _ => 0
  | _, [], _ => 0
  | a :: _as, q, 0 => a * q.getD 0 0
  | a :: as, q, n + 1 =>
      a * q.getD (n + 1) 0 + mulCoeff as q n

private theorem getD_scaleWithInt (a : ℤ) : ∀ q n,
    (scaleWith (· * ·) a q).getD n 0 = a * q.getD n 0 := by
  intro q
  induction q with
  | nil => simp [scaleWith]
  | cons b q ih =>
      intro n
      cases n with
      | zero => rfl
      | succ n => simpa [scaleWith] using ih n

private theorem getD_addWithInt : ∀ (p q : One) (n : ℕ),
    (addWith (· + ·) p q).getD n 0 = p.getD n 0 + q.getD n 0 := by
  intro p
  induction p with
  | nil =>
      intro q n
      simp [addWith]
  | cons a p ih =>
      intro q n
      cases q with
      | nil => simp [addWith]
      | cons b q =>
          cases n with
          | zero => rfl
          | succ n => simpa [addWith] using ih q n

theorem mulCoeff_eq_getD : ∀ p q n,
    mulCoeff p q n = (One.mul p q).getD n 0 := by
  intro p
  induction p with
  | nil =>
      intro q n
      simp [mulCoeff, One.mul, mulWith]
  | cons a p ih =>
      intro q n
      cases q with
      | nil =>
          rw [oneMul_nil]
          simp [mulCoeff]
      | cons b q =>
          cases n with
          | zero =>
              change a * b =
                (addWith (· + ·) (scaleWith (· * ·) a (b :: q))
                  (0 :: One.mul p (b :: q))).getD 0 0
              rw [getD_addWithInt
                (scaleWith (· * ·) a (b :: q))
                (0 :: One.mul p (b :: q)) 0,
                getD_scaleWithInt a (b :: q) 0]
              simp
          | succ n =>
              change
                a * (b :: q).getD (n + 1) 0 + mulCoeff p (b :: q) n =
                  (addWith (· + ·) (scaleWith (· * ·) a (b :: q))
                    (0 :: One.mul p (b :: q))).getD (n + 1) 0
              rw [getD_addWithInt
                (scaleWith (· * ·) a (b :: q))
                (0 :: One.mul p (b :: q)) (n + 1),
                getD_scaleWithInt a (b :: q) (n + 1)]
              simp only [List.getD_cons_succ]
              rw [ih (b :: q) n]

def mulCoeffTwo : Two → Two → ℕ → ℕ → ℤ
  | [], _, _, _ => 0
  | _, [], _, _ => 0
  | a :: _as, q, 0, j => mulCoeff a (q.getD 0 []) j
  | a :: as, q, n + 1, j =>
      mulCoeff a (q.getD (n + 1) []) j + mulCoeffTwo as q n j

theorem mulCoeffTwo_eq_getD : ∀ p q n j,
    mulCoeffTwo p q n j = (mulRow p q n).getD j 0 := by
  intro p
  induction p with
  | nil =>
      intro q n j
      simp [mulCoeffTwo, mulRow]
  | cons a p ih =>
      intro q n j
      cases q with
      | nil => simp [mulCoeffTwo, mulRow]
      | cons b q =>
          cases n with
          | zero =>
              simp only [mulCoeffTwo, mulRow]
              exact mulCoeff_eq_getD a b j
          | succ n =>
              simp only [mulCoeffTwo, mulRow]
              change
                mulCoeff a ((b :: q).getD (n + 1) []) j +
                    mulCoeffTwo p (b :: q) n j =
                  (addWith (· + ·)
                    (One.mul a ((b :: q).getD (n + 1) []))
                    (mulRow p (b :: q) n)).getD j 0
              rw [getD_addWithInt
                (One.mul a ((b :: q).getD (n + 1) []))
                (mulRow p (b :: q) n) j,
                ← mulCoeff_eq_getD, ← ih (b :: q) n j]

def addMulRow (p q t : Two) (n : ℕ) : One :=
  One.add (p.getD n []) (mulRow q t n)

theorem addMulRow_eq_getD (p q t : Two) (n : ℕ) :
    addMulRow p q t n = (Two.add p (Two.mul q t)).getD n [] := by
  rw [addMulRow, mulRow_eq_getD]
  exact (getD_addWith p (Two.mul q t) n).symm

def addMulCoeffTwo (p q t : Two) (n j : ℕ) : ℤ :=
  (p.getD n []).getD j 0 + mulCoeffTwo q t n j

theorem addMulCoeffTwo_eq_getD (p q t : Two) (n j : ℕ) :
    addMulCoeffTwo p q t n j = (addMulRow p q t n).getD j 0 := by
  rw [addMulCoeffTwo, addMulRow]
  change (p.getD n []).getD j 0 + mulCoeffTwo q t n j =
    (addWith (· + ·) (p.getD n []) (mulRow q t n)).getD j 0
  rw [getD_addWithInt, mulCoeffTwo_eq_getD]

def coefficientRow (inner : ℕ) (p q : Two) (n : ℕ) : One :=
  (List.range inner).map (mulCoeffTwo p q n)

private theorem getD_coefficientRow (inner : ℕ) (p q : Two) (n j : ℕ)
    (hj : j < inner) :
    (coefficientRow inner p q n).getD j 0 = mulCoeffTwo p q n j := by
  simp [coefficientRow, List.getD_eq_getElem?_getD, hj]

theorem coefficientRow_eq_padOne (inner : ℕ) (p q : Two) (n : ℕ)
    (hSupport : (mulRow p q n).length ≤ inner) :
    coefficientRow inner p q n = padOne inner (mulRow p q n) := by
  apply List.ext_getElem
  · simp [coefficientRow, padOne]
    omega
  · intro j hjLeft hjRight
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0,
      getD_coefficientRow inner p q n j,
      getD_padOne inner (mulRow p q n) j]
    · exact mulCoeffTwo_eq_getD p q n j
    · simpa [coefficientRow] using hjLeft
    · simpa [coefficientRow] using hjLeft

theorem padOne_mulRow_eq_of_coefficients (inner : ℕ) (p q : Two)
    (n : ℕ) (target : One)
    (hSupport : (mulRow p q n).length ≤ inner)
    (hTarget : target.length = inner)
    (hCoeff : ∀ j, j < inner →
      mulCoeffTwo p q n j = target.getD j 0) :
    padOne inner (mulRow p q n) = target := by
  have hPad : (padOne inner (mulRow p q n)).length = inner := by
    simp [padOne]
    omega
  apply List.ext_getElem (hPad.trans hTarget.symm)
  intro j hjLeft _
  have hj : j < inner := by simpa [hPad] using hjLeft
  rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0,
    getD_padOne inner (mulRow p q n) j hj,
    ← mulCoeffTwo_eq_getD]
  exact hCoeff j hj

theorem padOne_eq_of_coefficients (inner : ℕ) (p target : One)
    (hSupport : p.length ≤ inner)
    (hTarget : target.length = inner)
    (hCoeff : ∀ j, j < inner → p.getD j 0 = target.getD j 0) :
    padOne inner p = target := by
  have hPad : (padOne inner p).length = inner := by
    simp [padOne]
    omega
  apply List.ext_getElem (hPad.trans hTarget.symm)
  intro j hjLeft _
  have hj : j < inner := by simpa [hPad] using hjLeft
  rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0,
    getD_padOne inner p j hj]
  exact hCoeff j hj

theorem padOne_addMulRow_eq_of_coefficients (inner : ℕ) (p q t : Two)
    (n : ℕ) (target : One)
    (hSupport : (addMulRow p q t n).length ≤ inner)
    (hTarget : target.length = inner)
    (hCoeff : ∀ j, j < inner →
      addMulCoeffTwo p q t n j = target.getD j 0) :
    padOne inner (addMulRow p q t n) = target := by
  apply padOne_eq_of_coefficients inner (addMulRow p q t n) target
    hSupport hTarget
  intro j hj
  rw [← addMulCoeffTwo_eq_getD]
  exact hCoeff j hj

end MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate
