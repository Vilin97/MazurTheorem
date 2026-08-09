/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial
import Mathlib.Tactic.NormNum

/-!
# Rectangular representatives for dense order-twenty-five certificates

Appending zero coefficients does not change evaluation.  Generated tables can
therefore be compared after padding, while the comparison still retains every
coefficient already present in either operand.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRectangular

open OrderTwentyFiveDensePolynomial

def padOne (inner : ℕ) (p : One) : One :=
  p ++ List.replicate (inner - p.length) 0

def rectangularize (outer inner : ℕ) (p : Two) : Two :=
  p.map (padOne inner) ++
    List.replicate (outer - p.length) (List.replicate inner 0)

theorem getD_padOne (inner : ℕ) (p : One) (n : ℕ) (hn : n < inner) :
    (padOne inner p).getD n 0 = p.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, padOne, List.getElem?_append]
  by_cases hp : n < p.length
  · simp [hp, List.getD_eq_getElem?_getD]
  · have hle : p.length ≤ n := by omega
    have hidx : n - p.length < inner - p.length := by omega
    simp [hp, hidx, List.getD_eq_getElem?_getD]

theorem getD_rectangularize (outer inner : ℕ) (p : Two) (n : ℕ)
    (hn : n < outer) :
    (rectangularize outer inner p).getD n [] =
      padOne inner (p.getD n []) := by
  rw [List.getD_eq_getElem?_getD, rectangularize,
    List.getElem?_append]
  by_cases hp : n < p.length
  · simp [hp, List.getD_eq_getElem?_getD]
  · have hle : p.length ≤ n := by omega
    have hidx : n - p.length < outer - p.length := by omega
    simp [hp, hidx, List.getD_eq_getElem?_getD, padOne]

private theorem evalWith_replicate_zero (f : α → ℚ) (z : α)
    (hz : f z = 0) (x : ℚ) : ∀ n,
    evalWith f x (List.replicate n z) = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change f z + x * evalWith f x (List.replicate n z) = 0
      rw [hz, ih, mul_zero, add_zero]

private theorem evalWith_append_replicate_zero (f : α → ℚ) (z : α)
    (hz : f z = 0) (x : ℚ) (n : ℕ) : ∀ p,
    evalWith f x (p ++ List.replicate n z) = evalWith f x p := by
  intro p
  induction p with
  | nil => exact evalWith_replicate_zero f z hz x n
  | cons a p ih => simp only [List.cons_append, evalWith, ih]

theorem eval_padOne (inner : ℕ) (p : One) (s : ℚ) :
    One.eval (padOne inner p) s = One.eval p s := by
  exact evalWith_append_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s (inner - p.length) p

private theorem eval_map_padOne (inner : ℕ) (p : Two) (r s : ℚ) :
    evalWith (fun q => One.eval q s) r (p.map (padOne inner)) =
      evalWith (fun q => One.eval q s) r p := by
  induction p with
  | nil => rfl
  | cons q p ih => simp only [List.map_cons, evalWith, eval_padOne, ih]

private theorem eval_zeroRow (inner : ℕ) (s : ℚ) :
    One.eval (List.replicate inner 0) s = 0 := by
  exact evalWith_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s inner

theorem eval_rectangularize (outer inner : ℕ) (p : Two) (r s : ℚ) :
    Two.eval (rectangularize outer inner p) r s = Two.eval p r s := by
  simp only [rectangularize, Two.eval]
  rw [evalWith_append_replicate_zero
    (fun q => One.eval q s) (List.replicate inner 0)
    (eval_zeroRow inner s) r]
  exact eval_map_padOne inner p r s

end MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRectangular
