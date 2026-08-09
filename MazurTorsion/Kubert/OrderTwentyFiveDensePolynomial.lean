/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

/-!
# A small checked dense-polynomial evaluator for order twenty five

The generated order-twenty-five certificates use coefficient lists in ascending
degree.  This leaf proves once that their elementary list multiplication is
preserved by evaluation.  Certificate leaves then ask Lean to check only small
integer-list multiplication steps.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial

def addWith (add : α → α → α) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => add x y :: addWith add xs ys

def scaleWith (mul : α → α → α) (a : α) : List α → List α
  | [] => []
  | x :: xs => mul a x :: scaleWith mul a xs

def mulWith (zero : α) (add mul : α → α → α) : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | x :: xs, ys =>
      addWith add (scaleWith mul x ys) (zero :: mulWith zero add mul xs ys)

def evalWith (f : α → ℚ) (x : ℚ) : List α → ℚ
  | [] => 0
  | a :: as => f a + x * evalWith f x as

theorem evalWith_addWith (add : α → α → α) (f : α → ℚ)
    (hadd : ∀ a b, f (add a b) = f a + f b) (x : ℚ) (as bs : List α) :
    evalWith f x (addWith add as bs) = evalWith f x as + evalWith f x bs := by
  induction as generalizing bs with
  | nil => simp [addWith, evalWith]
  | cons a as ih =>
      cases bs with
      | nil => simp [addWith, evalWith]
      | cons b bs =>
          simp only [addWith, evalWith, hadd, ih]
          ring

theorem evalWith_scaleWith (mul : α → α → α) (f : α → ℚ)
    (hmul : ∀ a b, f (mul a b) = f a * f b) (x : ℚ) (a : α) (as : List α) :
    evalWith f x (scaleWith mul a as) = f a * evalWith f x as := by
  induction as with
  | nil => simp [scaleWith, evalWith]
  | cons b bs ih =>
      simp only [scaleWith, evalWith, hmul, ih]
      ring

theorem evalWith_mulWith (zero : α) (add mul : α → α → α) (f : α → ℚ)
    (hzero : f zero = 0) (hadd : ∀ a b, f (add a b) = f a + f b)
    (hmul : ∀ a b, f (mul a b) = f a * f b) (x : ℚ) (as bs : List α) :
    evalWith f x (mulWith zero add mul as bs) = evalWith f x as * evalWith f x bs := by
  induction as with
  | nil => simp [mulWith, evalWith]
  | cons a as ih =>
      cases bs with
      | nil => simp [mulWith, evalWith]
      | cons b bs =>
          simp only [mulWith]
          rw [evalWith_addWith add f hadd,
            evalWith_scaleWith mul f hmul]
          simp only [evalWith, hzero, zero_add, ih]
          ring

abbrev One := List ℤ

namespace One

def add : One → One → One := addWith (· + ·)

def mul : One → One → One := mulWith 0 (· + ·) (· * ·)

def eval (p : One) (s : ℚ) : ℚ := evalWith (fun z : ℤ => (z : ℚ)) s p

theorem eval_add (p q : One) (s : ℚ) :
    eval (add p q) s = eval p s + eval q s := by
  apply evalWith_addWith
  simp

theorem eval_mul (p q : One) (s : ℚ) :
    eval (mul p q) s = eval p s * eval q s := by
  apply evalWith_mulWith
  · simp
  · simp
  · simp

end One

abbrev Two := List One

namespace Two

def add : Two → Two → Two := addWith One.add

def mul : Two → Two → Two := mulWith [] One.add One.mul

def eval (p : Two) (r s : ℚ) : ℚ := evalWith (fun q => One.eval q s) r p

theorem eval_add (p q : Two) (r s : ℚ) :
    eval (add p q) r s = eval p r s + eval q r s := by
  apply evalWith_addWith
  exact fun a b => One.eval_add a b s

theorem eval_mul (p q : Two) (r s : ℚ) :
    eval (mul p q) r s = eval p r s * eval q r s := by
  apply evalWith_mulWith
  · rfl
  · exact fun a b => One.eval_add a b s
  · exact fun a b => One.eval_mul a b s

end Two

end MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial
