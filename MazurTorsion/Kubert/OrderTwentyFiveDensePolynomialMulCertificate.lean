/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate

/-!
# Assembling dense multiplication certificates from checked rows

Generated certificates can check a large dense product one row or coefficient
window at a time.  This leaf assembles the resulting row equalities into a
rectangular polynomial equality and its evaluation consequence, without
recomputing the product table.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem rectangularize_length (outer inner : ℕ) (p : Two)
    (h : p.length ≤ outer) :
    (rectangularize outer inner p).length = outer := by
  simp only [rectangularize, List.length_append, List.length_map,
    List.length_replicate]
  omega

/-- Assemble checked padded product rows into an equality of rectangular dense
polynomial representatives. -/
theorem rectangularize_mul_eq_of_rows
    (outer inner : ℕ) (p q mulData : Two)
    (hMulOuter : (Two.mul p q).length ≤ outer)
    (hDataOuter : mulData.length ≤ outer)
    (hRows : ∀ n, n < outer →
      padOne inner (mulRow p q n) =
        (rectangularize outer inner mulData).getD n []) :
    rectangularize outer inner (Two.mul p q) =
      rectangularize outer inner mulData := by
  have hLeft :
      (rectangularize outer inner (Two.mul p q)).length = outer :=
    rectangularize_length outer inner (Two.mul p q) hMulOuter
  have hRight :
      (rectangularize outer inner mulData).length = outer :=
    rectangularize_length outer inner mulData hDataOuter
  apply List.ext_getElem (hLeft.trans hRight.symm)
  intro n hn _
  rw [List.getElem_eq_getD [], List.getElem_eq_getD []]
  rw [hLeft] at hn
  rw [getD_rectangularize outer inner (Two.mul p q) n hn,
    ← mulRow_eq_getD]
  exact hRows n hn

/-- Evaluate a dense multiplication table assembled from checked padded rows. -/
theorem eval_mulData_eq_mul_of_rows
    (outer inner : ℕ) (p q mulData : Two)
    (hMulOuter : (Two.mul p q).length ≤ outer)
    (hDataOuter : mulData.length ≤ outer)
    (hRows : ∀ n, n < outer →
      padOne inner (mulRow p q n) =
        (rectangularize outer inner mulData).getD n [])
    (r s : ℚ) :
    Two.eval mulData r s = Two.eval p r s * Two.eval q r s := by
  have hRectangular := congrArg (fun z ↦ Two.eval z r s)
    (rectangularize_mul_eq_of_rows outer inner p q mulData
      hMulOuter hDataOuter hRows)
  simpa only [eval_rectangularize, Two.eval_mul] using hRectangular.symm

end MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
