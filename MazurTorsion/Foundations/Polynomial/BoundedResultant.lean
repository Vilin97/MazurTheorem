/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Bounded polynomial resultants

This file collects bridges used by exact-arithmetic polynomial certificates.
The first transports a pseudo-remainder identity to bounded resultants.  The
remaining results turn a nonzero bounded resultant against a monic polynomial
into the usual resultant, coprimality, and no-common-root conclusions, without
requiring the left polynomial to retain its generic degree after specialization.
-/

open Polynomial

namespace MazurTorsion.PolynomialResultant

variable {R : Type*} [CommRing R]

/-- A pseudo-remainder identity, with all degree padding explicit, induces
the corresponding identity between bounded resultants. -/
theorem bounded_resultant_pseudoRemainder
    (a b q r : R[X]) (l c : R) (m n k delta : ℕ)
    (hb : b.natDegree ≤ n)
    (hr : r.natDegree ≤ k) (hq : q.natDegree + n ≤ m)
    (hkm : k ≤ m) (hbl : b.coeff n = l)
    (hid : Polynomial.C (l ^ delta) * a =
      Polynomial.C c * r + b * q) :
    l ^ (delta * n) * a.resultant b m n =
      (-1 : R) ^ (n * (m - k)) * l ^ (m - k) * c ^ n *
        r.resultant b k n := by
  rw [pow_mul, ← resultant_C_mul_left, hid]
  rw [resultant_add_mul_left _ _ _ _ _ hq hb]
  rw [show m = k + (m - k) by omega]
  have hcr : (Polynomial.C c * r).natDegree ≤ k :=
    (Polynomial.natDegree_C_mul_le c r).trans hr
  rw [resultant_add_left_deg _ _ _ _ _ hcr, hbl]
  rw [resultant_C_mul_left]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- A nonzero bounded resultant against a monic polynomial is already a
nonzero ordinary resultant.  Only a degree bound is needed on the left
polynomial, so this remains useful when specialization drops its degree. -/
theorem resultant_ne_zero_of_bounded_resultant_ne_zero
    {f g : R[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic)
    (hres : resultant f g m n ≠ 0) :
    resultant f g ≠ 0 := by
  have hcoeff : g.coeff n = 1 := by
    rw [← hg]
    exact hmonic
  intro hzero
  apply hres
  have hm : m = f.natDegree + (m - f.natDegree) := by omega
  rw [hm, resultant_add_left_deg _ _ _ _ _ le_rfl, hcoeff]
  simp only [one_pow, mul_one]
  rw [← hg]
  exact mul_eq_zero_of_right _ hzero

/-- A nonzero bounded resultant against a monic polynomial over a field
makes the two polynomials coprime. -/
theorem isCoprime_of_bounded_resultant_ne_zero
    {K : Type*} [Field K] {f g : K[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic)
    (hres : resultant f g m n ≠ 0) :
    IsCoprime f g := by
  have hraw : resultant f g ≠ 0 :=
    resultant_ne_zero_of_bounded_resultant_ne_zero hf hg hmonic hres
  by_contra hnot
  apply hraw
  exact resultant_eq_zero_iff.mpr ⟨Or.inr hmonic.ne_zero, hnot⟩

/-- Coprime polynomials have nonzero bounded resultant when the right
polynomial is monic and the degree padding is explicit.  The left polynomial
may lose degree after specialization. -/
theorem bounded_resultant_ne_zero_of_isCoprime
    {K : Type*} [Field K] {f g : K[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic) (hcop : IsCoprime f g) :
    resultant f g m n ≠ 0 := by
  have hraw : resultant f g ≠ 0 :=
    Polynomial.resultant_ne_zero f g hcop
  have hcoeff : g.coeff n = 1 := by
    rw [← hg]
    exact hmonic.coeff_natDegree
  have hm : m = f.natDegree + (m - f.natDegree) := by omega
  rw [hm, resultant_add_left_deg _ _ _ _ _ le_rfl, hcoeff]
  simp only [one_pow, mul_one]
  rw [← hg]
  exact mul_ne_zero (by simp) hraw

/-- A nonzero bounded resultant against a monic polynomial rules out a
common root after specialization. -/
theorem eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
    {K : Type*} [Field K] {f g : K[X]} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree = n)
    (hmonic : g.Monic)
    (hres : resultant f g m n ≠ 0) (x : K) :
    f.eval x ≠ 0 ∨ g.eval x ≠ 0 := by
  have hcop : IsCoprime f g :=
    isCoprime_of_bounded_resultant_ne_zero hf hg hmonic hres
  simpa [aeval_def] using aeval_ne_zero_of_isCoprime hcop x

end MazurTorsion.PolynomialResultant
