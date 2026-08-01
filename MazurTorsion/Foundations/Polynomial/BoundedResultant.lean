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

section Telescope

variable [IsDomain R]

private theorem resultant_telescope_step
    {A B r s t e f : R} (hr : A * r = e * s)
    (hs : B * s = A * f * t) (hA : A ≠ 0) :
    B * r = e * f * t := by
  apply mul_left_cancel₀ hA
  calc
    A * (B * r) = B * (A * r) := by ring
    _ = B * (e * s) := by rw [hr]
    _ = e * (B * s) := by ring
    _ = e * (A * f * t) := by rw [hs]
    _ = A * (e * f * t) := by ring

/-- Telescope for the bounded-resultant degree pattern `33, 7, 6, ..., 0`.

The principal coefficients are cancelled in the coefficient domain, before
the parameter is specialized.  This is the algebraic cancellation used by
the order-seven backtracking resultant certificate. -/
theorem resultant_telescope_33_7
    (R0 R1 R2 R3 R4 R5 R6 : R)
    (L2 L3 L4 L5 L6 E0 E1 E2 E3 E4 E5 E6 U : R)
    (hL2 : L2 ≠ 0) (hL3 : L3 ≠ 0) (hL4 : L4 ≠ 0)
    (hL5 : L5 ≠ 0) (hL6 : L6 ≠ 0)
    (h0 : R0 = -E0 ^ 7 * R1)
    (h1 : L2 ^ 10 * R1 = E1 ^ 6 * R2)
    (h2 : L3 ^ 8 * R2 = L2 ^ 10 * E2 ^ 5 * R3)
    (h3 : L4 ^ 6 * R3 = L3 ^ 8 * E3 ^ 4 * R4)
    (h4 : L5 ^ 4 * R4 = L4 ^ 6 * E4 ^ 3 * R5)
    (h5 : L6 ^ 2 * R5 = L5 ^ 4 * E5 ^ 2 * R6)
    (h6 : R6 = L6 ^ 2 * E6 * U) :
    R0 = -E0 ^ 7 * E1 ^ 6 * E2 ^ 5 * E3 ^ 4 * E4 ^ 3 *
      E5 ^ 2 * E6 * U := by
  have h12 : L3 ^ 8 * R1 = E1 ^ 6 * E2 ^ 5 * R3 :=
    resultant_telescope_step h1 h2 (pow_ne_zero 10 hL2)
  have h123 : L4 ^ 6 * R1 =
      (E1 ^ 6 * E2 ^ 5) * E3 ^ 4 * R4 :=
    resultant_telescope_step h12 h3 (pow_ne_zero 8 hL3)
  have h1234 : L5 ^ 4 * R1 =
      ((E1 ^ 6 * E2 ^ 5) * E3 ^ 4) * E4 ^ 3 * R5 :=
    resultant_telescope_step h123 h4 (pow_ne_zero 6 hL4)
  have h12345 : L6 ^ 2 * R1 =
      (((E1 ^ 6 * E2 ^ 5) * E3 ^ 4) * E4 ^ 3) * E5 ^ 2 * R6 :=
    resultant_telescope_step h1234 h5 (pow_ne_zero 4 hL5)
  have hR1 : R1 =
      E1 ^ 6 * E2 ^ 5 * E3 ^ 4 * E4 ^ 3 * E5 ^ 2 * E6 * U := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hL6)
    rw [h12345, h6]
    ring
  rw [h0, hR1]
  ring

end Telescope

section DegreeTelescope

variable [IsDomain R]

/-- The normalized bounded-resultant telescope for the degree pattern
`33, 7, 6, 5, 4, 3, 2, 1, 0`.

The recurrence hypotheses retain the generated leading coefficients, so an
exact pseudo-remainder certificate can be passed without reshaping.  All
principal-coefficient cancellation happens over the coefficient domain. -/
theorem bounded_resultant_telescope_33_7
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 : R[X])
    (q0 q1 q2 q3 q4 q5 q6 : R[X])
    (L2 L3 L4 L5 L6 L7 E0 E1 E2 E3 E4 E5 E6 U : R)
    (hr1 : r1.natDegree ≤ 7)
    (hr2 : r2.natDegree ≤ 6)
    (hr3 : r3.natDegree ≤ 5)
    (hr4 : r4.natDegree ≤ 4)
    (hr5 : r5.natDegree ≤ 3)
    (hr6 : r6.natDegree ≤ 2)
    (hr7 : r7.natDegree ≤ 1)
    (hr8 : r8.natDegree ≤ 0)
    (hq0 : q0.natDegree + 7 ≤ 33)
    (hq1 : q1.natDegree + 6 ≤ 7)
    (hq2 : q2.natDegree + 5 ≤ 6)
    (hq3 : q3.natDegree + 4 ≤ 5)
    (hq4 : q4.natDegree + 3 ≤ 4)
    (hq5 : q5.natDegree + 2 ≤ 3)
    (hq6 : q6.natDegree + 1 ≤ 2)
    (hlead1 : r1.coeff 7 = 1)
    (hlead2 : r2.coeff 6 = L2)
    (hlead3 : r3.coeff 5 = L3)
    (hlead4 : r4.coeff 4 = L4)
    (hlead5 : r5.coeff 3 = L5)
    (hlead6 : r6.coeff 2 = L6)
    (hlead7 : r7.coeff 1 = L7)
    (hL2 : L2 ≠ 0)
    (hL3 : L3 ≠ 0)
    (hL4 : L4 ≠ 0)
    (hL5 : L5 ≠ 0)
    (hL6 : L6 ≠ 0)
    (hL7 : L7 ≠ 0)
    (hrec0 :
      Polynomial.C ((r1.coeff 7) ^ 27) * r0 =
        r1 * q0 + Polynomial.C E0 * r2)
    (hrec1 :
      Polynomial.C ((r2.coeff 6) ^ 2) * r1 =
        r2 * q1 +
          Polynomial.C ((r1.coeff 7) ^ 2 * E1) * r3)
    (hrec2 :
      Polynomial.C ((r3.coeff 5) ^ 2) * r2 =
        r3 * q2 +
          Polynomial.C ((r2.coeff 6) ^ 2 * E2) * r4)
    (hrec3 :
      Polynomial.C ((r4.coeff 4) ^ 2) * r3 =
        r4 * q3 +
          Polynomial.C ((r3.coeff 5) ^ 2 * E3) * r5)
    (hrec4 :
      Polynomial.C ((r5.coeff 3) ^ 2) * r4 =
        r5 * q4 +
          Polynomial.C ((r4.coeff 4) ^ 2 * E4) * r6)
    (hrec5 :
      Polynomial.C ((r6.coeff 2) ^ 2) * r5 =
        r6 * q5 +
          Polynomial.C ((r5.coeff 3) ^ 2 * E5) * r7)
    (hrec6 :
      Polynomial.C ((r7.coeff 1) ^ 2) * r6 =
        r7 * q6 +
          Polynomial.C ((r6.coeff 2) ^ 2 * E6) * r8)
    (hr8C : r8 = Polynomial.C U) :
    r0.resultant r1 33 7 =
      -E0 ^ 7 * E1 ^ 6 * E2 ^ 5 * E3 ^ 4 *
        E4 ^ 3 * E5 ^ 2 * E6 * U := by
  have hs0 :
      r0.resultant r1 33 7 =
        -E0 ^ 7 * r1.resultant r2 7 6 := by
    have h := bounded_resultant_pseudoRemainder
      r0 r1 q0 r2 1 E0 33 7 6 27
      hr1 hr2 hq0 (by omega) hlead1
      (by simpa [hlead1, add_comm] using hrec0)
    rw [resultant_comm r2 r1 6 7] at h
    norm_num at h ⊢
    simpa using h
  have hs1 :
      L2 ^ 10 * r1.resultant r2 7 6 =
        E1 ^ 6 * r2.resultant r3 6 5 := by
    have h := bounded_resultant_pseudoRemainder
      r1 r2 q1 r3 L2 E1 7 6 5 2
      hr2 hr3 hq1 (by omega) hlead2
      (by simpa [hlead1, hlead2, add_comm] using hrec1)
    rw [resultant_comm r3 r2 5 6] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL2)
    calc
      L2 ^ 2 * (L2 ^ 10 * r1.resultant r2 7 6) =
          L2 ^ 12 * r1.resultant r2 7 6 := by ring
      _ = L2 ^ 2 * E1 ^ 6 * r2.resultant r3 6 5 := h
      _ = L2 ^ 2 *
          (E1 ^ 6 * r2.resultant r3 6 5) := by ring
  have hs2 :
      L3 ^ 8 * r2.resultant r3 6 5 =
        L2 ^ 10 * E2 ^ 5 * r3.resultant r4 5 4 := by
    have h := bounded_resultant_pseudoRemainder
      r2 r3 q2 r4 L3 (L2 ^ 2 * E2) 6 5 4 2
      hr3 hr4 hq2 (by omega) hlead3
      (by simpa [hlead2, hlead3, add_comm] using hrec2)
    rw [resultant_comm r4 r3 4 5] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL3)
    calc
      L3 ^ 2 * (L3 ^ 8 * r2.resultant r3 6 5) =
          L3 ^ 10 * r2.resultant r3 6 5 := by ring
      _ = L3 ^ 2 * (L2 ^ 2 * E2) ^ 5 *
          r3.resultant r4 5 4 := h
      _ = L3 ^ 2 *
          (L2 ^ 10 * E2 ^ 5 * r3.resultant r4 5 4) := by ring
  have hs3 :
      L4 ^ 6 * r3.resultant r4 5 4 =
        L3 ^ 8 * E3 ^ 4 * r4.resultant r5 4 3 := by
    have h := bounded_resultant_pseudoRemainder
      r3 r4 q3 r5 L4 (L3 ^ 2 * E3) 5 4 3 2
      hr4 hr5 hq3 (by omega) hlead4
      (by simpa [hlead3, hlead4, add_comm] using hrec3)
    rw [resultant_comm r5 r4 3 4] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL4)
    calc
      L4 ^ 2 * (L4 ^ 6 * r3.resultant r4 5 4) =
          L4 ^ 8 * r3.resultant r4 5 4 := by ring
      _ = L4 ^ 2 * (L3 ^ 2 * E3) ^ 4 *
          r4.resultant r5 4 3 := h
      _ = L4 ^ 2 *
          (L3 ^ 8 * E3 ^ 4 * r4.resultant r5 4 3) := by ring
  have hs4 :
      L5 ^ 4 * r4.resultant r5 4 3 =
        L4 ^ 6 * E4 ^ 3 * r5.resultant r6 3 2 := by
    have h := bounded_resultant_pseudoRemainder
      r4 r5 q4 r6 L5 (L4 ^ 2 * E4) 4 3 2 2
      hr5 hr6 hq4 (by omega) hlead5
      (by simpa [hlead4, hlead5, add_comm] using hrec4)
    rw [resultant_comm r6 r5 2 3] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL5)
    calc
      L5 ^ 2 * (L5 ^ 4 * r4.resultant r5 4 3) =
          L5 ^ 6 * r4.resultant r5 4 3 := by ring
      _ = L5 ^ 2 * (L4 ^ 2 * E4) ^ 3 *
          r5.resultant r6 3 2 := h
      _ = L5 ^ 2 *
          (L4 ^ 6 * E4 ^ 3 * r5.resultant r6 3 2) := by ring
  have hs5 :
      L6 ^ 2 * r5.resultant r6 3 2 =
        L5 ^ 4 * E5 ^ 2 * r6.resultant r7 2 1 := by
    have h := bounded_resultant_pseudoRemainder
      r5 r6 q5 r7 L6 (L5 ^ 2 * E5) 3 2 1 2
      hr6 hr7 hq5 (by omega) hlead6
      (by simpa [hlead5, hlead6, add_comm] using hrec5)
    rw [resultant_comm r7 r6 1 2] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL6)
    calc
      L6 ^ 2 * (L6 ^ 2 * r5.resultant r6 3 2) =
          L6 ^ 4 * r5.resultant r6 3 2 := by ring
      _ = L6 ^ 2 * (L5 ^ 2 * E5) ^ 2 *
          r6.resultant r7 2 1 := h
      _ = L6 ^ 2 *
          (L5 ^ 4 * E5 ^ 2 * r6.resultant r7 2 1) := by ring
  have hs6 :
      r6.resultant r7 2 1 = L6 ^ 2 * E6 * U := by
    have h := bounded_resultant_pseudoRemainder
      r6 r7 q6 r8 L7 (L6 ^ 2 * E6) 2 1 0 2
      hr7 hr8 hq6 (by omega) hlead7
      (by simpa [hlead6, hlead7, add_comm] using hrec6)
    rw [resultant_comm r8 r7 0 1, hr8C] at h
    norm_num at h ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hL7)
    calc
      L7 ^ 2 * r6.resultant r7 2 1 =
          L7 ^ 2 * (L6 ^ 2 * E6) * U := h
      _ = L7 ^ 2 * (L6 ^ 2 * E6 * U) := by ring
  exact resultant_telescope_33_7
    (r0.resultant r1 33 7) (r1.resultant r2 7 6)
    (r2.resultant r3 6 5) (r3.resultant r4 5 4)
    (r4.resultant r5 4 3) (r5.resultant r6 3 2)
    (r6.resultant r7 2 1)
    L2 L3 L4 L5 L6 E0 E1 E2 E3 E4 E5 E6 U
    hL2 hL3 hL4 hL5 hL6 hs0 hs1 hs2 hs3 hs4 hs5 hs6

end DegreeTelescope

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
