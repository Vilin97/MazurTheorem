/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Total complexes of first-quadrant bicomplexes

Supply the standard signs for cochain complexes indexed by the natural numbers, so that
mathlib's existing total-complex construction applies to first-quadrant bicomplexes.
-/

namespace ComplexShape

/-- The standard tensor signs for natural-number-indexed cochain complexes. -/
instance upNat_tensorSigns : TensorSigns (up ℕ) where
  ε' := MonoidHom.mk' (fun n : Multiplicative ℕ ↦ (-1 : ℤˣ) ^ n.toAdd) (by
    intro m n
    exact pow_add (-1 : ℤˣ) m.toAdd n.toAdd)
  rel_add p q r hpq := by
    change p + r + 1 = q + r
    change p + 1 = q at hpq
    omega
  add_rel p q r hpq := by
    change r + p + 1 = r + q
    change p + 1 = q at hpq
    omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -((-1 : ℤˣ) ^ p)
    calc
      (-1 : ℤˣ) ^ (p + 1) = (-1 : ℤˣ) ^ p * (-1 : ℤˣ) :=
        pow_succ _ _
      _ = -((-1 : ℤˣ) ^ p) := by rw [mul_neg, mul_one]

@[simp]
lemma ε_up_ℕ (n : ℕ) : (up ℕ).ε n = (-1 : ℤˣ) ^ n :=
  rfl

/-- The standard Koszul symmetry for first-quadrant total complexes. -/
instance upNat_totalComplexShapeSymmetry :
    TotalComplexShapeSymmetry (up ℕ) (up ℕ) (up ℕ) where
  symm p q := add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, add_mul, one_mul]
    calc
      (-1 : ℤˣ) ^ (p * q) =
          ((-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ q) * (-1 : ℤˣ) ^ (p * q) := by
        rw [Int.units_mul_self, one_mul]
      _ = (-1 : ℤˣ) ^ q *
          ((-1 : ℤˣ) ^ (p * q) * (-1 : ℤˣ) ^ q) := by
        ac_rfl
      _ = (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ (p * q + q) := by
        exact congrArg (fun z ↦ (-1 : ℤˣ) ^ q * z)
          (pow_add (-1 : ℤˣ) (p * q) q).symm
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, mul_add, mul_one]
    exact (pow_add (-1 : ℤˣ) (p * q) p).symm

@[simp]
lemma σ_up_ℕ (p q : ℕ) :
    σ (up ℕ) (up ℕ) (up ℕ) p q = (-1 : ℤˣ) ^ (p * q) :=
  rfl

end ComplexShape
