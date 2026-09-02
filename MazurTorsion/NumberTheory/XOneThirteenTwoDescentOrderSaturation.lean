/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentDiscriminant

/-!
# Trace-power certificates for saturation of the `X₁(13)` Magma order

This file records finite certificates for the only rational primes dividing
the discriminant of the checked monogenic order.  The certificates use the
fixed companion matrix and canonical residue representatives, so their
verification is a bounded kernel computation rather than an unbounded search.
-/

namespace MazurTorsion.XOneThirteenTwoDescentOrderSaturation

open Module Polynomial
open scoped Matrix
open XOneThirteenTwoDescentSextic
open XOneThirteenTwoDescentMagmaBridge
open XOneThirteenTwoDescentDiscriminant

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The integral companion matrix of the alternate primitive element. -/
def saturationCompanionMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, -1;
     1, 0, 0, 0, 0,  2;
     0, 1, 0, 0, 0, -4;
     0, 0, 1, 0, 0,  4;
     0, 0, 0, 1, 0, -3;
     0, 0, 0, 0, 1,  2]

/-- Multiplication by the element with six power-basis coordinates `c`. -/
def coefficientMultiplicationMatrix (c : Fin 6 → ℤ) :
    Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j =>
    c 0 * (1 : Matrix (Fin 6) (Fin 6) ℤ) i j +
      c 1 * saturationCompanionMatrix i j +
      c 2 * (saturationCompanionMatrix ^ 2) i j +
      c 3 * (saturationCompanionMatrix ^ 3) i j +
      c 4 * (saturationCompanionMatrix ^ 4) i j +
      c 5 * (saturationCompanionMatrix ^ 5) i j

/-- The integer trace of the `k`-th power of the multiplication matrix. -/
def coefficientPowerTrace (c : Fin 6 → ℤ) (k : ℕ) : ℤ :=
  Matrix.trace (coefficientMultiplicationMatrix c ^ k)

/-- The integral trace-pairing matrix in the fixed power basis. -/
def saturationTraceMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 6,  2, -2,  2,  2,  -8;
      2, -2,  2,  2, -8,  -8;
     -2,  2,  2, -8, -8,   2;
      2,  2, -8, -8,  2,  -6;
      2, -8, -8,  2, -6, -16;
     -8, -8,  2, -6, -16,  8]

/-- The integer trace pairing against the `j`-th power-basis vector. -/
def coefficientPairingTrace (c : Fin 6 → ℤ) (j : Fin 6) : ℤ :=
  ![6 * c 0 + 2 * c 1 - 2 * c 2 + 2 * c 3 + 2 * c 4 - 8 * c 5,
    2 * c 0 - 2 * c 1 + 2 * c 2 + 2 * c 3 - 8 * c 4 - 8 * c 5,
    -2 * c 0 + 2 * c 1 + 2 * c 2 - 8 * c 3 - 8 * c 4 + 2 * c 5,
    2 * c 0 + 2 * c 1 - 8 * c 2 - 8 * c 3 + 2 * c 4 - 6 * c 5,
    2 * c 0 - 8 * c 1 - 8 * c 2 + 2 * c 3 - 6 * c 4 - 16 * c 5,
    -8 * c 0 - 8 * c 1 + 2 * c 2 - 6 * c 3 - 16 * c 4 + 8 * c 5] j

def modTwoLift (v : Fin 6 → ZMod 2) : Fin 6 → ℤ :=
  fun i => (v i).val

def modThirteenLift (v : Fin 6 → ZMod 13) : Fin 6 → ℤ :=
  fun i => (v i).val

private def saturationIndexEquiv :
    Fin magmaQuotientPowerBasis.dim ≃ Fin 6 :=
  finCongr magmaQuotientPowerBasis_dim

/-- Multiplication in the rational Magma presentation, reindexed to the
same fixed coordinates as the integral certificate matrices. -/
def saturationRationalMultiplicationMatrix :
    MagmaAlgebra →ₐ[ℚ] Matrix (Fin 6) (Fin 6) ℚ :=
  (Matrix.reindexAlgEquiv ℚ ℚ saturationIndexEquiv).toAlgHom.comp
    (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis)

theorem saturationRationalMultiplicationMatrix_gen :
    saturationRationalMultiplicationMatrix magmaQuotientPowerBasis.gen =
      saturationCompanionMatrix.map (algebraMap ℤ ℚ) := by
  rw [saturationRationalMultiplicationMatrix]
  change Matrix.reindexAlgEquiv ℚ ℚ saturationIndexEquiv
      (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis
        magmaQuotientPowerBasis.gen) = _
  rw [magmaQuotientPowerBasis.leftMulMatrix,
    magmaQuotientPowerBasis_minpolyGen]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindexAlgEquiv, Matrix.reindexLinearEquiv,
      Matrix.reindex, saturationIndexEquiv, saturationCompanionMatrix,
      magmaRationalSextic, Polynomial.coeff_one, Polynomial.coeff_X]

/-- The element with the displayed integral coordinates in the rational
Magma power basis. -/
def magmaCoefficientElement (c : Fin 6 → ℤ) : MagmaAlgebra :=
  (c 0 : ℚ) • 1 +
    (c 1 : ℚ) • magmaQuotientPowerBasis.gen +
    (c 2 : ℚ) • magmaQuotientPowerBasis.gen ^ 2 +
    (c 3 : ℚ) • magmaQuotientPowerBasis.gen ^ 3 +
    (c 4 : ℚ) • magmaQuotientPowerBasis.gen ^ 4 +
    (c 5 : ℚ) • magmaQuotientPowerBasis.gen ^ 5

theorem saturationRationalMultiplicationMatrix_coefficientElement
    (c : Fin 6 → ℤ) :
    saturationRationalMultiplicationMatrix (magmaCoefficientElement c) =
      (Int.castRingHom ℚ).mapMatrix (coefficientMultiplicationMatrix c) := by
  ext i j
  simp [magmaCoefficientElement, coefficientMultiplicationMatrix,
    saturationRationalMultiplicationMatrix_gen, Matrix.smul_apply,
    Matrix.map_apply]

private theorem matrix_trace_reindex {m n R : Type*}
    [Fintype m] [Fintype n] [CommRing R]
    (e : m ≃ n) (M : Matrix m m R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  rw [Matrix.trace, Matrix.trace, Matrix.reindex_apply]
  exact e.symm.sum_comp (fun i => M i i)

/-- Algebraic traces of powers agree with the retained integer matrix
certificate. -/
theorem magmaCoefficientElement_trace_pow (c : Fin 6 → ℤ) (k : ℕ) :
    Algebra.trace ℚ MagmaAlgebra (magmaCoefficientElement c ^ k) =
      (coefficientPowerTrace c k : ℚ) := by
  rw [Algebra.trace_eq_matrix_trace magmaQuotientPowerBasis.basis]
  calc
    Matrix.trace (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis
        (magmaCoefficientElement c ^ k)) =
        Matrix.trace
          (Matrix.reindex saturationIndexEquiv saturationIndexEquiv
            (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis
              (magmaCoefficientElement c ^ k))) :=
      (matrix_trace_reindex saturationIndexEquiv _).symm
    _ = Matrix.trace
        (saturationRationalMultiplicationMatrix
          (magmaCoefficientElement c) ^ k) := by
      change Matrix.trace
        (saturationRationalMultiplicationMatrix
          (magmaCoefficientElement c ^ k)) = _
      rw [map_pow]
    _ = (coefficientPowerTrace c k : ℚ) := by
      rw [saturationRationalMultiplicationMatrix_coefficientElement,
        ← RingHom.map_pow, coefficientPowerTrace,
        ← AddMonoidHom.map_trace (Int.castRingHom ℚ)
          (coefficientMultiplicationMatrix c ^ k)]

/-- Algebraic trace pairings with the power basis agree with the retained
integer trace matrix. -/
theorem magmaCoefficientElement_trace_mul_gen_pow
    (c : Fin 6 → ℤ) (j : Fin 6) :
    Algebra.trace ℚ MagmaAlgebra
        (magmaCoefficientElement c *
          magmaQuotientPowerBasis.gen ^ (j : ℕ)) =
      (coefficientPairingTrace c j : ℚ) := by
  have t0 := magmaQuotientPowerBasis_trace_pow (0 : Fin 11)
  have t1 := magmaQuotientPowerBasis_trace_pow (1 : Fin 11)
  have t2 := magmaQuotientPowerBasis_trace_pow (2 : Fin 11)
  have t3 := magmaQuotientPowerBasis_trace_pow (3 : Fin 11)
  have t4 := magmaQuotientPowerBasis_trace_pow (4 : Fin 11)
  have t5 := magmaQuotientPowerBasis_trace_pow (5 : Fin 11)
  have t6 := magmaQuotientPowerBasis_trace_pow (6 : Fin 11)
  have t7 := magmaQuotientPowerBasis_trace_pow (7 : Fin 11)
  have t8 := magmaQuotientPowerBasis_trace_pow (8 : Fin 11)
  have t9 := magmaQuotientPowerBasis_trace_pow (9 : Fin 11)
  have t10 := magmaQuotientPowerBasis_trace_pow (10 : Fin 11)
  fin_cases j <;>
    simp [magmaCoefficientElement, coefficientPairingTrace,
      add_mul, smul_mul_assoc, ← pow_add, t0, t1, t2, t3, t4, t5,
      t6, t7, t8, t9, t10, magmaPowerTraceValues] <;>
    ring

/-- Exhaustive 64-case certificate at `2`: the divisibilities forced by
integrality of `h(a)/2` through trace powers one to four leave only the zero
residue vector. -/
theorem modTwo_tracePower_certificate
    (v : Fin 6 → ZMod 2)
    (h1 : (2 : ℤ) ∣ coefficientPowerTrace (modTwoLift v) 1)
    (h2 : (4 : ℤ) ∣ coefficientPowerTrace (modTwoLift v) 2)
    (h3 : (8 : ℤ) ∣ coefficientPowerTrace (modTwoLift v) 3)
    (h4 : (16 : ℤ) ∣ coefficientPowerTrace (modTwoLift v) 4) :
    v = 0 := by
  revert v
  decide

/-- First generator of the two-dimensional trace-pairing kernel modulo
`13`. -/
def modThirteenKernelFirst : Fin 6 → ZMod 13 :=
  ![9, 10, 2, 3, 1, 0]

/-- Second generator of the two-dimensional trace-pairing kernel modulo
`13`. -/
def modThirteenKernelSecond : Fin 6 → ZMod 13 :=
  ![12, 5, 4, 6, 0, 1]

def modThirteenPairingTrace (v : Fin 6 → ZMod 13) (j : Fin 6) :
    ZMod 13 :=
  ![6 * v 0 + 2 * v 1 - 2 * v 2 + 2 * v 3 + 2 * v 4 - 8 * v 5,
    2 * v 0 - 2 * v 1 + 2 * v 2 + 2 * v 3 - 8 * v 4 - 8 * v 5,
    -2 * v 0 + 2 * v 1 + 2 * v 2 - 8 * v 3 - 8 * v 4 + 2 * v 5,
    2 * v 0 + 2 * v 1 - 8 * v 2 - 8 * v 3 + 2 * v 4 - 6 * v 5,
    2 * v 0 - 8 * v 1 - 8 * v 2 + 2 * v 3 - 6 * v 4 - 16 * v 5,
    -8 * v 0 - 8 * v 1 + 2 * v 2 - 6 * v 3 - 16 * v 4 + 8 * v 5] j

/-- The kernel of the six trace-pairing equations modulo `13` has the
displayed two-parameter basis. -/
theorem modThirteen_pairingKernel_parametrization
    (v : Fin 6 → ZMod 13)
    (h : ∀ j, modThirteenPairingTrace v j = 0) :
    v = v 4 • modThirteenKernelFirst +
      v 5 • modThirteenKernelSecond := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp [modThirteenPairingTrace] at h0 h1 h2 h3 h4 h5
  have char13 (x : ZMod 13) : 13 * x = 0 := by
    rw [show (13 : ZMod 13) = 0 by exact ZMod.natCast_self 13,
      zero_mul]
  have c0 : 13 * v 0 = 0 := char13 _
  have c1 : 13 * v 1 = 0 := char13 _
  have c2 : 13 * v 2 = 0 := char13 _
  have c3 : 13 * v 3 = 0 := char13 _
  have c4 : 13 * v 4 = 0 := char13 _
  have c5 : 13 * v 5 = 0 := char13 _
  funext i
  fin_cases i
  · change v 0 = v 4 * 9 + v 5 * 12
    linear_combination 9 * h0 + 2 * h1 + h2 + 5 * h3 -
      5 * c0 - 2 * c1 + 4 * c2 + 2 * c3 - c4 + 8 * c5
  · change v 1 = v 4 * 10 + v 5 * 5
    linear_combination 2 * h0 + 7 * h1 + 6 * h2 + 6 * h3 -
      2 * c0 - c1 + 2 * c2 + 6 * c3 + 6 * c4 + 7 * c5
  · change v 2 = v 4 * 2 + v 5 * 4
    linear_combination h0 + 6 * h1 + 7 * h2 + 11 * h3 -
      2 * c0 - 2 * c1 + 5 * c2 + 10 * c3 + 6 * c4 + 8 * c5
  · change v 3 = v 4 * 3 + v 5 * 6
    linear_combination 5 * h0 + 6 * h1 + 11 * h2 + 3 * h3 -
      2 * c0 - 2 * c1 + 7 * c3 + 9 * c4 + 6 * c5
  · change v 4 = v 4 * 1 + v 5 * 0
    simp
  · change v 5 = v 4 * 0 + v 5 * 1
    simp

/-- Bounded 169-case certificate on the trace-pairing kernel: the power-two
and power-three divisibilities forced by integrality of `h(a)/13` kill both
kernel parameters. -/
theorem modThirteen_tracePower_kernel_certificate
    (r s : ZMod 13)
    (h2 : (169 : ℤ) ∣ coefficientPowerTrace
      (modThirteenLift
        (r • modThirteenKernelFirst + s • modThirteenKernelSecond)) 2)
    (h3 : (2197 : ℤ) ∣ coefficientPowerTrace
      (modThirteenLift
        (r • modThirteenKernelFirst + s • modThirteenKernelSecond)) 3) :
    r = 0 ∧ s = 0 := by
  revert r s
  decide

end

end MazurTorsion.XOneThirteenTwoDescentOrderSaturation
