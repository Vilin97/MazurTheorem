/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentMagmaBridge
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# The small discriminant bound for the `X₁(13)` two-descent field

This file turns the checked change of primitive element into an algebra
equivalence, certifies the discriminant of the alternate monic power basis,
and bounds the absolute field discriminant.  It makes no maximal-order claim.
-/

namespace MazurTorsion.XOneThirteenTwoDescentDiscriminant

open Module Polynomial
open XOneThirteenTwoDescentSextic
open XOneThirteenTwoDescentMagmaBridge

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

theorem magmaRationalSextic_monic : magmaRationalSextic.Monic := by
  rw [magmaRationalSextic_eq_map]
  exact magmaSextic_monic.map (algebraMap ℤ ℚ)

local instance : Nontrivial MagmaAlgebra :=
  AdjoinRoot.nontrivial magmaRationalSextic (by
    rw [show magmaRationalSextic.degree = 6 by
      simp only [magmaRationalSextic]
      compute_degree!]
    norm_num)

theorem oldToMagma_surjective : Function.Surjective oldToMagma := by
  intro z
  induction z using AdjoinRoot.induction_on with
  | ih p =>
      let f : ℚ →+* SexticField := AdjoinRoot.of rationalSextic
      let g : SexticField →+* MagmaAlgebra := oldToMagma.toRingHom
      refine ⟨p.eval₂ f magmaRootPreimage, ?_⟩
      change g (p.eval₂ f magmaRootPreimage) = AdjoinRoot.mk magmaRationalSextic p
      rw [p.hom_eval₂ f g magmaRootPreimage]
      have hcomp : g.comp f = AdjoinRoot.of magmaRationalSextic := by
        ext q
        change oldToMagma (algebraMap ℚ SexticField q) =
          algebraMap ℚ MagmaAlgebra q
        exact oldToMagma.commutes q
      rw [hcomp]
      change p.eval₂ (AdjoinRoot.of magmaRationalSextic)
        (oldToMagma magmaRootPreimage) = AdjoinRoot.mk magmaRationalSextic p
      rw [oldToMagma_magmaRootPreimage]
      simpa only [a, ← AdjoinRoot.algebraMap_eq, Polynomial.aeval_def] using
        (AdjoinRoot.aeval_eq (f := magmaRationalSextic) p)

theorem oldToMagma_injective : Function.Injective oldToMagma := by
  exact RingHom.injective oldToMagma.toRingHom

/-- The exact checked change of primitive element as an algebra equivalence. -/
noncomputable def oldToMagmaEquiv : SexticField ≃ₐ[ℚ] MagmaAlgebra :=
  AlgEquiv.ofBijective oldToMagma
    ⟨oldToMagma_injective, oldToMagma_surjective⟩

@[simp]
theorem oldToMagmaEquiv_theta : oldToMagmaEquiv theta = thetaValue :=
  oldToMagma_theta

/-- The monic power basis in the alternate quotient presentation. -/
noncomputable def magmaQuotientPowerBasis : PowerBasis ℚ MagmaAlgebra :=
  AdjoinRoot.powerBasis' magmaRationalSextic_monic

theorem magmaQuotientPowerBasis_minpolyGen :
    magmaQuotientPowerBasis.minpolyGen = magmaRationalSextic := by
  rw [PowerBasis.minpolyGen_eq]
  change minpoly ℚ (AdjoinRoot.root magmaRationalSextic) =
    magmaRationalSextic
  rw [AdjoinRoot.minpoly_root magmaRationalSextic_monic.ne_zero,
    magmaRationalSextic_monic.leadingCoeff]
  simp

/-- The same power basis transported to the existing sextic field. -/
noncomputable def magmaFieldPowerBasis : PowerBasis ℚ SexticField :=
  magmaQuotientPowerBasis.map oldToMagmaEquiv.symm

theorem magmaFieldPowerBasis_minpolyGen :
    magmaFieldPowerBasis.minpolyGen = magmaRationalSextic := by
  rw [magmaFieldPowerBasis, PowerBasis.minpolyGen_map,
    magmaQuotientPowerBasis_minpolyGen]

@[simp]
theorem magmaQuotientPowerBasis_dim : magmaQuotientPowerBasis.dim = 6 := by
  change magmaRationalSextic.natDegree = 6
  simp only [magmaRationalSextic]
  compute_degree!

private def magmaIndexEquiv : Fin magmaQuotientPowerBasis.dim ≃ Fin 6 :=
  finCongr magmaQuotientPowerBasis_dim

/-- The companion matrix of multiplication by the alternate primitive
element, written in the six-term power basis. -/
def magmaCompanionMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  Matrix.reindexAlgEquiv ℚ ℚ magmaIndexEquiv
    (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis
      magmaQuotientPowerBasis.gen)

theorem magmaCompanionMatrix_eq :
    magmaCompanionMatrix =
      !![0, 0, 0, 0, 0, -1;
         1, 0, 0, 0, 0,  2;
         0, 1, 0, 0, 0, -4;
         0, 0, 1, 0, 0,  4;
         0, 0, 0, 1, 0, -3;
         0, 0, 0, 0, 1,  2] := by
  rw [magmaCompanionMatrix, magmaQuotientPowerBasis.leftMulMatrix,
    magmaQuotientPowerBasis_minpolyGen]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindexAlgEquiv, Matrix.reindexLinearEquiv,
      Matrix.reindex, magmaIndexEquiv, magmaRationalSextic,
      Polynomial.coeff_one, Polynomial.coeff_X]

private theorem matrix_trace_reindex {m n R : Type*}
    [Fintype m] [Fintype n] [CommRing R]
    (e : m ≃ n) (M : Matrix m m R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  rw [Matrix.trace, Matrix.trace, Matrix.reindex_apply]
  exact e.symm.sum_comp (fun i => M i i)

/-- The eleven traces needed for the six-by-six power-basis trace matrix. -/
def magmaPowerTraceValues : Fin 11 → ℚ :=
  ![6, 2, -2, 2, 2, -8, -8, 2, -6, -16, 8]

theorem magmaQuotientPowerBasis_trace_pow (k : Fin 11) :
    Algebra.trace ℚ MagmaAlgebra
        (magmaQuotientPowerBasis.gen ^ (k : ℕ)) =
      magmaPowerTraceValues k := by
  rw [Algebra.trace_eq_matrix_trace magmaQuotientPowerBasis.basis]
  calc
    Matrix.trace
        (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis
          (magmaQuotientPowerBasis.gen ^ (k : ℕ))) =
        Matrix.trace
          (Matrix.reindex magmaIndexEquiv magmaIndexEquiv
            (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis
              (magmaQuotientPowerBasis.gen ^ (k : ℕ)))) :=
      (matrix_trace_reindex magmaIndexEquiv _).symm
    _ = Matrix.trace (magmaCompanionMatrix ^ (k : ℕ)) := by
      change Matrix.trace
        ((Matrix.reindexAlgEquiv ℚ ℚ magmaIndexEquiv)
          (Algebra.leftMulMatrix magmaQuotientPowerBasis.basis
            (magmaQuotientPowerBasis.gen ^ (k : ℕ)))) = _
      rw [map_pow, map_pow]
      rfl
    _ = magmaPowerTraceValues k := by
      fin_cases k <;>
        norm_num [magmaPowerTraceValues, magmaCompanionMatrix_eq,
          pow_succ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The trace pairing of the alternate power basis, reindexed by `Fin 6`. -/
def magmaTraceMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  Matrix.reindex magmaIndexEquiv magmaIndexEquiv
    (Algebra.traceMatrix ℚ magmaQuotientPowerBasis.basis)

private def magmaTraceIndex (i j : Fin 6) : Fin 11 :=
  ⟨(magmaIndexEquiv.symm i : ℕ) + (magmaIndexEquiv.symm j : ℕ), by
    have hi := (magmaIndexEquiv.symm i).isLt
    have hj := (magmaIndexEquiv.symm j).isLt
    have hi' : (magmaIndexEquiv.symm i : ℕ) < 6 := by
      simpa only [magmaQuotientPowerBasis_dim] using hi
    have hj' : (magmaIndexEquiv.symm j : ℕ) < 6 := by
      simpa only [magmaQuotientPowerBasis_dim] using hj
    omega⟩

private theorem magmaTraceMatrix_eq_hankel :
    magmaTraceMatrix = fun i j => magmaPowerTraceValues (magmaTraceIndex i j) := by
  ext i j
  rw [magmaTraceMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    magmaQuotientPowerBasis.basis_eq_pow, magmaQuotientPowerBasis.basis_eq_pow,
    ← pow_add]
  exact magmaQuotientPowerBasis_trace_pow (magmaTraceIndex i j)

/-- The concrete Hankel matrix used as the discriminant certificate. -/
def magmaTraceCertificateMatrix : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ 6,  2, -2,  2,  2,  -8;
      2, -2,  2,  2, -8,  -8;
     -2,  2,  2, -8, -8,   2;
      2,  2, -8, -8,  2,  -6;
      2, -8, -8,  2, -6, -16;
     -8, -8,  2, -6, -16,  8]

theorem magmaTraceMatrix_eq :
    magmaTraceMatrix = magmaTraceCertificateMatrix := by
  rw [magmaTraceMatrix_eq_hankel]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [magmaTraceCertificateMatrix, magmaTraceIndex,
      magmaPowerTraceValues, magmaIndexEquiv]

private def magmaTraceLower : Matrix (Fin 6) (Fin 6) ℚ :=
  !![   1,    0,    0,     0,  0, 0;
      1/3,    1,    0,     0,  0, 0;
     -1/3,   -1,    1,     0,  0, 0;
      1/3, -1/2, -3/2,     1,  0, 0;
      1/3, 13/4,   -4, 27/17,  1, 0;
     -4/3,    2, -3/2, 15/17, 10, 1]

private def magmaTraceUpper : Matrix (Fin 6) (Fin 6) ℚ :=
  !![6,    2,   -2,   2,      2,     -8;
     0, -8/3,  8/3, 4/3,  -26/3,  -16/3;
     0,    0,    4,  -6,    -16,     -6;
     0,    0,    0, -17,    -27,    -15;
     0,    0,    0,   0,  13/34,  65/17;
     0,    0,    0,   0,      0,    -26]

private theorem magmaTraceCertificateMatrix_eq_mul :
    magmaTraceCertificateMatrix = magmaTraceLower * magmaTraceUpper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [magmaTraceCertificateMatrix, magmaTraceLower, magmaTraceUpper,
      Matrix.mul_apply, Fin.sum_univ_succ]

private theorem magmaTraceLower_det : Matrix.det magmaTraceLower = 1 := by
  rw [← Matrix.det_transpose magmaTraceLower,
    Matrix.det_of_upperTriangular]
  · norm_num [magmaTraceLower, Matrix.transpose_apply,
      Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [magmaTraceLower, Matrix.transpose_apply]

private theorem magmaTraceUpper_det : Matrix.det magmaTraceUpper = -10816 := by
  rw [Matrix.det_of_upperTriangular]
  · norm_num [magmaTraceUpper, Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [magmaTraceUpper]

/-- Exact discriminant of the checked alternate quotient power basis. -/
theorem magmaQuotientPowerBasis_discr :
    Algebra.discr ℚ magmaQuotientPowerBasis.basis = -10816 := by
  rw [Algebra.discr_def, ← Matrix.det_reindex_self magmaIndexEquiv]
  change Matrix.det magmaTraceMatrix = -10816
  rw [magmaTraceMatrix_eq, magmaTraceCertificateMatrix_eq_mul,
    Matrix.det_mul, magmaTraceLower_det, magmaTraceUpper_det, one_mul]

/-- Transporting the alternate power basis through the checked algebra
equivalence does not change its discriminant. -/
theorem magmaFieldPowerBasis_discr :
    Algebra.discr ℚ magmaFieldPowerBasis.basis = -10816 := by
  calc
    Algebra.discr ℚ magmaFieldPowerBasis.basis =
        Algebra.discr ℚ
          (oldToMagmaEquiv.symm ∘ magmaQuotientPowerBasis.basis) := by
      congr 1
    _ = Algebra.discr ℚ magmaQuotientPowerBasis.basis :=
      (Algebra.discr_eq_discr_of_algEquiv
        magmaQuotientPowerBasis.basis oldToMagmaEquiv.symm).symm
    _ = -10816 := magmaQuotientPowerBasis_discr

theorem magmaRoot_isIntegral : IsIntegral ℤ a := by
  refine ⟨magmaSextic, magmaSextic_monic, ?_⟩
  simpa only [magmaSextic, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one] using a_spec

theorem magmaFieldPowerBasis_gen_isIntegral :
    IsIntegral ℤ magmaFieldPowerBasis.gen := by
  have h := magmaRoot_isIntegral.map oldToMagmaEquiv.symm
  simpa [magmaFieldPowerBasis, magmaQuotientPowerBasis, a] using h

theorem magmaFieldPowerBasis_basis_isIntegral
    (i : Fin magmaFieldPowerBasis.dim) :
    IsIntegral ℤ (magmaFieldPowerBasis.basis i) := by
  rw [magmaFieldPowerBasis.basis_eq_pow]
  exact magmaFieldPowerBasis_gen_isIntegral.pow _

/-- The discriminant of the maximal order divides the discriminant of any
integral rational basis.  This is the precise order-index statement needed
below; it does not assert that the supplied basis is an integral basis. -/
theorem numberField_discr_dvd_discr_of_integral_basis
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    {d : ℤ} (hd : Algebra.discr ℚ b = algebraMap ℤ ℚ d) :
    NumberField.discr K ∣ d := by
  let e := b.indexEquiv (NumberField.integralBasis K)
  let b' := b.reindex e
  let P := (NumberField.integralBasis K).toMatrix b'
  have hb' (j : Module.Free.ChooseBasisIndex ℤ
      (NumberField.RingOfIntegers K)) :
      IsIntegral ℤ (b' j) := by
    simpa [b', e] using hb (e.symm j)
  have hP : ∀ i j, IsIntegral ℤ (P i j) := by
    intro i j
    let z : NumberField.RingOfIntegers K := ⟨b' j, hb' j⟩
    have hz : algebraMap (NumberField.RingOfIntegers K) K z = b' j := rfl
    change IsIntegral ℤ
      ((NumberField.integralBasis K).repr (b' j) i)
    rw [← hz,
      NumberField.integralBasis_repr_apply]
    exact isIntegral_algebraMap
  have hdet : IsIntegral ℤ P.det := IsIntegral.det hP
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.1 hdet
  have hb'disc : Algebra.discr ℚ b' = Algebra.discr ℚ b := by
    change Algebra.discr ℚ (b.reindex e) = Algebra.discr ℚ b
    rw [Basis.coe_reindex, Algebra.discr_reindex]
  have hchange :
      Algebra.discr ℚ b' =
        P.det ^ 2 * Algebra.discr ℚ (NumberField.integralBasis K) := by
    calc
      Algebra.discr ℚ b' = Algebra.discr ℚ
          (Matrix.vecMul (NumberField.integralBasis K)
            (((NumberField.integralBasis K).toMatrix b').map
              (algebraMap ℚ K))) :=
        congrArg (Algebra.discr ℚ)
          ((NumberField.integralBasis K).toMatrix_map_vecMul b').symm
      _ = ((NumberField.integralBasis K).toMatrix b').det ^ 2 *
          Algebra.discr ℚ (NumberField.integralBasis K) :=
        Algebra.discr_of_matrix_vecMul (NumberField.integralBasis K)
          ((NumberField.integralBasis K).toMatrix b')
  have hcast :
      algebraMap ℤ ℚ d =
        algebraMap ℤ ℚ (q ^ 2 * NumberField.discr K) := by
    calc
      algebraMap ℤ ℚ d = Algebra.discr ℚ b := hd.symm
      _ = Algebra.discr ℚ b' := hb'disc.symm
      _ = P.det ^ 2 * Algebra.discr ℚ (NumberField.integralBasis K) := hchange
      _ = algebraMap ℤ ℚ (q ^ 2 * NumberField.discr K) := by
        rw [← hq, ← NumberField.coe_discr]
        simp
  have hdq : d = q ^ 2 * NumberField.discr K :=
    Rat.intCast_injective hcast
  exact ⟨q ^ 2, by simpa [mul_comm] using hdq⟩

/-- The maximal-order discriminant divides the checked power-basis
discriminant. -/
theorem sexticField_discr_dvd :
    NumberField.discr SexticField ∣ (-10816 : ℤ) := by
  apply numberField_discr_dvd_discr_of_integral_basis
    magmaFieldPowerBasis.basis magmaFieldPowerBasis_basis_isIntegral
  simpa using magmaFieldPowerBasis_discr

theorem sexticField_discr_natAbs_le :
    (NumberField.discr SexticField).natAbs ≤ 10816 := by
  exact Int.natAbs_le_of_dvd_ne_zero sexticField_discr_dvd (by norm_num)

/-- The actual field discriminant has absolute value at most `10816`.
No maximal-order identification is used. -/
theorem sexticField_discr_abs_le :
    |NumberField.discr SexticField| ≤ 10816 := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast sexticField_discr_natAbs_le

end


end MazurTorsion.XOneThirteenTwoDescentDiscriminant
