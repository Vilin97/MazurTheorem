/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenFiniteMumford

/-!
# Fixed balanced Mumford records for `X₁(13)` over `𝔽₅`

This file gives a second, independent finite-field certificate for the fixed
hyperelliptic model

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

First, an explicit Bézout identity proves that the sextic modulo `5` is
squarefree.  We then enumerate canonical balanced Mumford records.  As in the
corresponding `𝔽₃` certificate, a record represents an effective divisor of
degree two before subtracting the two-point infinity divisor:

* degree zero records the number of negative infinity directions;
* degree one records an affine point and one remaining infinity direction;
* degree two records monic `u = X² + u₁X + u₀` and
  `v = v₁X + v₀`.

The scalar degree-two validity equations are proved equivalent to the genuine
polynomial condition `u ∣ f - v²`.  Kernel evaluation with `decide` gives
`3 + 8 + 8 = 19` valid records, and the six checked curve points inject into
them.

This is a finite coordinate certificate.  It does not construct a divisor
class quotient or identify the record set with a rational Jacobian.
-/

namespace MazurTorsion.XOneThirteenFiniteMumfordFive

open Polynomial

/-! ## The squarefree sextic and its six curve points -/

/-- The five-element residue field used for this certificate. -/
abbrev F5 := ZMod 5

local instance : NeZero 5 := ⟨by norm_num⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The order-thirteen hyperelliptic sextic reduced modulo `5`. -/
noncomputable def sexticF5 : F5[X] :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- Computable evaluation formula for the sextic modulo `5`. -/
def sexticValueF5 (x : F5) : F5 :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

private lemma five_eq_zero_F5 : (5 : F5) = 0 := by decide

private lemma six_eq_one_F5 : (6 : F5) = 1 := by decide

private lemma polynomial_five_eq_zero_F5 :
    (5 : F5[X]) = 0 := by
  rw [← C_ofNat (R := F5) 5, five_eq_zero_F5, C_0]

private lemma polynomial_six_eq_one_F5 :
    (6 : F5[X]) = 1 := by
  rw [← C_ofNat (R := F5) 6, six_eq_one_F5, C_1]

private lemma polynomial_ten_eq_zero_F5 :
    (10 : F5[X]) = 0 := by
  have hten : (10 : F5) = 0 := by decide
  rw [← C_ofNat (R := F5) 10, hten, C_0]

private lemma C_five_eq_zero_F5 : C (5 : F5) = 0 := by
  rw [five_eq_zero_F5, C_0]

private lemma C_six_eq_one_F5 : C (6 : F5) = 1 := by
  rw [six_eq_one_F5, C_1]

private lemma C_three_mul_two_F5 :
    C (3 : F5) * (2 : F5[X]) = 1 := by
  rw [← C_ofNat (R := F5) 2, ← C_mul]
  have h : (3 : F5) * 2 = 1 := by decide
  rw [h, C_1]

/-- Polynomial evaluation agrees with the computable scalar formula. -/
lemma eval_sexticF5 (x : F5) :
    Polynomial.eval x sexticF5 = sexticValueF5 x := by
  simp [sexticF5, sexticValueF5]

/-- Formal derivative of the fixed sextic modulo `5`. -/
lemma derivative_sexticF5 :
    sexticF5.derivative = X ^ 5 + 4 * X ^ 3 + X ^ 2 + 2 * X + 4 := by
  simp [sexticF5, derivative_add, derivative_mul, derivative_pow]
  ring_nf
  rw [C_six_eq_one_F5, C_five_eq_zero_F5,
    polynomial_six_eq_one_F5]
  ring_nf
  calc
    X * C 2 + X ^ 2 * C 3 * 2 + X ^ 3 * C 4 + X ^ 5 =
        X ^ 5 + C 2 * X + (C 3 * (2 : F5[X])) * X ^ 2 +
          C 4 * X ^ 3 := by ring
    _ = X ^ 5 + C 2 * X + X ^ 2 + C 4 * X ^ 3 := by
      rw [C_three_mul_two_F5]
      ring
    _ = X * 2 + X ^ 2 + X ^ 3 * 4 + X ^ 5 := by
      rw [← C_ofNat (R := F5) 2, ← C_ofNat (R := F5) 4]
      ring

/-- Left coefficient in the explicit sextic-derivative Bézout identity. -/
noncomputable def bezoutLeftF5 : F5[X] :=
  -X ^ 3 + X ^ 2 - 2 * X + 2

/-- Right coefficient in the explicit sextic-derivative Bézout identity. -/
noncomputable def bezoutRightF5 : F5[X] :=
  X ^ 4 + X ^ 3 + 2 * X ^ 2 - 2 * X + 1

/-- Explicit gcd certificate for the sextic and its derivative modulo `5`. -/
lemma sexticF5_derivative_bezout :
    bezoutLeftF5 * sexticF5 + bezoutRightF5 * sexticF5.derivative = 1 := by
  rw [derivative_sexticF5]
  simp only [bezoutLeftF5, bezoutRightF5, sexticF5]
  ring_nf
  simp [polynomial_five_eq_zero_F5, polynomial_six_eq_one_F5,
    polynomial_ten_eq_zero_F5]

/-- The sextic is coprime to its derivative modulo `5`. -/
theorem sexticF5_isCoprime_derivative :
    IsCoprime sexticF5 sexticF5.derivative :=
  ⟨bezoutLeftF5, bezoutRightF5, sexticF5_derivative_bezout⟩

/-- The reduction modulo `5` is separable. -/
theorem sexticF5_separable : sexticF5.Separable :=
  sexticF5_isCoprime_derivative

/-- In particular, the reduction modulo `5` is squarefree. -/
theorem sexticF5_squarefree : Squarefree sexticF5 :=
  sexticF5_separable.squarefree

/-- Affine solutions of the reduced hyperelliptic equation. -/
def AffineSolutionF5 :=
  {p : F5 × F5 // p.2 ^ 2 = sexticValueF5 p.1}

instance : Fintype AffineSolutionF5 := by
  unfold AffineSolutionF5
  infer_instance

/-- Complete enumeration of affine solutions modulo `5`. -/
theorem affine_solution_F5_iff :
    ∀ x y : F5,
      y ^ 2 = sexticValueF5 x ↔
        (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = -1 ∧ (y = 1 ∨ y = -1)) := by
  decide

/-- There are four affine solutions modulo `5`. -/
theorem card_affineSolutionF5 :
    Fintype.card AffineSolutionF5 = 4 := by
  decide

/-- The normalized infinity directions `η² = 1` modulo `5`. -/
def InfinityDirectionF5 :=
  {η : F5 // η ^ 2 = 1}

instance : Fintype InfinityDirectionF5 := by
  unfold InfinityDirectionF5
  infer_instance

/-- There are two normalized infinity directions modulo `5`. -/
theorem card_infinityDirectionF5 :
    Fintype.card InfinityDirectionF5 = 2 := by
  decide

/-- The affine points together with the two infinity directions. -/
def PointCertificateF5 :=
  AffineSolutionF5 ⊕ InfinityDirectionF5

instance : Fintype PointCertificateF5 := by
  unfold PointCertificateF5
  infer_instance

/-- The checked curve-point certificate has six elements. -/
theorem card_pointCertificateF5 :
    Fintype.card PointCertificateF5 = 6 := by
  change Fintype.card (AffineSolutionF5 ⊕ InfinityDirectionF5) = 6
  rw [Fintype.card_sum, card_affineSolutionF5, card_infinityDirectionF5]

/-! ## Canonical balanced encodings -/

/-- Raw balanced coordinates in support degrees zero, one, and two. -/
abbrev RawBalancedMumfordF5 :=
  Fin 3 ⊕ ((F5 × F5 × Fin 2) ⊕ (F5 × F5 × F5 × F5))

/-- Degree-zero coordinates, recording the number of copies of `∞⁻`. -/
def rawDegreeZeroF5 (infinityMinus : Fin 3) : RawBalancedMumfordF5 :=
  .inl infinityMinus

/-- Degree-one coordinates `(x,y)` plus the remaining infinity direction. -/
def rawDegreeOneF5 (x y : F5) (infinityMinus : Fin 2) :
    RawBalancedMumfordF5 :=
  .inr (.inl (x, y, infinityMinus))

/-- Degree-two affine coordinates `(u₀,u₁,v₀,v₁)`. -/
def rawDegreeTwoF5 (u₀ u₁ v₀ v₁ : F5) : RawBalancedMumfordF5 :=
  .inr (.inr (u₀, u₁, v₀, v₁))

/-- Affine support degree of a raw record. -/
def supportDegreeF5 : RawBalancedMumfordF5 → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- Number of negative infinity directions in the effective divisor. -/
def infinityMinusCountF5 : RawBalancedMumfordF5 → ℕ
  | .inl n => n
  | .inr (.inl (_, _, n)) => n
  | .inr (.inr _) => 0

/-! ## Scalar validity and exact polynomial division -/

/-- Constant remainder in the fixed monic-quadratic division. -/
def remainderConstantF5 (u₀ u₁ v₀ v₁ : F5) : F5 :=
  -u₀ ^ 3 + 3 * u₀ ^ 2 * u₁ ^ 2 - 4 * u₀ ^ 2 * u₁ + u₀ ^ 2 -
    u₀ * u₁ ^ 4 + 2 * u₀ * u₁ ^ 3 - u₀ * u₁ ^ 2 +
    2 * u₀ * u₁ + u₀ * v₁ ^ 2 - 6 * u₀ - v₀ ^ 2 + 1

/-- Linear remainder in the fixed monic-quadratic division. -/
def remainderLinearF5 (u₀ u₁ v₀ v₁ : F5) : F5 :=
  -3 * u₀ ^ 2 * u₁ + 2 * u₀ ^ 2 + 4 * u₀ * u₁ ^ 3 -
    6 * u₀ * u₁ ^ 2 + 2 * u₀ * u₁ - 2 * u₀ - u₁ ^ 5 +
    2 * u₁ ^ 4 - u₁ ^ 3 + 2 * u₁ ^ 2 + u₁ * v₁ ^ 2 -
    6 * u₁ - 2 * v₀ * v₁ + 4

/-- Computable validity of degree-two coefficient data. -/
def IsValidDegreeTwoF5 : (F5 × F5 × F5 × F5) → Prop
  | (u₀, u₁, v₀, v₁) =>
      remainderConstantF5 u₀ u₁ v₀ v₁ = 0 ∧
        remainderLinearF5 u₀ u₁ v₀ v₁ = 0

instance (z : F5 × F5 × F5 × F5) :
    Decidable (IsValidDegreeTwoF5 z) := by
  rcases z with ⟨u₀, u₁, v₀, v₁⟩
  change Decidable
    (remainderConstantF5 u₀ u₁ v₀ v₁ = 0 ∧
      remainderLinearF5 u₀ u₁ v₀ v₁ = 0)
  exact inferInstance

/-- Valid monic-quadratic coefficient data. -/
def DegreeTwoRecordF5 :=
  {z : F5 × F5 × F5 × F5 // IsValidDegreeTwoF5 z}

instance : Fintype DegreeTwoRecordF5 := by
  unfold DegreeTwoRecordF5
  infer_instance

instance : DecidableEq DegreeTwoRecordF5 := by
  unfold DegreeTwoRecordF5
  infer_instance

/-- Computable validity of a raw balanced record. -/
def IsValidF5 : RawBalancedMumfordF5 → Prop
  | .inl _ => True
  | .inr (.inl (x, y, _)) => y ^ 2 = sexticValueF5 x
  | .inr (.inr z) => IsValidDegreeTwoF5 z

instance (D : RawBalancedMumfordF5) : Decidable (IsValidF5 D) := by
  rcases D with n | h
  · exact isTrue trivial
  · rcases h with p | q
    · rcases p with ⟨x, y, n⟩
      change Decidable (y ^ 2 = sexticValueF5 x)
      exact inferInstance
    · rcases q with ⟨u₀, u₁, v₀, v₁⟩
      change Decidable
        (remainderConstantF5 u₀ u₁ v₀ v₁ = 0 ∧
          remainderLinearF5 u₀ u₁ v₀ v₁ = 0)
      exact inferInstance

/-- Valid balanced Mumford records for the fixed sextic modulo `5`. -/
def BalancedMumfordF5 :=
  {D : RawBalancedMumfordF5 // IsValidF5 D}

instance : Fintype BalancedMumfordF5 := by
  unfold BalancedMumfordF5
  infer_instance

/-- The eight valid degree-two records, displayed as actual coefficients. -/
def degreeTwoRecordOfIndexF5 : Fin 8 → DegreeTwoRecordF5
  | 0 => ⟨(0, 0, 1, 2), by decide⟩
  | 1 => ⟨(0, 0, 4, 3), by decide⟩
  | 2 => ⟨(0, 1, 1, 0), by decide⟩
  | 3 => ⟨(0, 1, 1, 2), by decide⟩
  | 4 => ⟨(0, 1, 4, 0), by decide⟩
  | 5 => ⟨(0, 1, 4, 3), by decide⟩
  | 6 => ⟨(1, 2, 0, 1), by decide⟩
  | 7 => ⟨(1, 2, 0, 4), by decide⟩

/-- The displayed degree-two records are pairwise distinct. -/
theorem degreeTwoRecordOfIndexF5_injective :
    Function.Injective degreeTwoRecordOfIndexF5 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- Bounded exhaustive verification that every valid coefficient tuple occurs
in the displayed eight-element table.  Fixing the first two coefficients
keeps each kernel computation to only twenty-five cases. -/
private theorem degreeTwoRecordF5_exhaustive :
    ∀ u₀ u₁ v₀ v₁ : F5,
      IsValidDegreeTwoF5 (u₀, u₁, v₀, v₁) →
        ∃ i : Fin 8,
          (degreeTwoRecordOfIndexF5 i).1 = (u₀, u₁, v₀, v₁) := by
  intro u₀ u₁
  fin_cases u₀ <;> fin_cases u₁ <;> decide

/-- Every valid degree-two record occurs in the explicit table. -/
theorem degreeTwoRecordOfIndexF5_surjective :
    Function.Surjective degreeTwoRecordOfIndexF5 := by
  rintro ⟨⟨u₀, u₁, v₀, v₁⟩, hvalid⟩
  obtain ⟨i, hi⟩ := degreeTwoRecordF5_exhaustive u₀ u₁ v₀ v₁ hvalid
  exact ⟨i, Subtype.ext hi⟩

/-- The explicit table is equivalent to all valid degree-two records. -/
noncomputable def finEightEquivDegreeTwoRecordF5 : Fin 8 ≃ DegreeTwoRecordF5 :=
  Equiv.ofBijective degreeTwoRecordOfIndexF5
    ⟨degreeTwoRecordOfIndexF5_injective,
      degreeTwoRecordOfIndexF5_surjective⟩

/-- There are exactly eight valid degree-two records. -/
theorem card_degreeTwoRecordF5 :
    Fintype.card DegreeTwoRecordF5 = 8 := by
  calc
    Fintype.card DegreeTwoRecordF5 = Fintype.card (Fin 8) :=
      (Fintype.card_congr finEightEquivDegreeTwoRecordF5).symm
    _ = 8 := Fintype.card_fin 8

/-- Split a valid balanced record into its canonical support-degree data. -/
def balancedMumfordF5Equiv :
    BalancedMumfordF5 ≃
      Fin 3 ⊕ ((AffineSolutionF5 × Fin 2) ⊕ DegreeTwoRecordF5) where
  toFun
    | ⟨.inl n, _⟩ => .inl n
    | ⟨.inr (.inl (x, y, n)), h⟩ =>
        .inr (.inl (⟨(x, y), h⟩, n))
    | ⟨.inr (.inr z), h⟩ => .inr (.inr ⟨z, h⟩)
  invFun
    | .inl n => ⟨.inl n, trivial⟩
    | .inr (.inl (P, n)) => ⟨.inr (.inl (P.1.1, P.1.2, n)), P.2⟩
    | .inr (.inr z) => ⟨.inr (.inr z.1), z.2⟩
  left_inv := by
    rintro ⟨D, h⟩
    rcases D with n | D
    · rfl
    · rcases D with p | z
      · rcases p with ⟨x, y, n⟩
        rfl
      · rfl
  right_inv := by
    intro D
    rcases D with n | D
    · rfl
    · rcases D with p | z
      · rcases p with ⟨P, n⟩
        rcases P with ⟨⟨x, y⟩, h⟩
        rfl
      · rfl

/-- The complete balanced record set modulo `5` has nineteen elements. -/
theorem card_balancedMumfordF5 :
    Fintype.card BalancedMumfordF5 = 19 := by
  rw [Fintype.card_congr balancedMumfordF5Equiv]
  simp [card_affineSolutionF5, card_degreeTwoRecordF5]

/-- The monic affine support polynomial encoded by a raw record. -/
noncomputable def recordUF5 : RawBalancedMumfordF5 → F5[X]
  | .inl _ => 1
  | .inr (.inl (x, _, _)) => X - C x
  | .inr (.inr (u₀, u₁, _, _)) => X ^ 2 + C u₁ * X + C u₀

/-- The interpolating ordinate polynomial encoded by a raw record. -/
noncomputable def recordVF5 : RawBalancedMumfordF5 → F5[X]
  | .inl _ => 0
  | .inr (.inl (_, y, _)) => C y
  | .inr (.inr (_, _, v₀, v₁)) => C v₁ * X + C v₀

/-- Structural monicity, reducedness, and infinity balance. -/
def IsReducedEncodingF5 (D : RawBalancedMumfordF5) : Prop :=
  (recordUF5 D).Monic ∧
    (recordUF5 D).natDegree = supportDegreeF5 D ∧
    (recordVF5 D).degree < (recordUF5 D).degree ∧
    infinityMinusCountF5 D + supportDegreeF5 D ≤ 2

/-- Every raw constructor is canonically monic, reduced, and balanced. -/
theorem raw_isReducedEncodingF5 (D : RawBalancedMumfordF5) :
    IsReducedEncodingF5 D := by
  rcases D with n | h
  · simp only [IsReducedEncodingF5, recordUF5, recordVF5, supportDegreeF5,
      infinityMinusCountF5, monic_one, natDegree_one, degree_zero,
      degree_one, true_and]
    constructor
    · simp
    · simpa using Nat.le_pred_of_lt n.isLt
  · rcases h with p | z
    · rcases p with ⟨x, y, n⟩
      simp only [IsReducedEncodingF5, recordUF5, recordVF5, supportDegreeF5,
        infinityMinusCountF5]
      constructor
      · exact monic_X_sub_C x
      constructor
      · simp
      constructor
      · rw [degree_X_sub_C]
        exact degree_C_le.trans_lt (by norm_num)
      · omega
    · rcases z with ⟨u₀, u₁, v₀, v₁⟩
      simp only [IsReducedEncodingF5, recordUF5, recordVF5, supportDegreeF5,
        infinityMinusCountF5, Nat.zero_add]
      constructor
      · monicity <;> norm_num
      constructor
      · compute_degree <;> norm_num
      constructor
      · have huDegree :
            (X ^ 2 + C u₁ * X + C u₀ : F5[X]).degree = 2 := by
            compute_degree <;> norm_num
        rw [huDegree]
        compute_degree
        all_goals norm_num
      · norm_num

/-- Quotient in the fixed monic-quadratic division identity. -/
noncomputable def quotientF5 (u₀ u₁ v₁ : F5) : F5[X] :=
  X ^ 4 + C (2 - u₁) * X ^ 3 +
    C (-u₀ + u₁ ^ 2 - 2 * u₁ + 1) * X ^ 2 +
    C (2 * u₀ * u₁ - 2 * u₀ - u₁ ^ 3 +
      2 * u₁ ^ 2 - u₁ + 2) * X +
    C (u₀ ^ 2 - 3 * u₀ * u₁ ^ 2 + 4 * u₀ * u₁ - u₀ +
      u₁ ^ 4 - 2 * u₁ ^ 3 + u₁ ^ 2 - 2 * u₁ - v₁ ^ 2 + 6)

/-- Exact polynomial division identity over `𝔽₅`. -/
theorem quadratic_division_certificate_F5 (u₀ u₁ v₀ v₁ : F5) :
    sexticF5 - (C v₁ * X + C v₀) ^ 2 =
      (X ^ 2 + C u₁ * X + C u₀) * quotientF5 u₀ u₁ v₁ +
        C (remainderConstantF5 u₀ u₁ v₀ v₁) +
        C (remainderLinearF5 u₀ u₁ v₀ v₁) * X := by
  simp only [sexticF5, quotientF5, remainderConstantF5,
    remainderLinearF5, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_one]
  ring

/-- Scalar validity is equivalent to genuine fixed-sextic divisibility. -/
theorem isValidF5_iff_polynomialDivisibility (D : RawBalancedMumfordF5) :
    IsValidF5 D ↔ recordUF5 D ∣ sexticF5 - recordVF5 D ^ 2 := by
  rcases D with n | h
  · simp [IsValidF5, recordUF5, recordVF5]
  · rcases h with p | z
    · rcases p with ⟨x, y, n⟩
      rw [IsValidF5, recordUF5, recordVF5, dvd_iff_isRoot]
      simp only [IsRoot, eval_sub, eval_pow, eval_C, eval_sexticF5]
      constructor
      · exact fun h => sub_eq_zero.mpr h.symm
      · exact fun h => (sub_eq_zero.mp h).symm
    · rcases z with ⟨u₀, u₁, v₀, v₁⟩
      rw [IsValidF5]
      constructor
      · rintro ⟨h₀, h₁⟩
        refine ⟨quotientF5 u₀ u₁ v₁, ?_⟩
        change sexticF5 - (C v₁ * X + C v₀) ^ 2 =
          (X ^ 2 + C u₁ * X + C u₀) * quotientF5 u₀ u₁ v₁
        rw [quadratic_division_certificate_F5, h₀, h₁]
        simp
      · intro hdvd
        have hu : (X ^ 2 + C u₁ * X + C u₀ : F5[X]).Monic := by
          monicity <;> norm_num
        let rem : F5[X] :=
          C (remainderConstantF5 u₀ u₁ v₀ v₁) +
            C (remainderLinearF5 u₀ u₁ v₀ v₁) * X
        have hsub : (X ^ 2 + C u₁ * X + C u₀ : F5[X]) ∣
            (sexticF5 - (C v₁ * X + C v₀) ^ 2) - rem := by
          refine ⟨quotientF5 u₀ u₁ v₁, ?_⟩
          calc
            (sexticF5 - (C v₁ * X + C v₀) ^ 2) - rem =
                ((X ^ 2 + C u₁ * X + C u₀) * quotientF5 u₀ u₁ v₁ +
                  C (remainderConstantF5 u₀ u₁ v₀ v₁) +
                  C (remainderLinearF5 u₀ u₁ v₀ v₁) * X) - rem := by
                    rw [quadratic_division_certificate_F5]
            _ = (X ^ 2 + C u₁ * X + C u₀) *
                quotientF5 u₀ u₁ v₁ := by
                  simp only [rem]
                  ring
        have hmod := modByMonic_eq_of_dvd_sub hu hsub
        have hpmod : (sexticF5 - (C v₁ * X + C v₀) ^ 2) %ₘ
            (X ^ 2 + C u₁ * X + C u₀) = 0 :=
          (modByMonic_eq_zero_iff_dvd hu).2
            (by simpa [recordUF5, recordVF5] using hdvd)
        have hrdeg :
            rem.degree < (X ^ 2 + C u₁ * X + C u₀ : F5[X]).degree := by
          have huDegree :
              (X ^ 2 + C u₁ * X + C u₀ : F5[X]).degree = 2 := by
            compute_degree <;> norm_num
          rw [huDegree]
          dsimp [rem]
          compute_degree
          all_goals norm_num
        have hrmod : rem %ₘ (X ^ 2 + C u₁ * X + C u₀ : F5[X]) = rem :=
          (modByMonic_eq_self_iff hu).2 hrdeg
        rw [hpmod, hrmod] at hmod
        have hz : rem = 0 := hmod.symm
        constructor
        · have hc := congrArg (fun p : F5[X] => p.coeff 0) hz
          simpa [rem] using hc
        · have hc := congrArg (fun p : F5[X] => p.coeff 1) hz
          simpa [rem] using hc

/-- Every valid record satisfies reducedness and polynomial divisibility. -/
theorem balancedMumfordF5_spec (D : BalancedMumfordF5) :
    IsReducedEncodingF5 D.1 ∧
      recordUF5 D.1 ∣ sexticF5 - recordVF5 D.1 ^ 2 :=
  ⟨raw_isReducedEncodingF5 D.1,
    (isValidF5_iff_polynomialDivisibility D.1).mp D.2⟩

/-! ## Injection of the six reduced curve points -/

/-- Balanced coordinates of a curve point, using `∞⁺` as base point. -/
def curvePointRawF5 : PointCertificateF5 → RawBalancedMumfordF5
  | .inl P => rawDegreeOneF5 P.1.1 P.1.2 1
  | .inr P => if P.1 = 1 then rawDegreeZeroF5 1 else rawDegreeZeroF5 2

/-- Every checked curve point produces a valid balanced record. -/
theorem curvePointRawF5_valid (P : PointCertificateF5) :
    IsValidF5 (curvePointRawF5 P) := by
  rcases P with P | P
  · simpa [curvePointRawF5, rawDegreeOneF5, IsValidF5] using P.property
  · by_cases h : P.1 = 1
    · simp [curvePointRawF5, h, rawDegreeZeroF5, IsValidF5]
    · simp [curvePointRawF5, h, rawDegreeZeroF5, IsValidF5]

/-- Balanced Mumford record attached to a checked curve point. -/
def curvePointMumfordF5 (P : PointCertificateF5) : BalancedMumfordF5 :=
  ⟨curvePointRawF5 P, curvePointRawF5_valid P⟩

/-- The six curve points have distinct raw balanced records. -/
theorem curvePointRawF5_injective : Function.Injective curvePointRawF5 := by
  decide

/-- The induced map into valid balanced records is injective. -/
theorem curvePointMumfordF5_injective : Function.Injective curvePointMumfordF5 := by
  intro P Q h
  apply curvePointRawF5_injective
  exact congrArg Subtype.val h

/-- Polynomial certificate for each of the six reduced curve points. -/
theorem curvePointMumfordF5_spec (P : PointCertificateF5) :
    IsReducedEncodingF5 (curvePointMumfordF5 P).1 ∧
      recordUF5 (curvePointMumfordF5 P).1 ∣
        sexticF5 - recordVF5 (curvePointMumfordF5 P).1 ^ 2 :=
  balancedMumfordF5_spec (curvePointMumfordF5 P)

/-- Six curve points embed into the nineteen actual balanced records. -/
theorem six_curve_points_embed_in_nineteen_records_F5 :
    Fintype.card PointCertificateF5 = 6 ∧
      Fintype.card BalancedMumfordF5 = 19 ∧
      Function.Injective curvePointMumfordF5 :=
  ⟨card_pointCertificateF5, card_balancedMumfordF5,
    curvePointMumfordF5_injective⟩

end MazurTorsion.XOneThirteenFiniteMumfordFive
