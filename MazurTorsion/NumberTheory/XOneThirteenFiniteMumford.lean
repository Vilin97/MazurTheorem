/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenFiniteField
import MazurTorsion.NumberTheory.XOneThirteenMumfordCoordinates

/-!
# Fixed balanced Mumford records for `X₁(13)` over `𝔽₃`

This file enumerates actual polynomial coordinate records for the reduction
of

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`

over `𝔽₃`.  The even-degree model has two normalized infinity
directions, denoted informally by `∞⁺` and `∞⁻`.  A balanced record
encodes an effective divisor of degree two before subtracting
`D∞ = ∞⁺ + ∞⁻`:

* degree zero stores the number `0`, `1`, or `2` of copies of `∞⁻`;
* degree one stores an affine point and `0` or `1` copy of `∞⁻`;
* degree two stores monic `u = X² + u₁X + u₀` and
  `v = v₁X + v₀`.

The remaining infinity copies are necessarily `∞⁺`.  Thus monicity,
degree bounds, and the infinity balance are canonical by construction.  For
degree one and two, the scalar validity predicate is proved equivalent to
the genuine polynomial condition `u ∣ f - v²`.

Kernel evaluation with `decide` gives `3 + 8 + 8 = 19` valid records.  The
six checked reduced curve points embed injectively into these records.

This is a fixed finite-field coordinate certificate.  It does not define a
generic Mumford representation, a divisor-class quotient, or a rational
Jacobian.
-/

namespace MazurTorsion.XOneThirteenFiniteMumford

open Polynomial
open XOneThirteenFiniteField

/-! ## Canonical coefficient encodings -/

/-- Raw balanced coordinates.  The three summands encode support degrees
`0`, `1`, and `2`, respectively. -/
abbrev RawBalancedMumfordF3 :=
  Fin 3 ⊕ ((F3 × F3 × Fin 2) ⊕ (F3 × F3 × F3 × F3))

/-- Degree-zero coordinates, with the number of copies of `∞⁻`. -/
def rawDegreeZero (infinityMinus : Fin 3) : RawBalancedMumfordF3 :=
  .inl infinityMinus

/-- Degree-one coordinates.  The two field entries are the affine point
`(x,y)`; the last entry records whether the other point is `∞⁺` or `∞⁻`. -/
def rawDegreeOne (x y : F3) (infinityMinus : Fin 2) :
    RawBalancedMumfordF3 :=
  .inr (.inl (x, y, infinityMinus))

/-- Degree-two affine coordinates `(u₀,u₁,v₀,v₁)`. -/
def rawDegreeTwo (u₀ u₁ v₀ v₁ : F3) : RawBalancedMumfordF3 :=
  .inr (.inr (u₀, u₁, v₀, v₁))

/-- Affine support degree of a raw record. -/
def supportDegree : RawBalancedMumfordF3 → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- Number of copies of the negative infinity direction in the balanced
effective divisor. -/
def infinityMinusCount : RawBalancedMumfordF3 → ℕ
  | .inl n => n
  | .inr (.inl (_, _, n)) => n
  | .inr (.inr _) => 0

/-! ## Computable scalar validity -/

/-- Constant remainder after dividing the fixed sextic minus `v²` by the
monic quadratic `u`. -/
def remainderConstantF3 (u₀ u₁ v₀ v₁ : F3) : F3 :=
  -u₀ ^ 3 + 3 * u₀ ^ 2 * u₁ ^ 2 - 4 * u₀ ^ 2 * u₁ + u₀ ^ 2 -
    u₀ * u₁ ^ 4 + 2 * u₀ * u₁ ^ 3 - u₀ * u₁ ^ 2 +
    2 * u₀ * u₁ + u₀ * v₁ ^ 2 - 6 * u₀ - v₀ ^ 2 + 1

/-- Linear remainder after the same fixed polynomial division. -/
def remainderLinearF3 (u₀ u₁ v₀ v₁ : F3) : F3 :=
  -3 * u₀ ^ 2 * u₁ + 2 * u₀ ^ 2 + 4 * u₀ * u₁ ^ 3 -
    6 * u₀ * u₁ ^ 2 + 2 * u₀ * u₁ - 2 * u₀ - u₁ ^ 5 +
    2 * u₁ ^ 4 - u₁ ^ 3 + 2 * u₁ ^ 2 + u₁ * v₁ ^ 2 -
    6 * u₁ - 2 * v₀ * v₁ + 4

/-- Computable validity of a raw balanced record. -/
def IsValid : RawBalancedMumfordF3 → Prop
  | .inl _ => True
  | .inr (.inl (x, y, _)) => y ^ 2 = sexticValue x
  | .inr (.inr (u₀, u₁, v₀, v₁)) =>
      remainderConstantF3 u₀ u₁ v₀ v₁ = 0 ∧
        remainderLinearF3 u₀ u₁ v₀ v₁ = 0

instance (D : RawBalancedMumfordF3) : Decidable (IsValid D) := by
  rcases D with n | h
  · exact isTrue trivial
  · rcases h with p | q
    · rcases p with ⟨x, y, n⟩
      change Decidable (y ^ 2 = sexticValue x)
      exact inferInstance
    · rcases q with ⟨u₀, u₁, v₀, v₁⟩
      change Decidable
        (remainderConstantF3 u₀ u₁ v₀ v₁ = 0 ∧
          remainderLinearF3 u₀ u₁ v₀ v₁ = 0)
      exact inferInstance

/-- Valid balanced Mumford records for the fixed reduced sextic. -/
def BalancedMumfordF3 :=
  {D : RawBalancedMumfordF3 // IsValid D}

instance : Fintype BalancedMumfordF3 := by
  unfold BalancedMumfordF3
  infer_instance

/-- There are three valid degree-zero infinity configurations. -/
theorem card_degreeZero :
    Fintype.card {D : BalancedMumfordF3 // supportDegree D.1 = 0} = 3 := by
  decide

/-- There are eight valid degree-one balanced records. -/
theorem card_degreeOne :
    Fintype.card {D : BalancedMumfordF3 // supportDegree D.1 = 1} = 8 := by
  decide

/-- There are eight valid degree-two affine records. -/
theorem card_degreeTwo :
    Fintype.card {D : BalancedMumfordF3 // supportDegree D.1 = 2} = 8 := by
  decide

/-- The complete fixed record set has nineteen elements. -/
theorem card_balancedMumfordF3 :
    Fintype.card BalancedMumfordF3 = 19 := by
  decide

/-! ## Polynomial meaning and reducedness -/

/-- The monic affine support polynomial encoded by a raw record. -/
noncomputable def recordU : RawBalancedMumfordF3 → F3[X]
  | .inl _ => 1
  | .inr (.inl (x, _, _)) => X - C x
  | .inr (.inr (u₀, u₁, _, _)) => X ^ 2 + C u₁ * X + C u₀

/-- The interpolating ordinate polynomial encoded by a raw record. -/
noncomputable def recordV : RawBalancedMumfordF3 → F3[X]
  | .inl _ => 0
  | .inr (.inl (_, y, _)) => C y
  | .inr (.inr (_, _, v₀, v₁)) => C v₁ * X + C v₀

/-- Structural reducedness and balance conditions for a raw encoding. -/
def IsReducedEncoding (D : RawBalancedMumfordF3) : Prop :=
  (recordU D).Monic ∧
    (recordU D).natDegree = supportDegree D ∧
    (recordV D).degree < (recordU D).degree ∧
    infinityMinusCount D + supportDegree D ≤ 2

/-- Every raw constructor is canonically monic, reduced, and balanced. -/
theorem raw_isReducedEncoding (D : RawBalancedMumfordF3) :
    IsReducedEncoding D := by
  rcases D with n | h
  · simp only [IsReducedEncoding, recordU, recordV, supportDegree,
      infinityMinusCount, monic_one, natDegree_one, degree_zero,
      degree_one, true_and]
    constructor
    · simp
    · simpa using Nat.le_pred_of_lt n.isLt
  · rcases h with p | z
    · rcases p with ⟨x, y, n⟩
      simp only [IsReducedEncoding, recordU, recordV, supportDegree,
        infinityMinusCount]
      constructor
      · exact monic_X_sub_C x
      constructor
      · simp
      constructor
      · rw [degree_X_sub_C]
        exact degree_C_le.trans_lt (by norm_num)
      · omega
    · rcases z with ⟨u₀, u₁, v₀, v₁⟩
      simp only [IsReducedEncoding, recordU, recordV, supportDegree,
        infinityMinusCount, Nat.zero_add]
      constructor
      · monicity <;> norm_num
      constructor
      · compute_degree <;> norm_num
      constructor
      · have huDegree :
            (X ^ 2 + C u₁ * X + C u₀ : F3[X]).degree = 2 := by
            compute_degree <;> norm_num
        rw [huDegree]
        compute_degree
        all_goals norm_num
      · norm_num

/-- Quotient in the fixed monic-quadratic division identity over `𝔽₃`. -/
noncomputable def quotientF3 (u₀ u₁ v₁ : F3) : F3[X] :=
  X ^ 4 + C (2 - u₁) * X ^ 3 +
    C (-u₀ + u₁ ^ 2 - 2 * u₁ + 1) * X ^ 2 +
    C (2 * u₀ * u₁ - 2 * u₀ - u₁ ^ 3 +
      2 * u₁ ^ 2 - u₁ + 2) * X +
    C (u₀ ^ 2 - 3 * u₀ * u₁ ^ 2 + 4 * u₀ * u₁ - u₀ +
      u₁ ^ 4 - 2 * u₁ ^ 3 + u₁ ^ 2 - 2 * u₁ - v₁ ^ 2 + 6)

/-- Exact polynomial division identity over `𝔽₃`. -/
theorem quadratic_division_certificate_F3 (u₀ u₁ v₀ v₁ : F3) :
    sextic - (C v₁ * X + C v₀) ^ 2 =
      (X ^ 2 + C u₁ * X + C u₀) * quotientF3 u₀ u₁ v₁ +
        C (remainderConstantF3 u₀ u₁ v₀ v₁) +
        C (remainderLinearF3 u₀ u₁ v₀ v₁) * X := by
  simp only [sextic, quotientF3, remainderConstantF3,
    remainderLinearF3, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_one]
  ring

/-- The computable scalar test is equivalent to genuine polynomial
divisibility for every canonical record. -/
theorem isValid_iff_polynomialDivisibility (D : RawBalancedMumfordF3) :
    IsValid D ↔ recordU D ∣ sextic - recordV D ^ 2 := by
  rcases D with n | h
  · simp [IsValid, recordU, recordV]
  · rcases h with p | z
    · rcases p with ⟨x, y, n⟩
      rw [IsValid, recordU, recordV, dvd_iff_isRoot]
      simp only [IsRoot, eval_sub, eval_pow, eval_C, eval_sextic]
      constructor
      · exact fun h => sub_eq_zero.mpr h.symm
      · exact fun h => (sub_eq_zero.mp h).symm
    · rcases z with ⟨u₀, u₁, v₀, v₁⟩
      rw [IsValid]
      constructor
      · rintro ⟨h₀, h₁⟩
        refine ⟨quotientF3 u₀ u₁ v₁, ?_⟩
        change sextic - (C v₁ * X + C v₀) ^ 2 =
          (X ^ 2 + C u₁ * X + C u₀) * quotientF3 u₀ u₁ v₁
        rw [quadratic_division_certificate_F3, h₀, h₁]
        simp
      · intro hdvd
        have hu : (X ^ 2 + C u₁ * X + C u₀ : F3[X]).Monic := by
          monicity <;> norm_num
        let rem : F3[X] :=
          C (remainderConstantF3 u₀ u₁ v₀ v₁) +
            C (remainderLinearF3 u₀ u₁ v₀ v₁) * X
        have hsub : (X ^ 2 + C u₁ * X + C u₀ : F3[X]) ∣
            (sextic - (C v₁ * X + C v₀) ^ 2) - rem := by
          refine ⟨quotientF3 u₀ u₁ v₁, ?_⟩
          calc
            (sextic - (C v₁ * X + C v₀) ^ 2) - rem =
                ((X ^ 2 + C u₁ * X + C u₀) * quotientF3 u₀ u₁ v₁ +
                  C (remainderConstantF3 u₀ u₁ v₀ v₁) +
                  C (remainderLinearF3 u₀ u₁ v₀ v₁) * X) - rem := by
                    rw [quadratic_division_certificate_F3]
            _ = (X ^ 2 + C u₁ * X + C u₀) *
                quotientF3 u₀ u₁ v₁ := by
                  simp only [rem]
                  ring
        have hmod := modByMonic_eq_of_dvd_sub hu hsub
        have hpmod : (sextic - (C v₁ * X + C v₀) ^ 2) %ₘ
            (X ^ 2 + C u₁ * X + C u₀) = 0 :=
          (modByMonic_eq_zero_iff_dvd hu).2
            (by simpa [recordU, recordV] using hdvd)
        have hrdeg :
            rem.degree < (X ^ 2 + C u₁ * X + C u₀ : F3[X]).degree := by
          have huDegree :
              (X ^ 2 + C u₁ * X + C u₀ : F3[X]).degree = 2 := by
            compute_degree <;> norm_num
          rw [huDegree]
          dsimp [rem]
          compute_degree
          all_goals norm_num
        have hrmod : rem %ₘ (X ^ 2 + C u₁ * X + C u₀ : F3[X]) = rem :=
          (modByMonic_eq_self_iff hu).2 hrdeg
        rw [hpmod, hrmod] at hmod
        have hz : rem = 0 := hmod.symm
        constructor
        · have hc := congrArg (fun p : F3[X] => p.coeff 0) hz
          simpa [rem] using hc
        · have hc := congrArg (fun p : F3[X] => p.coeff 1) hz
          simpa [rem] using hc

/-- Every valid record satisfies both the reducedness conditions and the
actual fixed-sextic divisibility condition. -/
theorem balancedMumfordF3_spec (D : BalancedMumfordF3) :
    IsReducedEncoding D.1 ∧
      recordU D.1 ∣ sextic - recordV D.1 ^ 2 :=
  ⟨raw_isReducedEncoding D.1,
    (isValid_iff_polynomialDivisibility D.1).mp D.2⟩

/-! ## The six reduced curve points -/

/-- Balanced raw coordinates of a reduced curve point, using `∞⁺` as the
Abel--Jacobi base point.  An affine point is completed by `∞⁻`; `∞⁺` maps
to `D∞-D∞`, while `∞⁻` maps to `2∞⁻-D∞`. -/
def curvePointRaw : PointCertificate → RawBalancedMumfordF3
  | .inl P => rawDegreeOne P.1.1 P.1.2 1
  | .inr P => if P.1 = 1 then rawDegreeZero 1 else rawDegreeZero 2

/-- Each checked reduced curve point gives a valid balanced record. -/
theorem curvePointRaw_valid (P : PointCertificate) :
    IsValid (curvePointRaw P) := by
  rcases P with P | P
  · simpa [curvePointRaw, rawDegreeOne, IsValid] using P.property
  · by_cases h : P.1 = 1
    · simp [curvePointRaw, h, rawDegreeZero, IsValid]
    · simp [curvePointRaw, h, rawDegreeZero, IsValid]

/-- The balanced Mumford record of a checked reduced curve point. -/
def curvePointMumford (P : PointCertificate) : BalancedMumfordF3 :=
  ⟨curvePointRaw P, curvePointRaw_valid P⟩

/-- The six reduced curve points have distinct balanced Mumford records. -/
theorem curvePointRaw_injective : Function.Injective curvePointRaw := by
  decide

/-- Subtype form of the injective curve-to-record map. -/
theorem curvePointMumford_injective : Function.Injective curvePointMumford := by
  intro P Q h
  apply curvePointRaw_injective
  exact congrArg Subtype.val h

/-- Downstream-facing polynomial certificate for each of the six reduced
curve points. -/
theorem curvePointMumford_spec (P : PointCertificate) :
    IsReducedEncoding (curvePointMumford P).1 ∧
      recordU (curvePointMumford P).1 ∣
        sextic - recordV (curvePointMumford P).1 ^ 2 :=
  balancedMumfordF3_spec (curvePointMumford P)

/-- The checked source has six elements and embeds into the nineteen actual
balanced coordinate records. -/
theorem six_curve_points_embed_in_nineteen_records :
    Fintype.card PointCertificate = 6 ∧
      Fintype.card BalancedMumfordF3 = 19 ∧
      Function.Injective curvePointMumford :=
  ⟨card_pointCertificate, card_balancedMumfordF3,
    curvePointMumford_injective⟩

end MazurTorsion.XOneThirteenFiniteMumford
