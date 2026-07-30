/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.NaiveHeightDescent
import MazurTorsion.GroupTheory.IndexNSmulFG
import MazurTorsion.NumberTheory.RatNorthcott
import MazurTorsion.NumberTheory.XOneElevenReduction

/-!
# The explicit descent boundary for `X₁(11)`

For the rational elliptic curve

`v² + v = u³ - u²`,

this file separates the routine Mordell--Weil consequences of a
five-descent from its one genuinely arithmetic input.  In particular:

* finite index of multiplication by five implies finite generation, by
  an explicit five-fold version of naïve-height descent;
* the visible point `(0,0)` has exact order five;
* reduction at three controls rational five-torsion;
* a five-coset certificate for `E(ℚ) / 5 E(ℚ)` implies rank zero and
  finiteness.

The remaining unconditional input is therefore an explicit five-isogeny
Selmer calculation producing the five-coset certificate.
-/

open WeierstrassCurve

namespace WeierstrassCurve.Affine

open Height

/-- The approximate parallelogram law is strong enough to run descent
with multiplication by five. -/
theorem fg_point_of_finiteIndex_five
    (W : WeierstrassCurve ℚ) [W.toAffine.IsElliptic]
    (hindex :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 5).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  let h : W.toAffine.Point → ℝ :=
    Point.naiveHeight
  have hnonneg (P : W.toAffine.Point) : 0 ≤ h P := by
    change 0 ≤ P.naiveHeight
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  have htranslate (G P : W.toAffine.Point) :
      h P ≤ 2 * h (G + P) + (2 * h (-G) + C) := by
    have hpar := hC (G + P) (-G)
    have hrest : 0 ≤ h ((G + P) - (-G)) :=
      hnonneg _
    have hsum : (G + P) + (-G) = P := by
      abel
    rw [hsum] at hpar
    grind
  have hgrowth (P : W.toAffine.Point) :
      25 * h P - (6 * h 0 + 9 * C) ≤ h ((5 : ℕ) • P) := by
    have htwoPar := hC P P
    have htwo :
        4 * h P - (h 0 + C) ≤ h ((2 : ℕ) • P) := by
      have hsum : P + P = (2 : ℕ) • P := by
        abel
      have hdiff : P - P = 0 := sub_self P
      rw [hsum, hdiff] at htwoPar
      grind
    have hthreePar := hC ((2 : ℕ) • P) P
    have hthree :
        9 * h P - (2 * h 0 + 3 * C) ≤ h ((3 : ℕ) • P) := by
      have hsum : (2 : ℕ) • P + P = (3 : ℕ) • P := by
        abel
      have hdiff : (2 : ℕ) • P - P = P := by
        abel
      rw [hsum, hdiff] at hthreePar
      grind
    have hfivePar := hC ((3 : ℕ) • P) ((2 : ℕ) • P)
    have hsum :
        (3 : ℕ) • P + (2 : ℕ) • P = (5 : ℕ) • P := by
      abel
    have hdiff :
        (3 : ℕ) • P - (2 : ℕ) • P = P := by
      abel
    rw [hsum, hdiff] at hfivePar
    grind
  letI : Northcott h := by
    dsimp only [h]
    infer_instance
  exact
    AddCommGroup.fg_of_descent
      (n := 5) (h := h) (a := 2) (b := 25)
      (c₀ := 6 * h 0 + 9 * C)
      (c := fun G ↦ 2 * h (-G) + C)
      (by norm_num) (by norm_num) hindex
      htranslate hgrowth

end WeierstrassCurve.Affine

namespace MazurTorsion.XOneEleven

open WeierstrassCurve.Affine

/-- Multiplication by five on the rational point group. -/
def fiveRange : AddSubgroup curve.toAffine.Point :=
  (nsmulAddMonoidHom (α := curve.toAffine.Point) 5).range

/-- Doubling `(0,0)` gives `(1,-1)`. -/
theorem double_P00 : (2 : ℕ) • P00 = P1n1 := by
  simp only [two_nsmul, P00]
  rw [Point.add_self_of_Y_ne
    (by norm_num [negY, curve])]
  rw [P1n1]
  simp only [Point.some.injEq]
  constructor
  · norm_num [addX, WeierstrassCurve.Affine.slope,
      negY, curve]
  · norm_num [addY, addX,
      WeierstrassCurve.Affine.slope, negY, curve]

private theorem add_P00_P1n1 :
    P00 + P1n1 = P10 := by
  rw [P00, P1n1, P10]
  rw [Point.add_of_X_ne
    (by norm_num : (0 : ℚ) ≠ 1)]
  simp only [Point.some.injEq]
  constructor
  · norm_num [addX, WeierstrassCurve.Affine.slope,
      curve]
  · norm_num [addY, addX,
      WeierstrassCurve.Affine.slope, curve]

/-- Tripling `(0,0)` gives `(1,0)`. -/
theorem triple_P00 : (3 : ℕ) • P00 = P10 := by
  calc
    (3 : ℕ) • P00 = P00 + (2 : ℕ) • P00 := by
      abel
    _ = P00 + P1n1 := by rw [double_P00]
    _ = P10 := add_P00_P1n1

private theorem double_P1n1 :
    (2 : ℕ) • P1n1 = P0n1 := by
  simp only [two_nsmul, P1n1]
  rw [Point.add_self_of_Y_ne
    (by norm_num [negY, curve])]
  rw [P0n1]
  simp only [Point.some.injEq]
  constructor
  · norm_num [addX, WeierstrassCurve.Affine.slope,
      negY, curve]
  · norm_num [addY, addX,
      WeierstrassCurve.Affine.slope, negY, curve]

/-- Four times `(0,0)` is its negative `(0,-1)`. -/
theorem four_P00 : (4 : ℕ) • P00 = P0n1 := by
  calc
    (4 : ℕ) • P00 =
        (2 : ℕ) • ((2 : ℕ) • P00) := by
      norm_num [← mul_nsmul]
    _ = (2 : ℕ) • P1n1 := by rw [double_P00]
    _ = P0n1 := double_P1n1

private theorem neg_P00 :
    -P00 = P0n1 := by
  rw [P00, Point.neg_some, P0n1]
  simp only [Point.some.injEq]
  norm_num [negY, curve]

/-- Five times `(0,0)` is the identity. -/
theorem five_P00 : (5 : ℕ) • P00 = 0 := by
  calc
    (5 : ℕ) • P00 = (4 : ℕ) • P00 + P00 := by
      abel
    _ = P0n1 + P00 := by rw [four_P00]
    _ = -P00 + P00 := by rw [neg_P00]
    _ = 0 := neg_add_cancel P00

instance : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

/-- The visible point `(0,0)` has exact additive order five. -/
theorem addOrderOf_P00 :
    addOrderOf P00 = 5 := by
  exact addOrderOf_eq_prime five_P00
    (by simp [P00])

/-- The Vélu quotient of `curve` by the visible order-five subgroup.
It is the minimal curve customarily labelled `11a1`. -/
def fiveIsogenousCurve : WeierstrassCurve ℚ :=
  ⟨0, -1, 1, -10, -20⟩

instance : fiveIsogenousCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [fiveIsogenousCurve,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- The abscissa in the normalized Vélu map away from its four
nonzero kernel points. -/
def veluFiveX (x _y : ℚ) : ℚ :=
  x + 1 / x ^ 2 + (2 * x - 1) / (x - 1) ^ 2

/-- The ordinate in the normalized Vélu map away from its four
nonzero kernel points. -/
def veluFiveY (x y : ℚ) : ℚ :=
  y - (2 * y + 1) / x ^ 3 -
    x * (2 * y + 1) / (x - 1) ^ 3

/-- The explicit Vélu formulas carry the affine equation for `curve`
to the affine equation for its five-isogenous quotient whenever the
input is outside the kernel.

The factorization used in the proof is

`F'(φ(x,y)) =
 -(x³-4x²+4x-2)² (x³-x²-y²-y)
   (x³+x²+x-1)² / (x⁶(x-1)⁶)`.
-/
theorem veluFive_equation
    {x y : ℚ}
    (hcurve : y ^ 2 + y = x ^ 3 - x ^ 2)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    fiveIsogenousCurve.toAffine.Equation
      (veluFiveX x y) (veluFiveY x y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [fiveIsogenousCurve]
  apply sub_eq_zero.mp
  have hfactor :
      veluFiveY x y ^ 2 + veluFiveY x y -
          (veluFiveX x y ^ 3 - veluFiveX x y ^ 2 -
            10 * veluFiveX x y - 20) =
        -((x ^ 3 - 4 * x ^ 2 + 4 * x - 2) ^ 2 *
            (x ^ 3 - x ^ 2 - y ^ 2 - y) *
          (x ^ 3 + x ^ 2 + x - 1) ^ 2) /
          (x ^ 6 * (x - 1) ^ 6) := by
    simp only [veluFiveX, veluFiveY]
    field_simp [hx0, sub_ne_zero.mpr hx1]
    ring
  have hrel :
      x ^ 3 - x ^ 2 - y ^ 2 - y = 0 := by
    linarith
  calc
    _ =
        veluFiveY x y ^ 2 + veluFiveY x y -
          (veluFiveX x y ^ 3 - veluFiveX x y ^ 2 -
            10 * veluFiveX x y - 20) := by
      ring
    _ =
        -((x ^ 3 - 4 * x ^ 2 + 4 * x - 2) ^ 2 *
            (x ^ 3 - x ^ 2 - y ^ 2 - y) *
            (x ^ 3 + x ^ 2 + x - 1) ^ 2) /
          (x ^ 6 * (x - 1) ^ 6) :=
      hfactor
    _ = 0 := by rw [hrel]; norm_num

/-- The denominator-safe affine part of the explicit Vélu map. -/
def veluFivePoint
    {x y : ℚ}
    (hP : curve.toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    fiveIsogenousCurve.toAffine.Point :=
  .some (veluFiveX x y) (veluFiveY x y)
    (fiveIsogenousCurve.toAffine.equation_iff_nonsingular.mp
      (veluFive_equation
        (by
          have heq := hP.1
          norm_num
            [WeierstrassCurve.Affine.equation_iff,
              curve] at heq ⊢
          simpa only [sub_eq_add_neg] using heq)
        hx0 hx1))

/-- The denominator-safe candidate Vélu map, sending the point at
infinity and the four points with abscissa `0` or `1` to infinity.

Its coordinate identity and zero fiber are checked here.  Proving that
it preserves addition is a separate (substantial) rational-function
calculation and is not smuggled into the definition. -/
def veluFiveMap :
    curve.toAffine.Point →
      fiveIsogenousCurve.toAffine.Point
  | 0 => 0
  | .some x y hP =>
      if hx : x = 0 ∨ x = 1 then
        0
      else
        veluFivePoint (x := x) (y := y) hP
          (fun h ↦ hx (Or.inl h))
          (fun h ↦ hx (Or.inr h))

/-- The affine zero fiber of the candidate Vélu map is exactly the
four nonzero points with abscissa `0` or `1`. -/
theorem veluFiveMap_some_eq_zero_iff
    {x y : ℚ}
    (hP : curve.toAffine.Nonsingular x y) :
    veluFiveMap (.some x y hP) = 0 ↔
      x = 0 ∨ x = 1 := by
  by_cases hx : x = 0 ∨ x = 1
  · simp [veluFiveMap, hx]
  · simp [veluFiveMap, hx, veluFivePoint]

/-- Miller's degree-five function attached to the kernel generator.
On the smooth projective curve its divisor is
`5(P00) - 5(O)`; the displayed formula is the input for the Kummer
map in a five-isogeny descent. -/
def fiveKummerFunction (x y : ℚ) : ℚ :=
  y ^ 2 * (y + x) / (x - 1) ^ 2

/-- The subgroup of rational points killed by five. -/
abbrev FiveTorsion :=
  (nsmulAddMonoidHom
    (α := curve.toAffine.Point) 5).ker

/-- Restriction of reduction modulo three to rational five-torsion. -/
noncomputable def fiveTorsionReduction :
    FiveTorsion →
      (redCurve (intPrime 3) integralCurve).Point :=
  fun P ↦ redHom (intPrime 3) map_integralCurve P

/-- Good reduction at three is injective on rational five-torsion. -/
theorem fiveTorsionReduction_injective :
    Function.Injective fiveTorsionReduction := by
  intro P Q hPQ
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero
    (intPrime 3) map_integralCurve
    (by norm_num) three_mem_prime
    three_not_mem_prime_pow_two
  · apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨5, by norm_num, ?_⟩
    have hP :
        (5 : ℕ) • (P : curve.toAffine.Point) = 0 :=
      AddMonoidHom.mem_ker.mp P.property
    have hQ :
        (5 : ℕ) • (Q : curve.toAffine.Point) = 0 :=
      AddMonoidHom.mem_ker.mp Q.property
    rw [nsmul_sub, hP, hQ, sub_zero]
  · change
      redHom (intPrime 3) map_integralCurve
          ((P : curve.toAffine.Point) - Q) = 0
    change
      redHom (intPrime 3) map_integralCurve
          (P : curve.toAffine.Point) =
        redHom (intPrime 3) map_integralCurve
          (Q : curve.toAffine.Point) at hPQ
    rw [map_sub, hPQ, sub_self]

noncomputable instance :
    Finite FiveTorsion :=
  Finite.of_injective fiveTorsionReduction
    fiveTorsionReduction_injective

/-- There are at most five rational points killed by five. -/
theorem five_torsion_card_le_five :
    Nat.card FiveTorsion ≤ 5 := by
  calc
    Nat.card FiveTorsion ≤
        Nat.card
          (redCurve (intPrime 3) integralCurve).Point :=
      Nat.card_le_card_of_injective
        fiveTorsionReduction
        fiveTorsionReduction_injective
    _ = 5 := card_reducedCurve

/-- The five multiples of `(0,0)`, regarded as points killed by five. -/
def visibleFiveTorsion (i : Fin 5) :
    FiveTorsion :=
  ⟨i.val • P00, by
    apply AddMonoidHom.mem_ker.mpr
    change (5 : ℕ) • (i.val • P00) = 0
    calc
      (5 : ℕ) • (i.val • P00) =
          i.val • ((5 : ℕ) • P00) := by
        rw [← mul_nsmul, ← mul_nsmul,
          Nat.mul_comm]
      _ = 0 := by rw [five_P00, nsmul_zero]⟩

theorem visibleFiveTorsion_injective :
    Function.Injective visibleFiveTorsion := by
  intro i j hij
  have hval :
      i.val • P00 = j.val • P00 :=
    congrArg Subtype.val hij
  have hfin : IsOfFinAddOrder P00 :=
    addOrderOf_pos_iff.mp (by
      rw [addOrderOf_P00]
      norm_num)
  have hmod :
      i.val ≡ j.val [MOD addOrderOf P00] :=
    hfin.nsmul_eq_nsmul_iff_modEq.mp hval
  rw [addOrderOf_P00] at hmod
  exact Fin.ext
    (hmod.eq_of_lt_of_lt i.isLt j.isLt)

/-- The rational five-torsion subgroup consists of exactly the five
multiples of `(0,0)`. -/
theorem five_torsion_card_eq_five :
    Nat.card FiveTorsion = 5 := by
  apply le_antisymm five_torsion_card_le_five
  simpa using
    Nat.card_le_card_of_injective
      visibleFiveTorsion visibleFiveTorsion_injective

/-- Every rational point killed by five is one of the five multiples
of `(0,0)`. -/
theorem visibleFiveTorsion_bijective :
    Function.Bijective visibleFiveTorsion :=
  visibleFiveTorsion_injective.bijective_of_nat_card_le
    (by simpa using five_torsion_card_le_five)

/-- The five proposed representatives for
`E(ℚ) / 5 E(ℚ)`. -/
def fiveRepresentative (i : Fin 5) :
    curve.toAffine.Point :=
  i.val • P00

/-- The exact arithmetic output required from a five-isogeny descent:
every rational point differs from one of the five visible torsion points
by a multiple of five.

This is deliberately a proposition rather than a class or a hidden
assumption.  A future Selmer computation can prove it and feed the
theorem below. -/
def FiveCosetBound : Prop :=
  ∀ P : curve.toAffine.Point,
    ∃ i : Fin 5, ∃ Q : curve.toAffine.Point,
      P = fiveRepresentative i + (5 : ℕ) • Q

/-- A five-coset bound gives a surjection onto the quotient by
multiplication by five. -/
theorem five_quotient_surjective
    (hcosets : FiveCosetBound) :
    Function.Surjective
      (fun i : Fin 5 ↦
        QuotientAddGroup.mk' fiveRange
          (fiveRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective fiveRange c
  obtain ⟨i, Q, hP⟩ := hcosets P
  refine
    ⟨i,
      (QuotientAddGroup.mk'_eq_mk'
        fiveRange).mpr ?_⟩
  refine
    ⟨(5 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
  exact hP.symm

/-- A five-coset bound makes multiplication by five have finite
index. -/
theorem five_finiteIndex_of_cosetBound
    (hcosets : FiveCosetBound) :
    fiveRange.FiniteIndex := by
  letI :
      Finite
        (curve.toAffine.Point ⧸ fiveRange) :=
    Finite.of_surjective _
      (five_quotient_surjective hcosets)
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- A five-coset bound implies finite generation by the explicit
five-fold height descent above. -/
theorem point_fg_of_cosetBound
    (hcosets : FiveCosetBound) :
    AddGroup.FG curve.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_five
    curve (five_finiteIndex_of_cosetBound hcosets)

/-- A five-coset bound gives the sharp index estimate
`[E(ℚ) : 5 E(ℚ)] ≤ 5`. -/
theorem five_index_le_five_of_cosetBound
    (hcosets : FiveCosetBound) :
    fiveRange.index ≤ 5 := by
  letI :
      Finite
        (curve.toAffine.Point ⧸ fiveRange) :=
    Finite.of_surjective _
      (five_quotient_surjective hcosets)
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      (five_quotient_surjective hcosets)).trans_eq
        (by simp)

/-- The five-coset output of a five-isogeny descent forces
Mordell--Weil rank zero. -/
theorem point_rank_zero_of_cosetBound
    (hcosets : FiveCosetBound) :
    Module.finrank ℤ curve.toAffine.Point = 0 := by
  letI : AddGroup.FG curve.toAffine.Point :=
    point_fg_of_cosetBound hcosets
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg
      curve.toAffine.Point
      (by norm_num : (5 : ℕ) ≠ 0)
  change
    fiveRange.index =
      5 ^ Module.finrank ℤ curve.toAffine.Point *
        Nat.card FiveTorsion at hformula
  rw [five_torsion_card_eq_five] at hformula
  have hindex :
      fiveRange.index ≤ 5 :=
    five_index_le_five_of_cosetBound hcosets
  have hpow :
      5 ^ Module.finrank ℤ curve.toAffine.Point ≤ 1 := by
    omega
  have hpowequal :
      5 ^ Module.finrank ℤ curve.toAffine.Point = 1 :=
    le_antisymm hpow
      (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- Once the five explicit cosets have been certified, every rational
point is torsion and the rational point group is finite. -/
theorem point_finite_of_cosetBound
    (hcosets : FiveCosetBound) :
    Finite curve.toAffine.Point := by
  letI : AddGroup.FG curve.toAffine.Point :=
    point_fg_of_cosetBound hcosets
  letI : Module.Finite ℤ curve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr
      (point_fg_of_cosetBound hcosets)
  have hmoduleTorsion :
      Module.IsTorsion ℤ curve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion
      (R := ℤ)).mp
        (point_rank_zero_of_cosetBound hcosets)
  exact
    AddCommGroup.finite_of_fg_torsion
      curve.toAffine.Point
      (AddMonoid.isTorsion_iff_isTorsion_int.mpr
        hmoduleTorsion)

/-- End-to-end consequence of the isolated five-descent boundary:
the rational point group has exactly five elements, and every affine
point has abscissa zero or one. -/
theorem five_point_classification_of_cosetBound
    (hcosets : FiveCosetBound) :
    Nat.card curve.toAffine.Point = 5 ∧
      ∀ {U V : ℚ},
        curve.toAffine.Nonsingular U V →
          U = 0 ∨ U = 1 :=
  finite_implies_five_point_classification
    (point_finite_of_cosetBound hcosets)

end MazurTorsion.XOneEleven
