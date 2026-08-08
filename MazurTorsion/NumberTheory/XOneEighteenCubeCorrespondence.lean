/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenEisensteinAllocation

/-!
# The final normalized cubic correspondence for `X₁(18)`

The two surviving Eisenstein cube systems reduce to one correspondence.
This file uses its order-three deck action to put the unique distinguished
prime factor into the second coordinate of each cube root.  Dividing those
coordinates by seven leaves one explicit pair of integral cubic equations.
-/

namespace MazurTorsion.XOneEighteenDescent

/-- Multiplication of an Eisenstein cube root by `ζ₃`. -/
def eisensteinCubeDeck (x y : ℤ) : ℤ × ℤ :=
  (-y, x - y)

/-- The deck transformation preserves the real coordinate of the cube. -/
theorem eisensteinCubeDeck_real (x y : ℤ) :
    eisensteinCubeReal (eisensteinCubeDeck x y).1
        (eisensteinCubeDeck x y).2 =
      eisensteinCubeReal x y := by
  simp only [eisensteinCubeDeck, eisensteinCubeReal]
  ring

/-- The deck transformation preserves the `ζ₃` coordinate of the cube. -/
theorem eisensteinCubeDeck_eta (x y : ℤ) :
    eisensteinCubeEta (eisensteinCubeDeck x y).1
        (eisensteinCubeDeck x y).2 =
      eisensteinCubeEta x y := by
  simp only [eisensteinCubeDeck, eisensteinCubeEta]
  ring

/-- If seven divides the eta coordinate, a deck-equivalent cube root has
second coordinate divisible by seven. -/
theorem exists_seven_normalized_eisensteinCubeRoot
    {x y : ℤ} (hseven : (7 : ℤ) ∣ eisensteinCubeEta x y) :
    ∃ x' y' : ℤ,
      eisensteinCubeReal x' y' = eisensteinCubeReal x y ∧
      eisensteinCubeEta x' y' = eisensteinCubeEta x y ∧
      (7 : ℤ) ∣ y' := by
  have hprime : Prime (7 : ℤ) :=
    (Int.prime_iff_natAbs_prime).2 (by decide)
  have hproduct : (7 : ℤ) ∣ x * y * (x - y) := by
    have hscaled : (7 : ℤ) ∣ 3 * (x * y * (x - y)) := by
      simpa only [eisensteinCubeEta] using hseven
    rcases hprime.dvd_mul.mp hscaled with hthree | hproduct
    · norm_num at hthree
    · exact hproduct
  rcases hprime.dvd_mul.mp hproduct with hxy | hdiff
  · rcases hprime.dvd_mul.mp hxy with hx | hy
    · refine ⟨y - x, -x, ?_, ?_, dvd_neg.mpr hx⟩
      · simp only [eisensteinCubeReal]
        ring
      · simp only [eisensteinCubeEta]
        ring
    · exact ⟨x, y, rfl, rfl, hy⟩
  · refine ⟨-y, x - y, ?_, ?_, hdiff⟩
    · exact eisensteinCubeDeck_real x y
    · exact eisensteinCubeDeck_eta x y

/-- The distinguished-seven affine chart of the surviving cubic
correspondence, after writing the second root coordinates as `7s` and
`7t`. -/
def SevenScaledFourScalarEisensteinCubeSystem
    (x s u t : ℤ) : Prop :=
  u * t * (u - 7 * t) = 2 * (x * s * (x - 7 * s)) ∧
    u ^ 3 - 147 * u * t ^ 2 + 343 * t ^ 3 =
      x ^ 3 + 42 * x ^ 2 * s - 441 * x * s ^ 2 + 343 * s ^ 3

/-- The scaled integer equations are exactly the four-scalar cube
correspondence on the distinguished-seven chart. -/
theorem sevenScaled_iff_fourScalarEisensteinCubeCorrespondence
    (x s u t : ℤ) :
    SevenScaledFourScalarEisensteinCubeSystem x s u t ↔
      FourScalarEisensteinCubeCorrespondence x (7 * s) u (7 * t) := by
  simp only [SevenScaledFourScalarEisensteinCubeSystem,
    FourScalarEisensteinCubeCorrespondence,
    eisensteinCubeReal, eisensteinCubeEta]
  constructor
  · rintro ⟨heta, hreal⟩
    constructor
    · linear_combination 21 * heta
    · linear_combination hreal
  · rintro ⟨heta, hreal⟩
    constructor
    · apply mul_left_cancel₀ (by norm_num : (21 : ℤ) ≠ 0)
      linear_combination heta
    · linear_combination hreal

/-- The final explicit global arithmetic boundary: every primitive integral
point on the seven-scaled cubic system lies on one of its three cusp lines. -/
def SevenScaledFourScalarEisensteinCubeDegeneracy : Prop :=
  ∀ x s u t : ℤ,
    IsCoprime (eisensteinCubeReal x (7 * s))
      (eisensteinCubeEta x (7 * s)) →
    IsCoprime (eisensteinCubeReal u (7 * t))
      (eisensteinCubeEta u (7 * t)) →
    SevenScaledFourScalarEisensteinCubeSystem x s u t →
    x * s * (x - 7 * s) = 0

/-- Degeneracy on the distinguished-seven chart proves degeneracy of the
primitive cubic correspondence. -/
theorem primitiveFourScalarDegeneracy_of_sevenScaled
    (hscaled : SevenScaledFourScalarEisensteinCubeDegeneracy) :
    PrimitiveFourScalarEisensteinCubeDegeneracy := by
  intro x y u v hcoprimeFirst hcoprimeSecond hfortyTwo hrelation
  have hsevenFirst : (7 : ℤ) ∣ eisensteinCubeEta x y :=
    dvd_trans (by norm_num : (7 : ℤ) ∣ 42) hfortyTwo
  have hsevenSecond : (7 : ℤ) ∣ eisensteinCubeEta u v := by
    obtain ⟨q, hq⟩ := hsevenFirst
    obtain ⟨heta, _hreal⟩ := hrelation
    refine ⟨2 * q, ?_⟩
    rw [heta, hq]
    ring
  obtain ⟨x', y', hrealFirst, hetaFirst, hsevenY⟩ :=
    exists_seven_normalized_eisensteinCubeRoot hsevenFirst
  obtain ⟨u', v', hrealSecond, hetaSecond, hsevenV⟩ :=
    exists_seven_normalized_eisensteinCubeRoot hsevenSecond
  obtain ⟨s, hs⟩ := hsevenY
  obtain ⟨t, ht⟩ := hsevenV
  have hcoprimeFirst' :
      IsCoprime (eisensteinCubeReal x' (7 * s))
        (eisensteinCubeEta x' (7 * s)) := by
    rw [← hs, hrealFirst, hetaFirst]
    exact hcoprimeFirst
  have hcoprimeSecond' :
      IsCoprime (eisensteinCubeReal u' (7 * t))
        (eisensteinCubeEta u' (7 * t)) := by
    rw [← ht, hrealSecond, hetaSecond]
    exact hcoprimeSecond
  have hrelation' :
      FourScalarEisensteinCubeCorrespondence
        x' (7 * s) u' (7 * t) := by
    obtain ⟨heta, hreal⟩ := hrelation
    constructor
    · rw [← ht, hetaSecond, ← hs, hetaFirst]
      exact heta
    · rw [← ht, hrealSecond, ← hs, hrealFirst, hetaFirst]
      exact hreal
  have hsystem :=
    (sevenScaled_iff_fourScalarEisensteinCubeCorrespondence x' s u' t).mpr
      hrelation'
  have hzero := hscaled x' s u' t hcoprimeFirst'
    hcoprimeSecond' hsystem
  rw [← hetaFirst, hs]
  simp only [eisensteinCubeEta]
  linear_combination 21 * hzero

/-- The seven-scaled cubic degeneracy has a checked exact-order-eighteen
consumer. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_sevenScaledCubeDegeneracy
    (hscaled : SevenScaledFourScalarEisensteinCubeDegeneracy)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 :=
  rationalPoint_addOrderOf_ne_eighteen_of_primitiveFourScalarDegeneracy
    (primitiveFourScalarDegeneracy_of_sevenScaled hscaled) E Q

end MazurTorsion.XOneEighteenDescent
