/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuadraticNormBase
import MazurTorsion.NumberTheory.XOneEighteenCubeCorrespondence

/-!
# The Eisenstein-cube consumer of the `X₁(18)` quadratic norm data

This downstream module connects the surviving four-scalar Eisenstein-cube
correspondence to the anti-diagonal sextic and its primitive quadratic norm
datum.  The sextic, point transport, and norm arithmetic themselves live in
`XOneEighteenQuadraticNormBase`, below `XOneEighteenDescent` in the import
graph.
-/

namespace MazurTorsion.XOneEighteenDescent

open MazurTorsion.XOneEighteenFiniteField

/-- The cyclic-cubic invariant of an integral cube root is the ratio of
its two Eisenstein cube coordinates. -/
theorem invariantX_intRatio
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    invariantX ((x : ℚ) / (y : ℚ)) =
      3 * (eisensteinCubeReal x y : ℚ) /
        (eisensteinCubeEta x y : ℚ) := by
  have hxQ : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hxyQ : (x : ℚ) - (y : ℚ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hxy
  simp only [invariantX, eisensteinCubeReal, eisensteinCubeEta]
  push_cast
  field_simp [hxQ, hyQ, hxyQ]

/-- The four-scalar cube correspondence is exactly the rational
anti-diagonal relation between the two cyclic-cubic invariants. -/
theorem invariantX_relation_of_fourScalarCorrespondence
    {x y u v : ℤ}
    (hetaNonzero : eisensteinCubeEta x y ≠ 0)
    (hcorrespondence : FourScalarEisensteinCubeCorrespondence x y u v) :
    invariantX ((x : ℚ) / (y : ℚ)) =
      2 * invariantX ((u : ℚ) / (v : ℚ)) - 6 := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp [eisensteinCubeEta] at hetaNonzero
  have hxy : x ≠ y := by
    intro hxy
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hetaSecond : eisensteinCubeEta u v ≠ 0 := by
    rw [hcorrespondence.1]
    exact mul_ne_zero (by norm_num) hetaNonzero
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  have hv : v ≠ 0 := by
    intro hv
    subst v
    simp [eisensteinCubeEta] at hetaSecond
  have huv : u ≠ v := by
    intro huv
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  rw [invariantX_intRatio x y hx hy hxy,
    invariantX_intRatio u v hu hv huv]
  have hetaQ := congrArg (fun z : ℤ => (z : ℚ)) hcorrespondence.1
  have hrealQ := congrArg (fun z : ℤ => (z : ℚ)) hcorrespondence.2
  norm_num at hetaQ hrealQ
  rw [hetaQ, hrealQ]
  have hetaNonzeroQ : (eisensteinCubeEta x y : ℚ) ≠ 0 := by
    exact_mod_cast hetaNonzero
  field_simp [hetaNonzeroQ]
  ring

/-- The quotient curve is a genuine consumer of the surviving four-scalar
cube correspondence. -/
theorem antiDiagonalZ_sq_of_fourScalarCorrespondence
    {x y u v : ℤ}
    (hetaNonzero : eisensteinCubeEta x y ≠ 0)
    (hcorrespondence : FourScalarEisensteinCubeCorrespondence x y u v) :
    antiDiagonalZ ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ)) ^ 2 =
      antiDiagonalSextic
        (antiDiagonalW ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ))) := by
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hy : y ≠ 0 := by
    intro hy
    subst y
    simp [eisensteinCubeEta] at hetaNonzero
  have hxy : x ≠ y := by
    intro hxy
    subst x
    simp [eisensteinCubeEta] at hetaNonzero
  have hetaSecond : eisensteinCubeEta u v ≠ 0 := by
    rw [hcorrespondence.1]
    exact mul_ne_zero (by norm_num) hetaNonzero
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  have hv : v ≠ 0 := by
    intro hv
    subst v
    simp [eisensteinCubeEta] at hetaSecond
  have huv : u ≠ v := by
    intro huv
    subst u
    simp [eisensteinCubeEta] at hetaSecond
  have hp0 : (x : ℚ) / (y : ℚ) ≠ 0 := div_ne_zero
    (by exact_mod_cast hx) (by exact_mod_cast hy)
  have hp1 : (x : ℚ) / (y : ℚ) ≠ 1 := by
    intro hp
    have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
    have hcast : (x : ℚ) = (y : ℚ) :=
      (div_eq_one_iff_eq hyQ).mp hp
    exact hxy (by exact_mod_cast hcast)
  have hq0 : (u : ℚ) / (v : ℚ) ≠ 0 := div_ne_zero
    (by exact_mod_cast hu) (by exact_mod_cast hv)
  have hq1 : (u : ℚ) / (v : ℚ) ≠ 1 := by
    intro hq
    have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv
    have hcast : (u : ℚ) = (v : ℚ) :=
      (div_eq_one_iff_eq hvQ).mp hq
    exact huv (by exact_mod_cast hcast)
  have hrelation := invariantX_relation_of_fourScalarCorrespondence
    hetaNonzero hcorrespondence
  have hden := antiDiagonalDen_ne_zero_of_invariantX_relation
    ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ))
    hp0 hp1 hq0 hq1 hrelation
  exact antiDiagonalZ_sq
    ((x : ℚ) / (y : ℚ)) ((u : ℚ) / (v : ℚ))
    hp0 hp1 hq0 hq1 hden hrelation

/-- The primitive quadratic norm datum is the final checked consumer of
the surviving four-scalar cube correspondence. -/
theorem exists_primitive_quadraticNormDatum_of_fourScalarCorrespondence
    {x y u v : ℤ}
    (hetaNonzero : eisensteinCubeEta x y ≠ 0)
    (hcorrespondence : FourScalarEisensteinCubeCorrespondence x y u v) :
    ∃ r s c : ℤ,
      0 < s ∧
      IsCoprime r s ∧
      antiDiagonalW ((x : ℚ) / (y : ℚ))
          ((u : ℚ) / (v : ℚ)) = (r : ℚ) / (s : ℚ) ∧
      c ^ 2 = antiDiagonalSexticHom r s ∧
      antiDiagonalNormReal r s ^ 2 +
            2 * antiDiagonalNormSqrtNegTwo r s ^ 2 = c ^ 2 ∧
        ((GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 1 ∨
          (GCDMonoid.gcd (antiDiagonalNormReal r s)
              (antiDiagonalNormSqrtNegTwo r s) : ℤ) = 8) := by
  have hcurve := antiDiagonalZ_sq_of_fourScalarCorrespondence
    hetaNonzero hcorrespondence
  exact exists_primitive_quadraticNormDatum_of_antiDiagonal_point hcurve

end MazurTorsion.XOneEighteenDescent
