/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassInfinityPairNeighborhoodAddition

/-!
# The addition formula near the infinity diagonal

On the checked principal neighborhood `D(B∞)` of the infinity-by-infinity
chart, the regular slope determines a line

`z = ℓ x + c`.

Writing the cubic obtained by substituting this line as

`-D x³ + E x² + F x + G`,

the denominator-free third intersection is `[N : D : M]`, where
`N = E - D (x₁ + x₂)` and `M = ℓ N + c D`.  Negating that third
intersection gives the addition triple

`[N : -D - a₁ N - a₃ M : M]`.

The proof below does not divide by `x₁ - x₂` or by `D`.  It uses both the
line equation and the checked divided-difference tangent relation, so the
same formula remains valid on the diagonal at infinity.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The Weierstrass curve after scalar extension to the infinity-pair
neighborhood. -/
abbrev projectiveInfinityPairNeighborhoodMappedCurve
    (W : WeierstrassCurve K) :=
  W.map (algebraMap K (projectiveInfinityPairNeighborhoodRing W))

/-- First `X / Y` coordinate on the infinity-pair neighborhood. -/
def projectiveInfinityPairNeighborhoodX₁ (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  algebraMap (projectiveInfinityPairCoordinateRing W)
    (projectiveInfinityPairNeighborhoodRing W)
    (projectiveInfinityPairX₁ W)

/-- First `Z / Y` coordinate on the infinity-pair neighborhood. -/
def projectiveInfinityPairNeighborhoodZ₁ (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  algebraMap (projectiveInfinityPairCoordinateRing W)
    (projectiveInfinityPairNeighborhoodRing W)
    (projectiveInfinityPairZ₁ W)

/-- Second `X / Y` coordinate on the infinity-pair neighborhood. -/
def projectiveInfinityPairNeighborhoodX₂ (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  algebraMap (projectiveInfinityPairCoordinateRing W)
    (projectiveInfinityPairNeighborhoodRing W)
    (projectiveInfinityPairX₂ W)

/-- Second `Z / Y` coordinate on the infinity-pair neighborhood. -/
def projectiveInfinityPairNeighborhoodZ₂ (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  algebraMap (projectiveInfinityPairCoordinateRing W)
    (projectiveInfinityPairNeighborhoodRing W)
    (projectiveInfinityPairZ₂ W)

/-- Intercept of the regular line through the two universal inputs. -/
def projectiveInfinityPairNeighborhoodIntercept (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  projectiveInfinityPairNeighborhoodZ₁ W -
    projectiveInfinityPairNeighborhoodSlope W *
      projectiveInfinityPairNeighborhoodX₁ W

/-- Negative leading coefficient, up to sign, after substituting the regular
line into the infinity-chart cubic. -/
def projectiveInfinityPairNeighborhoodThirdD (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  let W' := projectiveInfinityPairNeighborhoodMappedCurve W
  let ℓ := projectiveInfinityPairNeighborhoodSlope W
  1 + W'.a₂ * ℓ + W'.a₄ * ℓ ^ 2 + W'.a₆ * ℓ ^ 3

/-- Quadratic coefficient after substituting the regular line into the
infinity-chart cubic. -/
def projectiveInfinityPairNeighborhoodThirdE (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  let W' := projectiveInfinityPairNeighborhoodMappedCurve W
  let ℓ := projectiveInfinityPairNeighborhoodSlope W
  let c := projectiveInfinityPairNeighborhoodIntercept W
  W'.a₁ * ℓ - W'.a₂ * c + W'.a₃ * ℓ ^ 2 -
    2 * W'.a₄ * c * ℓ - 3 * W'.a₆ * c * ℓ ^ 2

/-- Homogeneous `X` coordinate of the third line-cubic intersection. -/
def projectiveInfinityPairNeighborhoodThirdN (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  projectiveInfinityPairNeighborhoodThirdE W -
    projectiveInfinityPairNeighborhoodThirdD W *
      (projectiveInfinityPairNeighborhoodX₁ W +
        projectiveInfinityPairNeighborhoodX₂ W)

/-- Homogeneous `Z` coordinate of the third line-cubic intersection. -/
def projectiveInfinityPairNeighborhoodThirdM (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W :=
  projectiveInfinityPairNeighborhoodSlope W *
      projectiveInfinityPairNeighborhoodThirdN W +
    projectiveInfinityPairNeighborhoodIntercept W *
      projectiveInfinityPairNeighborhoodThirdD W

/-- The denominator-free third intersection of the regular line with the
projective cubic. -/
def projectiveInfinityPairNeighborhoodThirdCoordinates
    (W : WeierstrassCurve K) :
    Fin 3 → projectiveInfinityPairNeighborhoodRing W :=
  ![projectiveInfinityPairNeighborhoodThirdN W,
    projectiveInfinityPairNeighborhoodThirdD W,
    projectiveInfinityPairNeighborhoodThirdM W]

/-- Negation of the third intersection, hence the local addition triple. -/
def projectiveInfinityPairNeighborhoodAdditionCoordinates
    (W : WeierstrassCurve K) :
    Fin 3 → projectiveInfinityPairNeighborhoodRing W :=
  let W' := projectiveInfinityPairNeighborhoodMappedCurve W
  ![projectiveInfinityPairNeighborhoodThirdN W,
    -projectiveInfinityPairNeighborhoodThirdD W -
      W'.a₁ * projectiveInfinityPairNeighborhoodThirdN W -
      W'.a₃ * projectiveInfinityPairNeighborhoodThirdM W,
    projectiveInfinityPairNeighborhoodThirdM W]

private lemma infinityChart_thirdIntersection_equation
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (x₁ z₁ x₂ z₂ ℓ c D E N M : R)
    (h₁ : W.toProjective.Equation ![x₁, 1, z₁])
    (hline : ℓ * (x₁ - x₂) = z₁ - z₂)
    (hslope : ℓ *
        (1 + W.a₁ * x₁ + W.a₃ * (z₁ + z₂) - W.a₂ * x₁ ^ 2 -
          W.a₄ * x₁ * (z₁ + z₂) -
          W.a₆ * (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2)) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * z₂ * (x₁ + x₂) +
        W.a₄ * z₂ ^ 2 - W.a₁ * z₂)
    (hc : c = z₁ - ℓ * x₁)
    (hD : D = 1 + W.a₂ * ℓ + W.a₄ * ℓ ^ 2 + W.a₆ * ℓ ^ 3)
    (hE : E = W.a₁ * ℓ - W.a₂ * c + W.a₃ * ℓ ^ 2 -
      2 * W.a₄ * c * ℓ - 3 * W.a₆ * c * ℓ ^ 2)
    (hN : N = E - D * (x₁ + x₂))
    (hM : M = ℓ * N + c * D) :
    W.toProjective.Equation ![N, D, M] := by
  have hz₁ : z₁ = ℓ * x₁ + c := by
    linear_combination -hc
  have hz₂ : z₂ = ℓ * x₂ + c := by
    linear_combination hline - hc
  rw [WeierstrassCurve.Projective.equation_iff] at h₁ ⊢
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, one_pow, one_mul, mul_one] at h₁
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [hz₁, hz₂] at h₁ hslope
  have hF :
      ℓ + W.a₁ * c + 2 * W.a₃ * c * ℓ - W.a₄ * c ^ 2 -
          3 * W.a₆ * c ^ 2 * ℓ =
        -(N * (x₁ + x₂) + D * x₁ * x₂) := by
    rw [hN, hE, hD]
    linear_combination hslope
  have hG : c + W.a₃ * c ^ 2 - W.a₆ * c ^ 3 = N * x₁ * x₂ := by
    have hE' : E = N + D * (x₁ + x₂) := by
      linear_combination -hN
    have hg₁ :
        -D * x₁ ^ 3 + E * x₁ ^ 2 +
            (ℓ + W.a₁ * c + 2 * W.a₃ * c * ℓ - W.a₄ * c ^ 2 -
              3 * W.a₆ * c ^ 2 * ℓ) * x₁ +
            (c + W.a₃ * c ^ 2 - W.a₆ * c ^ 3) = 0 := by
      rw [hD, hE]
      linear_combination h₁
    linear_combination hg₁ - x₁ * hF - x₁ ^ 2 * hE'
  have hE' : E = N + D * (x₁ + x₂) := by
    linear_combination -hN
  have hthird :
      -D * N ^ 3 + E * N ^ 2 * D +
          (ℓ + W.a₁ * c + 2 * W.a₃ * c * ℓ - W.a₄ * c ^ 2 -
            3 * W.a₆ * c ^ 2 * ℓ) * N * D ^ 2 +
          (c + W.a₃ * c ^ 2 - W.a₆ * c ^ 3) * D ^ 3 = 0 := by
    linear_combination
      N ^ 2 * D * hE' + N * D ^ 2 * hF + D ^ 3 * hG
  rw [hD, hE] at hthird
  rw [hM, hD]
  linear_combination hthird

private lemma projectiveEquation_negate_thirdIntersection
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) (X Y Z : R)
    (h : W.toProjective.Equation ![X, Y, Z]) :
    W.toProjective.Equation ![X, -Y - W.a₁ * X - W.a₃ * Z, Z] := by
  rw [WeierstrassCurve.Projective.equation_iff] at h ⊢
  simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h ⊢
  linear_combination h

private theorem projectiveInfinityPairNeighborhood_firstEquation
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairNeighborhoodMappedCurve W).toProjective.Equation
      ![projectiveInfinityPairNeighborhoodX₁ W, 1,
        projectiveInfinityPairNeighborhoodZ₁ W] := by
  let R := projectiveInfinityPairCoordinateRing W
  let S := projectiveInfinityPairNeighborhoodRing W
  let f : R →+* S := algebraMap R S
  have h := (projectivePairChartFirstUniversalPoint_equation
    W (false, false)).map f
  have hf : f.comp (algebraMap K R) = algebraMap K S :=
    (IsScalarTower.algebraMap_eq K R S).symm
  change ((W.map (algebraMap K R)).map f).toProjective.Equation
    (f ∘ projectivePairChartFirstUniversalPoint W (false, false)) at h
  rw [WeierstrassCurve.map_map, hf] at h
  have hp : f ∘ projectivePairChartFirstUniversalPoint W (false, false) =
      ![projectiveInfinityPairNeighborhoodX₁ W, 1,
        projectiveInfinityPairNeighborhoodZ₁ W] := by
    funext j
    fin_cases j
    · rfl
    · change f (projectivePairChartFirstUniversalPoint W (false, false)
          (coveringCoordinate false)) = 1
      rw [projectivePairChartFirstUniversalPoint_normalized, map_one]
    · rfl
  rw [hp] at h
  exact h

private theorem projectiveInfinityPairNeighborhoodB12_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodB12 W =
      let W' := projectiveInfinityPairNeighborhoodMappedCurve W
      1 + W'.a₁ * projectiveInfinityPairNeighborhoodX₁ W +
        W'.a₃ * (projectiveInfinityPairNeighborhoodZ₁ W +
          projectiveInfinityPairNeighborhoodZ₂ W) -
        W'.a₂ * projectiveInfinityPairNeighborhoodX₁ W ^ 2 -
        W'.a₄ * projectiveInfinityPairNeighborhoodX₁ W *
          (projectiveInfinityPairNeighborhoodZ₁ W +
            projectiveInfinityPairNeighborhoodZ₂ W) -
        W'.a₆ * (projectiveInfinityPairNeighborhoodZ₁ W ^ 2 +
          projectiveInfinityPairNeighborhoodZ₁ W *
            projectiveInfinityPairNeighborhoodZ₂ W +
          projectiveInfinityPairNeighborhoodZ₂ W ^ 2) := by
  let R := projectiveInfinityPairCoordinateRing W
  let S := projectiveInfinityPairNeighborhoodRing W
  let f : R →+* S := algebraMap R S
  have hcoefficient (a : K) : f (algebraMap K R a) = algebraMap K S a :=
    IsScalarTower.algebraMap_apply K R S a
  dsimp only [f, R, S] at hcoefficient
  simp only [projectiveInfinityPairNeighborhoodB12,
    projectiveInfinityPairAdditionB12, projectivePairChartMappedCurve,
    projectiveInfinityPairNeighborhoodMappedCurve,
    projectiveInfinityPairNeighborhoodX₁,
    projectiveInfinityPairNeighborhoodZ₁,
    projectiveInfinityPairNeighborhoodZ₂, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_sub,
    map_mul, map_pow, map_one]
  simp only [hcoefficient]

private theorem projectiveInfinityPairNeighborhoodA12_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodA12 W =
      let W' := projectiveInfinityPairNeighborhoodMappedCurve W
      projectiveInfinityPairNeighborhoodX₁ W ^ 2 +
        projectiveInfinityPairNeighborhoodX₁ W *
          projectiveInfinityPairNeighborhoodX₂ W +
        projectiveInfinityPairNeighborhoodX₂ W ^ 2 +
        W'.a₂ * projectiveInfinityPairNeighborhoodZ₂ W *
          (projectiveInfinityPairNeighborhoodX₁ W +
            projectiveInfinityPairNeighborhoodX₂ W) +
        W'.a₄ * projectiveInfinityPairNeighborhoodZ₂ W ^ 2 -
        W'.a₁ * projectiveInfinityPairNeighborhoodZ₂ W := by
  let R := projectiveInfinityPairCoordinateRing W
  let S := projectiveInfinityPairNeighborhoodRing W
  let f : R →+* S := algebraMap R S
  have hcoefficient (a : K) : f (algebraMap K R a) = algebraMap K S a :=
    IsScalarTower.algebraMap_apply K R S a
  dsimp only [f, R, S] at hcoefficient
  simp only [projectiveInfinityPairNeighborhoodA12,
    projectiveInfinityPairAdditionA12, projectivePairChartMappedCurve,
    projectiveInfinityPairNeighborhoodMappedCurve,
    projectiveInfinityPairNeighborhoodX₁,
    projectiveInfinityPairNeighborhoodX₂,
    projectiveInfinityPairNeighborhoodZ₂, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, map_add, map_sub,
    map_mul, map_pow]
  simp only [hcoefficient]

/-- The denominator-free third-intersection triple lies on the mapped
projective cubic throughout `D(B∞)`, including on the diagonal. -/
theorem projectiveInfinityPairNeighborhoodThirdCoordinates_equation
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairNeighborhoodMappedCurve W).toProjective.Equation
      (projectiveInfinityPairNeighborhoodThirdCoordinates W) := by
  apply infinityChart_thirdIntersection_equation
  · exact projectiveInfinityPairNeighborhood_firstEquation W
  · simpa [projectiveInfinityPairNeighborhoodX₁,
      projectiveInfinityPairNeighborhoodX₂,
      projectiveInfinityPairNeighborhoodZ₁,
      projectiveInfinityPairNeighborhoodZ₂] using
        projectiveInfinityPairNeighborhoodSlope_mul_sub W
  · have h := projectiveInfinityPairNeighborhoodSlope_mul_B12 W
    rw [projectiveInfinityPairNeighborhoodB12_eq,
      projectiveInfinityPairNeighborhoodA12_eq] at h
    exact h
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The local addition triple is an actual homogeneous solution of the mapped
Weierstrass equation on the infinity-diagonal neighborhood. -/
theorem projectiveInfinityPairNeighborhoodAdditionCoordinates_equation
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairNeighborhoodMappedCurve W).toProjective.Equation
      (projectiveInfinityPairNeighborhoodAdditionCoordinates W) := by
  apply projectiveEquation_negate_thirdIntersection
  simpa [projectiveInfinityPairNeighborhoodThirdCoordinates] using
    projectiveInfinityPairNeighborhoodThirdCoordinates_equation W

/-! ## Specialization at the infinity point -/

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_X₁
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodX₁ W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodX₁,
    projectiveInfinityPairOriginAlgHom]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_Z₁
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodZ₁ W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodZ₁,
    projectiveInfinityPairOriginAlgHom]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_X₂
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodX₂ W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodX₂,
    projectiveInfinityPairOriginAlgHom]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_Z₂
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodZ₂ W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodZ₂,
    projectiveInfinityPairOriginAlgHom]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_intercept
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodIntercept W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodIntercept]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_thirdD
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodThirdD W) = 1 := by
  simp [projectiveInfinityPairNeighborhoodThirdD]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_thirdE
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodThirdE W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodThirdE]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_thirdN
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodThirdN W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodThirdN]

@[simp]
theorem projectiveInfinityPairNeighborhoodOriginAlgHom_thirdM
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W
        (projectiveInfinityPairNeighborhoodThirdM W) = 0 := by
  simp [projectiveInfinityPairNeighborhoodThirdM]

/-- At `(O, O)`, the local addition triple is `[0 : -1 : 0]`, the same
projective point as the identity `[0 : 1 : 0]`. -/
theorem projectiveInfinityPairNeighborhoodAdditionCoordinates_at_origin
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodOriginAlgHom W ∘
        projectiveInfinityPairNeighborhoodAdditionCoordinates W =
      ![0, -1, 0] := by
  funext j
  fin_cases j <;>
    simp [projectiveInfinityPairNeighborhoodAdditionCoordinates]

/-! ## An actual addition morphism around `(O, O)` -/

/-- Further localize at the `Y` coordinate of the addition triple.  This
selected output chart contains `(O, O)` because that coordinate is `-1`
there. -/
abbrev projectiveInfinityPairNeighborhoodAdditionOutputRing
    (W : WeierstrassCurve K) :=
  Localization.Away
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W (1 : Fin 3))

/-- The selected addition-output coordinate as a unit in its principal
localization. -/
noncomputable def projectiveInfinityPairNeighborhoodAdditionOutputUnit
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairNeighborhoodAdditionOutputRing W)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W
      (1 : Fin 3))).unit

/-- The local addition triple, pulled to the output principal open and
normalized to have `Y = 1`. -/
noncomputable def projectiveInfinityPairNeighborhoodAdditionOutputPoint
    (W : WeierstrassCurve K) :
    Fin 3 → projectiveInfinityPairNeighborhoodAdditionOutputRing W :=
  fun j ↦
    ↑(projectiveInfinityPairNeighborhoodAdditionOutputUnit W)⁻¹ *
      algebraMap (projectiveInfinityPairNeighborhoodRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (projectiveInfinityPairNeighborhoodAdditionCoordinates W j)

@[simp]
theorem projectiveInfinityPairNeighborhoodAdditionOutputPoint_normalized
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodAdditionOutputPoint W
        (coveringCoordinate false) = 1 := by
  change (↑(projectiveInfinityPairNeighborhoodAdditionOutputUnit W)⁻¹ :
      projectiveInfinityPairNeighborhoodAdditionOutputRing W) *
      algebraMap (projectiveInfinityPairNeighborhoodRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (1 : Fin 3)) = 1
  rw [← (IsLocalization.Away.algebraMap_isUnit
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W
      (1 : Fin 3))).unit_spec]
  exact Units.inv_mul _

/-- The normalized local addition point still satisfies the cubic equation
after restriction to its `Y`-output principal open. -/
theorem projectiveInfinityPairNeighborhoodAdditionOutputPoint_equation
    (W : WeierstrassCurve K) :
    (W.map (algebraMap K
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W))).toProjective.Equation
        (projectiveInfinityPairNeighborhoodAdditionOutputPoint W) := by
  let R := projectiveInfinityPairNeighborhoodRing W
  let S := projectiveInfinityPairNeighborhoodAdditionOutputRing W
  let f : R →+* S := algebraMap R S
  have hmap :
      ((projectiveInfinityPairNeighborhoodMappedCurve W).map f).toProjective.Equation
        (f ∘ projectiveInfinityPairNeighborhoodAdditionCoordinates W) :=
    (projectiveInfinityPairNeighborhoodAdditionCoordinates_equation W).map f
  have hscaled :=
    (((projectiveInfinityPairNeighborhoodMappedCurve W).map f).toProjective.equation_smul
      (f ∘ projectiveInfinityPairNeighborhoodAdditionCoordinates W)
      (projectiveInfinityPairNeighborhoodAdditionOutputUnit W)⁻¹.isUnit).mpr hmap
  have hf : f.comp (algebraMap K R) = algebraMap K S :=
    (IsScalarTower.algebraMap_eq K R S).symm
  rw [projectiveInfinityPairNeighborhoodMappedCurve,
    WeierstrassCurve.map_map, hf] at hscaled
  have hp :
      (↑(projectiveInfinityPairNeighborhoodAdditionOutputUnit W)⁻¹ : S) •
          (f ∘ projectiveInfinityPairNeighborhoodAdditionCoordinates W) =
        projectiveInfinityPairNeighborhoodAdditionOutputPoint W := by
    funext j
    rfl
  rw [hp] at hscaled
  exact hscaled

/-- The normalized point induces a coordinate-ring map from the actual
infinity output chart. -/
noncomputable def projectiveInfinityPairNeighborhoodAdditionOutputAlgHom
    (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W false →ₐ[K]
      projectiveInfinityPairNeighborhoodAdditionOutputRing W :=
  coveringChartCoordinateRingAlgHomOfNormalizedPoint W false
    (projectiveInfinityPairNeighborhoodAdditionOutputPoint W)
    (projectiveInfinityPairNeighborhoodAdditionOutputPoint_equation W)
    (projectiveInfinityPairNeighborhoodAdditionOutputPoint_normalized W)

@[simp]
theorem projectiveInfinityPairNeighborhoodAdditionOutputAlgHom_ratio
    (W : WeierstrassCurve K) (j : Fin 3) :
    projectiveInfinityPairNeighborhoodAdditionOutputAlgHom W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (coveringCoordinate false) j)) =
      projectiveInfinityPairNeighborhoodAdditionOutputPoint W j := by
  exact coveringChartCoordinateRingAlgHomOfNormalizedPoint_ratio W false
    (projectiveInfinityPairNeighborhoodAdditionOutputPoint W)
    (projectiveInfinityPairNeighborhoodAdditionOutputPoint_equation W)
    (projectiveInfinityPairNeighborhoodAdditionOutputPoint_normalized W) j

/-- The first principal localization, viewed as an open of the
infinity-by-infinity projective-pair member. -/
noncomputable def projectiveInfinityPairNeighborhoodOpen
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairNeighborhoodRing W)) ⟶
      projectivePairChartScheme W (false, false) :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairNeighborhoodRing W))) ≫
    (projectivePairChartIsoSpecTensor W (false, false)).inv

instance projectiveInfinityPairNeighborhoodOpen_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectiveInfinityPairNeighborhoodOpen W) := by
  dsimp only [projectiveInfinityPairNeighborhoodOpen,
    projectiveInfinityPairNeighborhoodRing]
  infer_instance

/-- The selected output principal open inside the infinity-pair
neighborhood. -/
noncomputable def projectiveInfinityPairNeighborhoodAdditionOutputOpen
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairNeighborhoodAdditionOutputRing W)) ⟶
      Spec (.of (projectiveInfinityPairNeighborhoodRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (projectiveInfinityPairNeighborhoodRing W)
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W)))

instance projectiveInfinityPairNeighborhoodAdditionOutputOpen_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectiveInfinityPairNeighborhoodAdditionOutputOpen W) := by
  dsimp only [projectiveInfinityPairNeighborhoodAdditionOutputOpen,
    projectiveInfinityPairNeighborhoodAdditionOutputRing]
  infer_instance

/-- The actual source open around `(O, O)` inside the projective-pair chart. -/
noncomputable def projectiveInfinityPairOriginAdditionOpen
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairNeighborhoodAdditionOutputRing W)) ⟶
      projectivePairChartScheme W (false, false) :=
  projectiveInfinityPairNeighborhoodAdditionOutputOpen W ≫
    projectiveInfinityPairNeighborhoodOpen W

instance projectiveInfinityPairOriginAdditionOpen_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectiveInfinityPairOriginAdditionOpen W) := by
  dsimp only [projectiveInfinityPairOriginAdditionOpen]
  infer_instance

/-- Genuine addition morphism on the selected neighborhood of `(O, O)`. -/
noncomputable def projectiveInfinityPairOriginAdditionMorphism
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairNeighborhoodAdditionOutputRing W)) ⟶
      scheme W :=
  Spec.map (CommRingCat.ofHom
      (projectiveInfinityPairNeighborhoodAdditionOutputAlgHom W).toRingHom) ≫
    coveringChartMap W false

/-- The local addition morphism lies over the base field. -/
@[reassoc]
theorem projectiveInfinityPairOriginAdditionMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginAdditionMorphism W ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (algebraMap K
          (projectiveInfinityPairNeighborhoodAdditionOutputRing W))) := by
  rw [projectiveInfinityPairOriginAdditionMorphism, Category.assoc,
    coveringChartMap_comp_structureMap, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  ext a
  exact (projectiveInfinityPairNeighborhoodAdditionOutputAlgHom W).commutes a

/-- Evaluation at `(O, O)` extends through the output-coordinate
localization, proving that the actual source open above contains the missing
diagonal point. -/
noncomputable def projectiveInfinityPairOriginAdditionOriginAlgHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodAdditionOutputRing W →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W (1 : Fin 3))
    (f := projectiveInfinityPairNeighborhoodOriginAlgHom W) (by
      have h := congrFun
        (projectiveInfinityPairNeighborhoodAdditionCoordinates_at_origin W)
        (1 : Fin 3)
      change projectiveInfinityPairNeighborhoodOriginAlgHom W
          (projectiveInfinityPairNeighborhoodAdditionCoordinates W
            (1 : Fin 3)) = -1 at h
      rw [h]
      exact isUnit_neg_one)

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
