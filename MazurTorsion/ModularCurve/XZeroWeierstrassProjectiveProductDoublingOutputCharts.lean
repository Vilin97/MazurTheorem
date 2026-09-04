/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductOutputCharts

/-!
# Doubling output charts on the projective Weierstrass product

The raw secant triple vanishes when its two projective inputs coincide.  This
file regularizes the checked first-input doubling triple on the two principal
opens where its output `Y` or `Z` coordinate is invertible.  The normalized
point interface from the preceding file then supplies actual over-base
morphisms into the concrete projective cubic.

Proving that these doubling opens cover the secant base locus, and comparing
the resulting morphisms with the secant formulas on their intersections, are
the next gluing steps.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The coordinate ring obtained by inverting one selected output coordinate
of the first universal doubling triple. -/
abbrev projectivePairChartFirstDoublingOutputRing
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :=
  Localization.Away
    (projectivePairChartFirstDoublingCoordinates W ij
      (coveringCoordinate out))

/-- The selected doubling output coordinate as a unit in its principal
localization. -/
noncomputable def projectivePairChartFirstDoublingOutputUnit
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    (projectivePairChartFirstDoublingOutputRing W ij out)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (projectivePairChartFirstDoublingCoordinates W ij
      (coveringCoordinate out))).unit

/-- The first universal doubling triple, mapped to an output-coordinate
localization and normalized by the inverse of the selected coordinate. -/
noncomputable def projectivePairChartFirstDoublingOutputPoint
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    Fin 3 → projectivePairChartFirstDoublingOutputRing W ij out :=
  fun j ↦
    ↑(projectivePairChartFirstDoublingOutputUnit W ij out)⁻¹ *
      algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartFirstDoublingOutputRing W ij out)
        (projectivePairChartFirstDoublingCoordinates W ij j)

/-- The selected coordinate of the localized doubling output point is one. -/
@[simp]
theorem projectivePairChartFirstDoublingOutputPoint_normalized
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    projectivePairChartFirstDoublingOutputPoint W ij out
      (coveringCoordinate out) = 1 := by
  rw [projectivePairChartFirstDoublingOutputPoint]
  rw [← (IsLocalization.Away.algebraMap_isUnit
    (projectivePairChartFirstDoublingCoordinates W ij
      (coveringCoordinate out))).unit_spec]
  exact Units.inv_mul _

/-- The normalized doubling output point satisfies the mapped cubic equation
on its output-coordinate principal localization. -/
theorem projectivePairChartFirstDoublingOutputPoint_equation
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    (W.map (algebraMap K
      (projectivePairChartFirstDoublingOutputRing W ij out))).toProjective.Equation
        (projectivePairChartFirstDoublingOutputPoint W ij out) := by
  let R := projectivePairChartCoordinateRing W ij
  let S := projectivePairChartFirstDoublingOutputRing W ij out
  let f : R →+* S := algebraMap R S
  have hmap : ((projectivePairChartMappedCurve W ij).map f).toProjective.Equation
      (f ∘ projectivePairChartFirstDoublingCoordinates W ij) :=
    (projectivePairChartFirstDoublingCoordinates_equation W ij).map f
  have hscaled :=
    (((projectivePairChartMappedCurve W ij).map f).toProjective.equation_smul
      (f ∘ projectivePairChartFirstDoublingCoordinates W ij)
      (projectivePairChartFirstDoublingOutputUnit W ij out)⁻¹.isUnit).mpr hmap
  have hf : f.comp (algebraMap K R) = algebraMap K S :=
    (IsScalarTower.algebraMap_eq K R S).symm
  rw [projectivePairChartMappedCurve, WeierstrassCurve.map_map, hf] at hscaled
  have hp : (↑(projectivePairChartFirstDoublingOutputUnit W ij out)⁻¹ : S) •
      (f ∘ projectivePairChartFirstDoublingCoordinates W ij) =
        projectivePairChartFirstDoublingOutputPoint W ij out := by
    funext j
    rfl
  rw [hp] at hscaled
  exact hscaled

/-- The normalized doubling point induces a `K`-algebra map from the selected
quotient output chart. -/
noncomputable def projectivePairChartFirstDoublingOutputAlgHom
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    coveringChartCoordinateRing W out →ₐ[K]
      projectivePairChartFirstDoublingOutputRing W ij out :=
  coveringChartCoordinateRingAlgHomOfNormalizedPoint W out
    (projectivePairChartFirstDoublingOutputPoint W ij out)
    (projectivePairChartFirstDoublingOutputPoint_equation W ij out)
    (projectivePairChartFirstDoublingOutputPoint_normalized W ij out)

/-- On coordinate ratios, the doubling output algebra map is exactly the
selected normalized doubling coordinate. -/
@[simp]
theorem projectivePairChartFirstDoublingOutputAlgHom_ratio
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) (j : Fin 3) :
    projectivePairChartFirstDoublingOutputAlgHom W ij out
        (Ideal.Quotient.mk (coveringChartIdeal W out)
          (coordinateChartRatio (coveringCoordinate out) j)) =
      projectivePairChartFirstDoublingOutputPoint W ij out j := by
  exact coveringChartCoordinateRingAlgHomOfNormalizedPoint_ratio W out
    (projectivePairChartFirstDoublingOutputPoint W ij out)
    (projectivePairChartFirstDoublingOutputPoint_equation W ij out)
    (projectivePairChartFirstDoublingOutputPoint_normalized W ij out) j

/-- The selected doubling-output principal open, mapped into its original
projective-pair chart through the tensor-product presentation. -/
noncomputable def projectivePairChartFirstDoublingOutputOpen
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    Spec (.of (projectivePairChartFirstDoublingOutputRing W ij out)) ⟶
      projectivePairChartScheme W ij :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartFirstDoublingOutputRing W ij out))) ≫
    (projectivePairChartIsoSpecTensor W ij).inv

instance projectivePairChartFirstDoublingOutputOpen_isOpenImmersion
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    IsOpenImmersion
      (projectivePairChartFirstDoublingOutputOpen W ij out) := by
  dsimp only [projectivePairChartFirstDoublingOutputOpen,
    projectivePairChartFirstDoublingOutputRing]
  infer_instance

/-- Under the affine presentation, the doubling source is precisely the basic
open obtained by inverting the selected output coordinate. -/
@[reassoc]
theorem projectivePairChartFirstDoublingOutputOpen_comp_iso_hom
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool) :
    projectivePairChartFirstDoublingOutputOpen W ij out ≫
        (projectivePairChartIsoSpecTensor W ij).hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartFirstDoublingOutputRing W ij out))) := by
  simp [projectivePairChartFirstDoublingOutputOpen]

/-- The regular doubling formula on the principal open where the selected
output coordinate is invertible. -/
noncomputable def projectivePairChartFirstDoublingOutputMorphism
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    Spec (.of (projectivePairChartFirstDoublingOutputRing W ij out)) ⟶
      scheme W :=
  Spec.map (CommRingCat.ofHom
      (projectivePairChartFirstDoublingOutputAlgHom W ij out).toRingHom) ≫
    coveringChartMap W out

/-- Every localized doubling formula is an actual morphism over `Spec K`. -/
@[reassoc]
theorem projectivePairChartFirstDoublingOutputMorphism_comp_structureMap
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (out : Bool) :
    projectivePairChartFirstDoublingOutputMorphism W ij out ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (algebraMap K
          (projectivePairChartFirstDoublingOutputRing W ij out))) := by
  rw [projectivePairChartFirstDoublingOutputMorphism, Category.assoc,
    coveringChartMap_comp_structureMap, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  ext a
  exact (projectivePairChartFirstDoublingOutputAlgHom W ij out).commutes a

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
