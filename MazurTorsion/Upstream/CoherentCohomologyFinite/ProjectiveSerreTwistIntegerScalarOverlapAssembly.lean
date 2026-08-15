/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarOverlapPointwise

/-!
# Assembly of the evaluated integer scalar overlap chain

This file composes the ten pointwise comparison steps through small
opaque equality-chain lemma.  The opacity of that generic lemma prevents
kernel checking from expanding a deeply nested tower of equality
recursors whose endpoints contain the effective-descent comparison maps.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

private theorem eq_trans_nine
    {α : Sort*} {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) (h₂ : a₂ = a₃)
    (h₃ : a₃ = a₄) (h₄ : a₄ = a₅) (h₅ : a₅ = a₆)
    (h₆ : a₆ = a₇) (h₇ : a₇ = a₈) (h₈ : a₈ = a₉) :
    a₀ = a₉ :=
  h₀.trans (h₁.trans (h₂.trans (h₃.trans
    (h₄.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))))

private theorem eq_trans_four
    {α : Sort*} {a₀ a₁ a₂ a₃ a₄ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) (h₂ : a₂ = a₃)
    (h₃ : a₃ = a₄) : a₀ = a₄ :=
  h₀.trans (h₁.trans (h₂.trans h₃))

private theorem eq_trans_two
    {α : Sort*} {a₀ a₁ a₂ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) : a₀ = a₂ :=
  h₀.trans h₁

private theorem eq_trans_three
    {α : Sort*} {a₀ a₁ a₂ a₃ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) (h₂ : a₂ = a₃) :
    a₀ = a₃ :=
  h₀.trans (h₁.trans h₂)

private theorem eq_trans_five
    {α : Sort*} {a₀ a₁ a₂ a₃ a₄ a₅ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) (h₂ : a₂ = a₃)
    (h₃ : a₃ = a₄) (h₄ : a₄ = a₅) : a₀ = a₅ :=
  h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

private def projectiveIntegerScalarLegOverlapAppPrefixLeft
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  eq_trans_three
    (projectiveIntegerFirstScalarFactorAppRaw k d m i j W x)
    (projectiveIntegerDescentScalarCompatibilityAppRaw
      k d m i j W x)
    (projectiveIntegerSecondChartCoreNormalizeAppRaw
      k d m i j W x)

private def projectiveIntegerScalarLegOverlapAppTransportNormalize
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  eq_trans_two
    (projectiveIntegerSecondScalarTransportRightAppRaw
      k d m i j W x)
    (projectiveIntegerSecondScalarTransportEndpointAppRaw
      k d m i j W x)

private def projectiveIntegerScalarLegOverlapAppTransportSquare
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  eq_trans_two
    (projectiveIntegerSecondScalarTransportEndpointReassocAppRaw
      k d m i j W x)
    (projectiveIntegerSecondScalarTransportAppRaw k d m i j W x)

private def projectiveIntegerScalarLegOverlapAppPrefixRight
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  (projectiveIntegerScalarLegOverlapAppTransportNormalize
      k d m i j W x).trans
    (projectiveIntegerScalarLegOverlapAppTransportSquare
      k d m i j W x)

private def projectiveIntegerScalarLegOverlapAppPrefix
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  (projectiveIntegerScalarLegOverlapAppPrefixLeft
      k d m i j W x).trans
    (projectiveIntegerScalarLegOverlapAppPrefixRight
      k d m i j W x)

private def projectiveIntegerScalarLegOverlapAppSuffix
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  eq_trans_five
    (projectiveIntegerSecondComparisonNormalizeAppRaw
      k d m i j W x)
    (projectiveIntegerSecondComparisonSuffixAppRaw k d m i j W x)
    (projectiveIntegerSecondComparisonReassocAppRaw k d m i j W x)
    (projectiveIntegerSecondChartCoreFactorAppRaw k d m i j W x)
    (projectiveIntegerRawSecondScalarTrivializeAppRaw k d m i j W x)

/-- The fully assembled scalar-leg equality, with its literal proposition
type inferred from the ten adjacent pointwise steps. -/
def projectiveIntegerScalarLegOverlapAppRaw
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :=
  (projectiveIntegerScalarLegOverlapAppPrefix k d m i j W x).trans
    (projectiveIntegerScalarLegOverlapAppSuffix k d m i j W x)

/-- On every overlap section, the first projective scalar leg agrees with
the fully literal second-chart scalar route. -/
theorem projectiveIntegerFirstScalar_eq_rawSecondScalar_app
    (m : ℤ) (i j : Fin (d + 1))
    (W : ((glueData k d).V (i, j)).Opens)
    (x : IntegerOverlapSection k d m i j W) :
    (projectiveIntegerFirstScalarLeg k d m i j).app W x =
      (((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m) ≫
          projectiveIntegerSecondChartLegCore k d m i j) ≫
        ((pullbackUnitIso
            ((glueData k d).t i j ≫
              (glueData k d).f j i)).hom ≫
          endomorphism (((overlapUnit k d i j) ^ m).inv))).app W x :=
  projectiveIntegerScalarLegOverlapAppRaw k d m i j W x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
