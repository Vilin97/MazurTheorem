/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveCoordinateChartFunction
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistNaturalTransformationRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenImmersionMapIsoRange

/-!
# Relative projective coordinate scalar-twist maps

After arbitrary base change `g : T ⟶ ℙ^d_k`, a coordinate `Xᵣ`
defines a natural map from the identity to the positive relative Serre
scalar twist.  It is invertible on the pulled-back `r`-th chart.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules

variable (k : Type) [CommRing k] (d : ℕ)
  {T : Scheme.{0}} (g : T ⟶ scheme k d)

local instance relativeStandardCoverMapIsOpenImmersion
    (r : Fin (d + 1)) :
    IsOpenImmersion ((cover k d).f r) :=
  Scheme.Cover.map_prop (cover k d) r

local instance pulledBackRelativeStandardCoverMapIsOpenImmersion
    (r : Fin (d + 1)) :
    IsOpenImmersion (((cover k d).pullback₁ g).f r) :=
  Scheme.Cover.map_prop ((cover k d).pullback₁ g) r

/--
The coordinate `Xᵣ` defines a natural map into the positive relative
degree-`N` Serre scalar twist after arbitrary base change.
-/
noncomputable def relativeProjectiveCoordinateScalarTwistNatTrans
    (N : ℕ) (r : Fin (d + 1)) :
    𝟭 T.Modules ⟶
      (relativeProjectiveSerreTwistEquivalence
        k d g (N : ℤ)).functor :=
  openCoverScalarTwistNatTrans
    ((cover k d).pullback₁ g)
    (baseChangedIntegerCoverUnit k d g (N : ℤ))
    (baseChangedIntegerCoverUnit_self k d g (N : ℤ))
    (baseChangedIntegerCoverUnit_cocycle k d g (N : ℤ))
    (baseChangedCoordinateChartFunction k d g N r)
    (baseChangedCoordinateChartFunction_coverCompatible
      k d g N r)

/-- The member of the pulled-back standard cover indexed by `r` has
open range `g ⁻¹ᵁ D₊(Xᵣ)`. -/
theorem relativeStandardChartMap_opensRange
    (r : Fin (d + 1)) :
    (((cover k d).pullback₁ g).f r).opensRange =
      g ⁻¹ᵁ standardChart k r := by
  change
    (CategoryTheory.Limits.pullback.fst
      g ((cover k d).f r)).opensRange =
      g ⁻¹ᵁ standardChart k r
  rw [Scheme.Hom.opensRange_pullbackFst,
    standardCoverMap_opensRange]

/--
The relative coordinate natural map is an isomorphism after restriction
to the pulled-back standard chart whose open range is
`g ⁻¹ᵁ D₊(Xᵣ)`.
-/
theorem isIso_relativeProjectiveCoordinateScalarTwistNatTrans_restrict_chart
    (N : ℕ) (r : Fin (d + 1))
    (M : T.Modules) :
    IsIso
      ((pullback (((cover k d).pullback₁ g).f r)).map
        ((relativeProjectiveCoordinateScalarTwistNatTrans
          k d g N r).app M)) := by
  change
    IsIso
      ((pullback (((cover k d).pullback₁ g).f r)).map
        ((openCoverScalarTwistNatTrans
          ((cover k d).pullback₁ g)
          (baseChangedIntegerCoverUnit
            k d g (N : ℤ))
          (baseChangedIntegerCoverUnit_self
            k d g (N : ℤ))
          (baseChangedIntegerCoverUnit_cocycle
            k d g (N : ℤ))
          (baseChangedCoordinateChartFunction
            k d g N r)
          (baseChangedCoordinateChartFunction_coverCompatible
            k d g N r)).app M))
  exact
    isIso_openCoverScalarTwistNatTrans_restrict_of_eq_one
      ((cover k d).pullback₁ g)
      (baseChangedIntegerCoverUnit k d g (N : ℤ))
      (baseChangedIntegerCoverUnit_self k d g (N : ℤ))
      (baseChangedIntegerCoverUnit_cocycle k d g (N : ℤ))
      (baseChangedCoordinateChartFunction k d g N r)
      (baseChangedCoordinateChartFunction_coverCompatible
        k d g N r)
      M r
      (baseChangedCoordinateChartFunction_self
        k d g N r)

/--
Equivalently, the relative coordinate natural map is an isomorphism
after restriction to the actual open subscheme
`g ⁻¹ᵁ standardChart k r`.
-/
theorem isIso_relativeProjectiveCoordinateScalarTwistNatTrans_restrict_preimage_standardChart
    (N : ℕ) (r : Fin (d + 1))
    (M : T.Modules) :
    IsIso
      ((pullback
        ((g ⁻¹ᵁ standardChart k r).ι)).map
        ((relativeProjectiveCoordinateScalarTwistNatTrans
          k d g N r).app M)) := by
  let fchart :=
    ((cover k d).pullback₁ g).f r
  let α :=
    (relativeProjectiveCoordinateScalarTwistNatTrans
      k d g N r).app M
  letI :
      IsIso ((pullback fchart).map α) := by
    exact
      isIso_relativeProjectiveCoordinateScalarTwistNatTrans_restrict_chart
        k d g N r M
  have hRange :
      IsIso
        ((pullback fchart.opensRange.ι).map α) :=
    isIso_pullback_opensRange_of_isIso_pullback
      fchart α
  have hopen :
      fchart.opensRange =
        g ⁻¹ᵁ standardChart k r :=
    relativeStandardChartMap_opensRange
      k d g r
  rw [hopen] at hRange
  exact hRange

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
