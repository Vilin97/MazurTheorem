/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenImmersionOverIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverCoversTop

/-!
# Finiteness of relative projective scalar twists

The relative scalar-twist autoequivalence is locally the identity on the
pulled-back standard projective cover.  Quasicoherence and finite type
therefore follow from their local character.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules

variable (k : Type) [CommRing k] (d : ℕ)
  {T : Scheme.{0}} (f : T ⟶ scheme k d)

/-- The range open of one chart in the pulled-back standard cover. -/
noncomputable abbrev relativeProjectiveChartOpen
    (i : Fin (d + 1)) : T.Opens := by
  let 𝒱 : T.OpenCover := (cover k d).pullback₁ f
  letI : IsOpenImmersion (𝒱.f i) := 𝒱.map_prop i
  exact (𝒱.f i).opensRange

/--
Slice-site form of the chartwise identity for the relative scalar twist.
-/
noncomputable def relativeProjectiveSerreTwistOverChartIso
    (m : ℤ) (M : T.Modules) (i : Fin (d + 1)) :
    ((relativeProjectiveSerreTwistEquivalence
        k d f m).functor.obj M).over
          (relativeProjectiveChartOpen k d f i) ≅
      M.over (relativeProjectiveChartOpen k d f i) :=
  by
    let 𝒱 : T.OpenCover := (cover k d).pullback₁ f
    letI : IsOpenImmersion (𝒱.f i) := 𝒱.map_prop i
    exact
      overRangeIsoOfPullbackIso
        (𝒱.f i)
        (relativeProjectiveSerreTwistChartRestrictionIso
          k d f m M i)

/-- The relative projective scalar twist preserves quasicoherence. -/
theorem relativeProjectiveSerreTwist_isQuasicoherent
    (m : ℤ) (M : T.Modules) [M.IsQuasicoherent] :
    ((relativeProjectiveSerreTwistEquivalence
      k d f m).functor.obj M).IsQuasicoherent := by
  let 𝒱 : T.OpenCover := (cover k d).pullback₁ f
  letI (i : Fin (d + 1)) : IsOpenImmersion (𝒱.f i) :=
    𝒱.map_prop i
  let N :=
    (relativeProjectiveSerreTwistEquivalence
      k d f m).functor.obj M
  let U : Fin (d + 1) → T.Opens :=
    relativeProjectiveChartOpen k d f
  have hU :
      (Opens.grothendieckTopology T).CoversTop U :=
    Opens.coversTop_of_iSup_eq_top U
      (by
        change
          ⨆ i : Fin (d + 1),
              ((((cover k d).pullback₁ f).f i).opensRange) =
            ⊤
        exact
          Scheme.OpenCover.iSup_opensRange
            ((cover k d).pullback₁ f))
  letI (i : Fin (d + 1)) :
      (N.over (U i)).IsQuasicoherent := by
    apply
      (SheafOfModules.isQuasicoherent
        (T.ringCatSheaf.over (U i))).prop_of_iso
          (relativeProjectiveSerreTwistOverChartIso
            k d f m M i).symm
    infer_instance
  exact
    SheafOfModules.IsQuasicoherent.of_coversTop
      N U hU

/-- The relative projective scalar twist preserves finite type. -/
theorem relativeProjectiveSerreTwist_isFiniteType
    (m : ℤ) (M : T.Modules) [M.IsFiniteType] :
    ((relativeProjectiveSerreTwistEquivalence
      k d f m).functor.obj M).IsFiniteType := by
  let 𝒱 : T.OpenCover := (cover k d).pullback₁ f
  letI (i : Fin (d + 1)) : IsOpenImmersion (𝒱.f i) :=
    𝒱.map_prop i
  let N :=
    (relativeProjectiveSerreTwistEquivalence
      k d f m).functor.obj M
  let U : Fin (d + 1) → T.Opens :=
    relativeProjectiveChartOpen k d f
  have hU :
      (Opens.grothendieckTopology T).CoversTop U :=
    Opens.coversTop_of_iSup_eq_top U
      (by
        change
          ⨆ i : Fin (d + 1),
              ((((cover k d).pullback₁ f).f i).opensRange) =
            ⊤
        exact
          Scheme.OpenCover.iSup_opensRange
            ((cover k d).pullback₁ f))
  letI (i : Fin (d + 1)) :
      (N.over (U i)).IsFiniteType := by
    exact
      SheafOfModules.isFiniteType_of_iso
        (R := T.ringCatSheaf.over (U i))
        (relativeProjectiveSerreTwistOverChartIso
          k d f m M i).symm
  exact
    SheafOfModules.IsFiniteType.of_coversTop
      N U hU

/-- The relative scalar twist preserves the pair of finiteness properties
used as coherence in this development. -/
theorem relativeProjectiveSerreTwist_isCoherent
    (m : ℤ) (M : T.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    ((relativeProjectiveSerreTwistEquivalence
          k d f m).functor.obj M).IsFiniteType ∧
      ((relativeProjectiveSerreTwistEquivalence
          k d f m).functor.obj M).IsQuasicoherent :=
  ⟨relativeProjectiveSerreTwist_isFiniteType
      k d f m M,
    relativeProjectiveSerreTwist_isQuasicoherent
      k d f m M⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
