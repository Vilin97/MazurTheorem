/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModification
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveFactorizationChoice
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistFiniteness

/-!
# Relative Serre twists on a projective modification

A projective modification carries a chosen map to absolute projective
space through its relative projective factorization.  Pulling the
integer Serre cocycle along that map gives a named autoequivalence of
the module category of the model.
-/

open AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace ProjectiveModification

open ProjectiveSpace
open ProjectiveSpace.IsRelativeProjectiveFactorization
open ProjectiveSpace.SerreTwist

variable {k : Type} [CommRing k]
  {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of k)}

/-- Relative integer Serre twist on the model of a projective
modification. -/
noncomputable def serreTwistEquivalence
    (P : ProjectiveModification f) (m : ℤ) :
    P.model.Modules ≌ P.model.Modules :=
  relativeProjectiveSerreTwistEquivalence
    k P.relativeProjective.chosenDimension
    P.relativeProjective.chosenProjectiveMap m

/-- Object-level relative Serre twist. -/
abbrev serreTwistModule
    (P : ProjectiveModification f) (m : ℤ)
    (M : P.model.Modules) : P.model.Modules :=
  (P.serreTwistEquivalence m).functor.obj M

/-- Relative Serre twisting preserves quasicoherence. -/
theorem serreTwistModule_isQuasicoherent
    (P : ProjectiveModification f) (m : ℤ)
    (M : P.model.Modules) (hM : M.IsQuasicoherent) :
    (P.serreTwistModule m M).IsQuasicoherent := by
  letI : M.IsQuasicoherent := hM
  exact
    relativeProjectiveSerreTwist_isQuasicoherent
      k P.relativeProjective.chosenDimension
      P.relativeProjective.chosenProjectiveMap
      m M

/-- Relative Serre twisting preserves finite type. -/
theorem serreTwistModule_isFiniteType
    (P : ProjectiveModification f) (m : ℤ)
    (M : P.model.Modules) (hM : M.IsFiniteType) :
    (P.serreTwistModule m M).IsFiniteType := by
  letI : M.IsFiniteType := hM
  exact
    relativeProjectiveSerreTwist_isFiniteType
      k P.relativeProjective.chosenDimension
      P.relativeProjective.chosenProjectiveMap
      m M

/-- Relative Serre twisting preserves coherence. -/
theorem serreTwistModule_coherent
    (P : ProjectiveModification f) (m : ℤ)
    (M : P.model.Modules)
    (hM : M.IsFiniteType ∧ M.IsQuasicoherent) :
    (P.serreTwistModule m M).IsFiniteType ∧
      (P.serreTwistModule m M).IsQuasicoherent := by
  letI : M.IsFiniteType := hM.1
  letI : M.IsQuasicoherent := hM.2
  exact
    relativeProjectiveSerreTwist_isCoherent
      k P.relativeProjective.chosenDimension
      P.relativeProjective.chosenProjectiveMap
      m M

/-- A relative Serre twist is unchanged after restriction to any chart
of the pulled-back standard projective cover. -/
noncomputable def serreTwistModuleChartRestrictionIso
    (P : ProjectiveModification f) (m : ℤ)
    (M : P.model.Modules)
    (i : Fin (P.relativeProjective.chosenDimension + 1)) :
    (Scheme.Modules.pullback
      (((ProjectiveSpace.SerreTwist.cover
        k P.relativeProjective.chosenDimension).pullback₁
          P.relativeProjective.chosenProjectiveMap).f i)).obj
        (P.serreTwistModule m M) ≅
      (Scheme.Modules.pullback
        (((ProjectiveSpace.SerreTwist.cover
          k P.relativeProjective.chosenDimension).pullback₁
            P.relativeProjective.chosenProjectiveMap).f i)).obj M :=
  relativeProjectiveSerreTwistChartRestrictionIso
    k P.relativeProjective.chosenDimension
    P.relativeProjective.chosenProjectiveMap
    m M i

end ProjectiveModification
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
