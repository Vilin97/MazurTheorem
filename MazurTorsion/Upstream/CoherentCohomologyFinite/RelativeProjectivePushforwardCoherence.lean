/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSectionsCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.QcqsPushforward
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectivePushforwardFiniteSections

/-!
# Coherence of a relative-projective pushforward

Relative projectivity supplies properness, hence the qcqs hypotheses
needed for quasicoherent pushforward.  The projective Ext calculation
gives finite sections over every affine open, so the finite-section
criterion upgrades the direct image to a finitely presented module.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

/-- A relative-projective direct image of a finite-type quasicoherent
module is finitely presented over a locally Noetherian rational base. -/
theorem isFinitePresentation_pushforward_of_relativeProjectiveFactorization
    {Y X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of ℚ)}
    {f : Y ⟶ X}
    [IsLocallyNoetherian X]
    (hprojective : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (hchart :
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (d : ℕ) (m : ℤ),
          BaseStandardCoverCoordinatesNatural Γ(X, U) d m)
    (hcoordinate :
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (d N : ℕ),
          IntegerOverChartCoordinateTransition Γ(X, U) d N) :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  letI : IsProper f := hprojective.isProper
  letI :
      ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_qcqs f M
  apply
    Scheme.Modules.isFinitePresentation_of_finiteAffineSections
      ((Scheme.Modules.pushforward f).obj M)
  intro U hU
  exact
    finiteSections_pushforward_of_relativeProjectiveFactorization
      hprojective M U hU
        (hchart U hU) (hcoordinate U hU)

/-- Under the same hypotheses, the relative-projective direct image is
in particular of finite type. -/
theorem isFiniteType_pushforward_of_relativeProjectiveFactorization
    {Y X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of ℚ)}
    {f : Y ⟶ X}
    [IsLocallyNoetherian X]
    (hprojective : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (hchart :
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (d : ℕ) (m : ℤ),
          BaseStandardCoverCoordinatesNatural Γ(X, U) d m)
    (hcoordinate :
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (d N : ℕ),
          IntegerOverChartCoordinateTransition Γ(X, U) d N) :
    ((Scheme.Modules.pushforward f).obj M).IsFiniteType := by
  letI :
      ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_relativeProjectiveFactorization
      hprojective M hchart hcoordinate
  exact
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
      ((Scheme.Modules.pushforward f).obj M)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
