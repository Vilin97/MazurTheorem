/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineOpenRestrictedBaseScalars
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveFiniteSections

/-!
# Finite sections of a relative-projective pushforward

This file transports the fixed-base finite-generation statement on an
affine inverse image to the corresponding section module of the direct
image.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open SerreTwist

/-- Sections of a relative-projective direct image over an affine open
are finite over the ring of functions on that open. -/
theorem finiteSections_pushforward_of_relativeProjectiveFactorization
    {Y X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of ℚ)}
    {f : Y ⟶ X}
    [IsLocallyNoetherian X]
    (hprojective : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (hchart :
      ∀ (d : ℕ) (m : ℤ),
        BaseStandardCoverCoordinatesNatural Γ(X, U) d m)
    (hcoordinate :
      ∀ (d N : ℕ),
        IntegerOverChartCoordinateTransition Γ(X, U) d N) :
    Module.Finite Γ(X, U)
      Γ((Scheme.Modules.pushforward f).obj M, U) := by
  letI : Algebra ℚ Γ(X, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  letI :
      (f ⁻¹ᵁ U).toScheme.Over
        (Spec (CommRingCat.of Γ(X, U))) :=
    ⟨morphismRestrict f U ≫ hU.isoSpec.hom⟩
  have hfinite :=
    finiteSections_preimage_of_relativeProjectiveFactorization
      hprojective M U hU hchart hcoordinate
  let e :=
    pushforwardSectionsLinearEquivRestrictTop
      f U hU M
  letI := hfinite
  exact Module.Finite.equiv e.symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
