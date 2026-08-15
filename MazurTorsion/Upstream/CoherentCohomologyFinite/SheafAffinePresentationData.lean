/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverCoversTop
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverPresentation
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Quasicoherent data from affine-open presentations

If every restriction of a module sheaf to an affine open has a global
presentation, those presentations form quasicoherent data on the
standard cover by all affine opens.
-/


open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/--
Quasicoherent data obtained from a chosen global presentation on every
affine open restriction.
-/
noncomputable def quasicoherentDataOfAffineOpenPresentations
    (P : ∀ U : X.affineOpens,
      (M.restrict (U : X.Opens).ι).Presentation) :
    M.QuasicoherentData where
  I := X.affineOpens
  X U := (U : X.Opens)
  coversTop :=
    TopologicalSpace.Opens.coversTop_of_iSup_eq_top
      (fun U : X.affineOpens => (U : X.Opens))
      (AlgebraicGeometry.iSup_affineOpens_eq_top X)
  presentation U :=
    Presentation.overOfRestrict (U : X.Opens) M (P U)

end AlgebraicGeometry.Scheme.Modules
