/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineSpectrumQuasicoherentPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafPresentationRestriction

/-!
# Global presentations of quasicoherent modules on affine schemes

Every module admits a (possibly infinite) free presentation.  Applying
the exact affine tilde functor gives a presentation of its associated
sheaf.  The affine tilde-counit theorem transports this presentation to
an arbitrary quasicoherent module on a spectrum, and then along the
canonical affine-scheme isomorphism.
-/


universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A global presentation of a quasicoherent module on an affine
scheme. -/
noncomputable def quasicoherentPresentation
    (M : X.Modules) [IsAffine X] [M.IsQuasicoherent] :
    M.Presentation := by
  let N : (Spec Γ(X, ⊤)).Modules :=
    M.restrict X.isoSpec.inv
  let P : N.Presentation :=
    quasicoherentPresentationSpec N
  let P' : ((M.restrict X.isoSpec.inv).restrict
      X.isoSpec.hom).Presentation :=
    Presentation.restrict X.isoSpec.hom P
  let e := restrictIsoOfIso X.isoSpec M
  exact @SheafOfModules.Presentation.ofIsIso.{u}
    _ _ _ _ _ _ _ _ e.hom e.isIso_hom P'

end AlgebraicGeometry.Scheme.Modules
