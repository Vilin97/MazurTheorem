/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffinePresentationData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafRestrictionExactness

/-!
# Cokernels of quasicoherent module sheaves

Open restriction is exact.  On affine schemes quasicoherent modules are
closed under colimits, hence under cokernels.  Affine presentations of the
restricted cokernels therefore assemble to quasicoherent data globally.
-/


universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme

open Modules

variable {X : Scheme.{u}}

/-- The cokernel of a morphism of quasicoherent module sheaves is
quasicoherent. -/
theorem Modules.isQuasicoherent_cokernel_coherentCohomology
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  let P :
      ∀ U : X.affineOpens,
        ((cokernel f).restrict (U : X.Opens).ι).Presentation :=
    fun U => by
      let fU :=
        (restrictFunctor (U : X.Opens).ι).map f
      haveI :
          ((restrictFunctor
            (U : X.Opens).ι).obj M).IsQuasicoherent :=
        inferInstance
      haveI :
          ((restrictFunctor
            (U : X.Opens).ι).obj N).IsQuasicoherent :=
        inferInstance
      let c : CokernelCofork fU :=
        CokernelCofork.ofπ (cokernel.π fU)
          (cokernel.condition fU)
      have hc : IsColimit c :=
        cokernelIsCokernel fU
      haveI : (cokernel fU).IsQuasicoherent := by
        exact
          (isQuasicoherentCohomology U).prop_of_isColimit
            (c := c) hc (fun j => by
              cases j with
              | zero =>
                  simpa only [parallelPair_obj_zero] using
                    (inferInstance :
                      ((restrictFunctor
                        (U : X.Opens).ι).obj M).IsQuasicoherent)
              | one =>
                  simpa only [parallelPair_obj_one] using
                    (inferInstance :
                      ((restrictFunctor
                        (U : X.Opens).ι).obj N).IsQuasicoherent))
      let Pcoker : (cokernel fU).Presentation :=
        quasicoherentPresentation (cokernel fU)
      let e :
          (cokernel f).restrict (U : X.Opens).ι ≅
            cokernel fU :=
        PreservesCokernel.iso
          (restrictFunctor (U : X.Opens).ι) f
      exact
        @SheafOfModules.Presentation.ofIsIso.{u}
          _ _ _ _ _ _ _ _ e.inv e.isIso_inv Pcoker
  exact
    (quasicoherentDataOfAffineOpenPresentations
      (cokernel f) P).isQuasicoherent

/-- Quasicoherent module sheaves on any scheme are closed under
cokernels. -/
noncomputable instance isQuasicoherent_isClosedUnderCokernels :
    (isQuasicoherentCohomology X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have hcoker :
        (isQuasicoherentCohomology X) (cokernel f) :=
      @Modules.isQuasicoherent_cokernel_coherentCohomology
        X _ _ f hf.1 hf.2
    exact
      (isQuasicoherentCohomology X).prop_of_iso
        ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
        hcoker

end AlgebraicGeometry.Scheme
