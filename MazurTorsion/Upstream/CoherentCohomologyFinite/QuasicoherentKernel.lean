/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentExactness
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffinePresentationData

/-!
# Kernels of quasicoherent module sheaves

Open restriction is exact.  Hence the restriction of a kernel to an
affine open is the kernel of the restricted map.  Affine
quasicoherent modules are closed under kernels and have global
presentations, so these affine presentations assemble to
quasicoherent data for the original kernel.
-/


universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

open Modules

variable {X : Scheme.{u}}

/-- The kernel of a morphism of quasicoherent module sheaves is
quasicoherent. -/
theorem Modules.isQuasicoherent_kernel_coherentCohomology
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  let P :
      ∀ U : X.affineOpens,
        ((kernel f).restrict (U : X.Opens).ι).Presentation :=
    fun U => by
      let fU :=
        (restrictFunctor (U : X.Opens).ι).map f
      haveI : ((restrictFunctor
          (U : X.Opens).ι).obj M).IsQuasicoherent :=
        inferInstance
      haveI : ((restrictFunctor
          (U : X.Opens).ι).obj N).IsQuasicoherent :=
        inferInstance
      haveI : (kernel fU).IsQuasicoherent :=
        (isQuasicoherentCohomology U).prop_kernel fU
          (by infer_instance) (by infer_instance)
      let Pker : (kernel fU).Presentation :=
        quasicoherentPresentation (kernel fU)
      let e :
          (kernel f).restrict (U : X.Opens).ι ≅
            kernel fU :=
        PreservesKernel.iso
          (restrictFunctor (U : X.Opens).ι) f
      exact
        @SheafOfModules.Presentation.ofIsIso.{u}
          _ _ _ _ _ _ _ _ e.inv e.isIso_inv Pker
  exact
    (quasicoherentDataOfAffineOpenPresentations
      (kernel f) P).isQuasicoherent

/-- Quasicoherent module sheaves on any scheme are closed under
kernels. -/
noncomputable instance isQuasicoherent_isClosedUnderKernels :
    (isQuasicoherentCohomology X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have hker :
        (isQuasicoherentCohomology X) (kernel f) :=
      @Modules.isQuasicoherent_kernel_coherentCohomology
        X _ _ f hf.1 hf.2
    exact
      (isQuasicoherentCohomology X).prop_of_iso
        ((kernelIsKernel f).conePointUniqueUpToIso hk)
        hker

end AlgebraicGeometry.Scheme
