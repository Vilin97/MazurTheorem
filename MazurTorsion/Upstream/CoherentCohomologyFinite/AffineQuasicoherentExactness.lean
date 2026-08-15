/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafRestrictionExactness
import MazurTorsion.Upstream.CoherentCohomologyFinite.TildeExactness
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Kernels of quasicoherent modules on affine schemes

On a spectrum, quasicoherent modules form the essential image of the
tilde functor.  Exactness of tilde therefore makes this essential image
closed under finite limits, in particular kernels.  The result is
transported to an arbitrary affine scheme through its canonical
isomorphism with a spectrum.
-/


universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

open Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

section Spec

variable [Modules.HasQuasicoherentTildeCounit R]

/-- Quasicoherent modules on a spectrum are closed under
parallel-pair limits. -/
noncomputable instance
    isQuasicoherent_spec_isClosedUnderParallelPairLimits :
    (isQuasicoherentCohomology (Spec R)).IsClosedUnderLimitsOfShape
      WalkingParallelPair := by
  rw [← isQuasicoherent_iff_tilde_essImage]
  haveI :
      HasLimitsOfShape WalkingParallelPair (ModuleCat R) :=
    inferInstance
  haveI :
      PreservesLimitsOfShape WalkingParallelPair
        (tilde.functor R) :=
    inferInstance
  exact
    instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsOfShapeOfPreservesLimitsOfShapeOfFullOfFaithful
      (tilde.functor R)

/-- Quasicoherent modules on a spectrum are closed under kernels. -/
noncomputable instance isQuasicoherent_spec_isClosedUnderKernels :
    (isQuasicoherentCohomology (Spec R)).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    apply (isQuasicoherentCohomology (Spec R)).prop_of_isLimit hk
    intro j
    cases j with
    | zero => exact hf.1
    | one => exact hf.2

end Spec

section Affine

variable [∀ S : CommRingCat.{u},
  Modules.HasQuasicoherentTildeCounit S]

/-- Quasicoherent modules on an affine scheme are closed under
parallel-pair limits. -/
noncomputable instance
    isQuasicoherent_affine_isClosedUnderParallelPairLimits
    [IsAffine X] :
    (isQuasicoherentCohomology X).IsClosedUnderLimitsOfShape
      WalkingParallelPair := by
  rw [← isQuasicoherent_inverseImage_iso_coherentCohomology
    (isoSpec X).symm]
  infer_instance

/-- Quasicoherent modules on an affine scheme are closed under kernels. -/
noncomputable instance isQuasicoherent_affine_isClosedUnderKernels
    [IsAffine X] :
    (isQuasicoherentCohomology X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    apply (isQuasicoherentCohomology X).prop_of_isLimit hk
    intro j
    cases j with
    | zero => exact hf.1
    | one => exact hf.2

end Affine

end AlgebraicGeometry.Scheme
