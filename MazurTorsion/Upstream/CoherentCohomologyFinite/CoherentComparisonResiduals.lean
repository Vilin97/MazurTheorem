/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoherentCokernel
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoherentKernel

/-!
# Coherence of kernel--image--cokernel residuals

On a locally Noetherian scheme, the image of a morphism between coherent
module sheaves is coherent.  Consequently, both residual objects in the
kernel--image--cokernel factorization are coherent.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{0}}

/-- The two residuals used by support dévissage are finite type and
quasicoherent. -/
theorem comparisonResidual_isFiniteType_and_isQuasicoherent
    [IsLocallyNoetherian X]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsFiniteType] [M.IsQuasicoherent]
    [N.IsFiniteType] [N.IsQuasicoherent] :
    ((kernel
          (Abelian.factorThruImage f)).IsFiniteType ∧
        (kernel
          (Abelian.factorThruImage f)).IsQuasicoherent) ∧
      ((cokernel
          (Abelian.image.ι f)).IsFiniteType ∧
        (cokernel
          (Abelian.image.ι f)).IsQuasicoherent) := by
  have hcokernel :
      (cokernel f).IsFiniteType ∧
        (cokernel f).IsQuasicoherent :=
    cokernel_isFiniteType_and_isQuasicoherent f
  letI : (cokernel f).IsFiniteType :=
    hcokernel.1
  letI : (cokernel f).IsQuasicoherent :=
    hcokernel.2
  have himage :
      (Abelian.image f).IsFiniteType ∧
        (Abelian.image f).IsQuasicoherent :=
    kernel_isFiniteType_and_isQuasicoherent
      (cokernel.π f)
  letI : (Abelian.image f).IsFiniteType :=
    himage.1
  letI : (Abelian.image f).IsQuasicoherent :=
    himage.2
  exact
    ⟨kernel_isFiniteType_and_isQuasicoherent
        (Abelian.factorThruImage f),
      cokernel_isFiniteType_and_isQuasicoherent
        (Abelian.image.ι f)⟩

end AlgebraicGeometry.Scheme.Modules
