/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `CoherentComparisonResiduals.lean`
in Vilin97/Clawristotle.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleQuasicoherent
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafModuleFiniteTypeQuotient

/-!
# Coherence of comparison residuals

On a locally Noetherian scheme, both residuals in the
kernel-image-cokernel factorization of a morphism between finite-type
quasicoherent modules are again finite type and quasicoherent.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Both residuals used by support induction are finite type and quasicoherent. -/
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
  letI : (Abelian.image f).IsQuasicoherent :=
    isQuasicoherent_image f
  have hkernel :
      (kernel (Abelian.factorThruImage f)).IsFiniteType ∧
        (kernel (Abelian.factorThruImage f)).IsQuasicoherent :=
    ⟨isFiniteType_kernel (Abelian.factorThruImage f),
      isQuasicoherent_kernel (Abelian.factorThruImage f)⟩
  let q :
      N ⟶ cokernel (Abelian.image.ι f) :=
    cokernel.π (Abelian.image.ι f)
  letI hq : Epi q := by
    dsimp only [q]
    infer_instance
  have hqFinite :
      (cokernel (Abelian.image.ι f)).IsFiniteType :=
    @SheafOfModules.isFiniteType_of_epi
      (Opens X) (inferInstance) (inferInstance)
      (Opens.grothendieckTopology X) X.ringCatSheaf
      (inferInstance) (inferInstance)
      N (cokernel (Abelian.image.ι f)) q hq
      (inferInstanceAs N.IsFiniteType)
  have hcokernel :
      (cokernel (Abelian.image.ι f)).IsFiniteType ∧
        (cokernel (Abelian.image.ι f)).IsQuasicoherent :=
    ⟨hqFinite,
      isQuasicoherent_cokernel (Abelian.image.ι f)⟩
  exact ⟨hkernel, hcokernel⟩

end AlgebraicGeometry.Scheme.Modules
