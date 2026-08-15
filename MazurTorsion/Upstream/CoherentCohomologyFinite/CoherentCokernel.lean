/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.QuasicoherentCokernel
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeQuotient

/-!
# Cokernels of coherent module sheaves

Finite type descends to quotients, and quasicoherent module sheaves are
closed under cokernels.  Thus the cokernel of a map between coherent
module sheaves is coherent; no Noetherian hypothesis is needed for this
right-exact closure statement.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{0}}

/-- A cokernel of finite-type quasicoherent modules is again finite type
and quasicoherent. -/
theorem cokernel_isFiniteType_and_isQuasicoherent
    {M N : X.Modules} (f : M ⟶ N)
    [N.IsFiniteType]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsFiniteType ∧
      (cokernel f).IsQuasicoherent := by
  let q : N ⟶ cokernel f :=
    cokernel.π f
  have hq : Epi q :=
    coequalizer.π_epi
  have hfinite : (cokernel f).IsFiniteType :=
    @SheafOfModules.isFiniteType_of_epi
      _ _ _ _ _ _ _ _ _ _ q hq
        (inferInstance : N.IsFiniteType)
  have hquasicoherent : (cokernel f).IsQuasicoherent :=
    isQuasicoherent_cokernel_coherentCohomology f
  exact ⟨hfinite, hquasicoherent⟩

end AlgebraicGeometry.Scheme.Modules
