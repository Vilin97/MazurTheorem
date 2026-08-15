/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePullbackCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafGlobalFinitePresentation

/-!
# Coherent scheme modules under pullback

On a locally Noetherian target, finite-type quasicoherent modules are
finitely presented.  Finite presentation survives arbitrary pullback,
so the pullback is again finite type and quasicoherent.
-/

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
Pullback of a finite-type quasicoherent module from a locally Noetherian
scheme is finitely presented.
-/
theorem isFinitePresentation_pullback_of_isLocallyNoetherian
    [IsLocallyNoetherian Y]
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    ((pullback f).obj M).IsFinitePresentation := by
  letI : M.IsFinitePresentation :=
    isFinitePresentation_of_isLocallyNoetherian M
  exact isFinitePresentation_pullback f M

/--
Pullback preserves the finite-type quasicoherent notion of coherence
when the target is locally Noetherian.
-/
theorem pullback_isFiniteType_and_isQuasicoherent
    [IsLocallyNoetherian Y]
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    ((pullback f).obj M).IsFiniteType ∧
      ((pullback f).obj M).IsQuasicoherent := by
  letI : SheafOfModules.IsFinitePresentation.{u, u, u}
      ((pullback f).obj M) :=
    isFinitePresentation_pullback_of_isLocallyNoetherian f M
  exact
    ⟨SheafOfModules.instIsFiniteTypeOfIsFinitePresentation ((pullback f).obj M),
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation ((pullback f).obj M)⟩

end AlgebraicGeometry.Scheme.Modules
