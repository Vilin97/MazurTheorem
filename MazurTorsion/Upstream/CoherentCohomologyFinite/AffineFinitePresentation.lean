/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.PresentationFiniteMap

/-!
# Finite presentations on a Noetherian affine scheme

Combining finite generation of affine global sections with Noetherian
commutative algebra gives a finite global presentation, hence a finite
presentation in the local sheaf-theoretic sense.
-/

open CategoryTheory Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- A finite-type quasicoherent module sheaf on a Noetherian affine scheme
admits a finite global presentation. -/
theorem exists_finite_presentation_of_isFiniteType_isQuasicoherent
    [IsNoetherianRing (R : Type u)]
    (F : (Spec R).Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ P : F.Presentation, P.IsFinite :=
  exists_finite_presentation_of_finite_sections F
    (finite_top_sections_of_isFiniteType_isQuasicoherent F)

/-- A finite global presentation induces finite-presentation data on the
trivial open cover. -/
theorem isFinitePresentation_of_finite_presentation
    (F : (Spec R).Modules)
    (P : F.Presentation) [P.IsFinite] :
    SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  refine SheafOfModules.IsFinitePresentation.mk (M := F) ?_
  refine ⟨P.quasicoherentData, { isFinite_presentation := ?_ }⟩
  intro i
  change (Spec R).Opens at i
  letI :
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward
          (𝟙 ((Spec R).ringCatSheaf.over i))) :=
    (SheafOfModules.overPushforwardOverAdj
      (R := (Spec R).ringCatSheaf) i).leftAdjoint_preservesColimits
  change
    (P.map
      (SheafOfModules.pushforward
        (𝟙 ((Spec R).ringCatSheaf.over i)))
      (Iso.refl _)).IsFinite
  exact SheafOfModules.Presentation.map_isFinite
    P
    (SheafOfModules.pushforward
      (𝟙 ((Spec R).ringCatSheaf.over i)))
    (Iso.refl _)

/-- Over a Noetherian ring, every finite-type quasicoherent module sheaf on
the affine spectrum is of finite presentation. -/
theorem isFinitePresentation_of_isFiniteType_isQuasicoherent
    [IsNoetherianRing (R : Type u)]
    (F : (Spec R).Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentation.{u, u, u} F := by
  obtain ⟨P, hP⟩ :=
    exists_finite_presentation_of_isFiniteType_isQuasicoherent F
  letI : P.IsFinite := hP
  exact isFinitePresentation_of_finite_presentation F P

end AlgebraicGeometry.Scheme.Modules
