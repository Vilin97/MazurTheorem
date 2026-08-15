/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SemilinearFiniteTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafPresentationRestriction

/-!
# Finite presentations from finite sections on an affine scheme

The affine coherence engine is stated for a spectrum.  This file
transports it across the canonical isomorphism from an arbitrary affine
scheme to the spectrum of its global functions.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/--
A quasicoherent module on a Noetherian affine scheme whose global
sections are finite admits a finite global presentation.
-/
theorem existsFinitePresentation_of_affine_of_finiteTopSections
    [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (M : X.Modules) [M.IsQuasicoherent]
    (hfin : Module.Finite Γ(X, ⊤) Γ(M, ⊤)) :
    ∃ P : M.Presentation, P.IsFinite := by
  let N : (Spec Γ(X, ⊤)).Modules :=
    M.restrict X.isoSpec.inv
  haveI : N.IsQuasicoherent := inferInstance
  have himage :
      X.isoSpec.inv ''ᵁ
          (⊤ : (Spec Γ(X, ⊤)).Opens) =
        (⊤ : X.Opens) := by
    rw [X.isoSpec.inv.image_top_eq_opensRange,
      X.isoSpec.inv.opensRange_of_isIso]
  have hfinImage := hfin
  rw [← himage] at hfinImage
  let σ :
      (Γ(X, ⊤) : Type u) →+*
        Γ(X, X.isoSpec.inv ''ᵁ
          (⊤ : (Spec Γ(X, ⊤)).Opens)) :=
    ((Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫
      (X.isoSpec.inv.appIso
        (⊤ : (Spec Γ(X, ⊤)).Opens)).inv).hom
  have hσ : Function.Surjective σ := by
    intro z
    refine
      ⟨(Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom
          ((X.isoSpec.inv.appIso
            (⊤ : (Spec Γ(X, ⊤)).Opens)).hom.hom z),
        ?_⟩
    simp [σ]
  let e :
      (Γ(N, ⊤) : Type u) ≃+
        Γ(M, X.isoSpec.inv ''ᵁ
          (⊤ : (Spec Γ(X, ⊤)).Opens)) :=
    (M.restrictAppIso X.isoSpec.inv
      (⊤ : (Spec Γ(X, ⊤)).Opens)).addCommGroupIsoToAddEquiv
  have hfinN : Module.Finite Γ(X, ⊤) Γ(N, ⊤) := by
    refine
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.Module.Finite.of_surjectiveSemilinearAddEquiv
        σ hσ e ?_ hfinImage
    intro r x
    change
      (M.restrictAppIso X.isoSpec.inv
        (⊤ : (Spec Γ(X, ⊤)).Opens)).hom.hom
          (r • x) =
        σ r •
          (M.restrictAppIso X.isoSpec.inv
            (⊤ : (Spec Γ(X, ⊤)).Opens)).hom.hom x
    rw [Scheme.Modules.smul_Spec_def]
    rfl
  obtain ⟨P, hP⟩ :=
    exists_finite_presentation_of_finite_sections N hfinN
  letI : P.IsFinite := hP
  let P' :
      ((M.restrict X.isoSpec.inv).restrict
        X.isoSpec.hom).Presentation :=
    Presentation.restrict X.isoSpec.hom P
  let hP' : P'.IsFinite := by
    dsimp only [P']
    infer_instance
  let e :
      (M.restrict X.isoSpec.inv).restrict
          X.isoSpec.hom ≅ M :=
    restrictIsoOfIso X.isoSpec M
  let P'' : M.Presentation :=
    @SheafOfModules.Presentation.ofIsIso.{u}
      _ _ _ _ _ _ _ _ e.hom e.isIso_hom P'
  have hP'' : P''.IsFinite := by
    refine SheafOfModules.Presentation.IsFinite.mk ?_ ?_
    · constructor
      dsimp only [P'', SheafOfModules.Presentation.ofIsIso,
        SheafOfModules.GeneratingSections.ofEpi]
      change Finite P'.generators.I
      exact hP'.isFiniteType_generators.finite
    · constructor
      dsimp only [P'', SheafOfModules.Presentation.ofIsIso,
        SheafOfModules.GeneratingSections.ofEpi]
      change Finite P'.relations.I
      exact hP'.isFiniteType_relations.finite
  exact ⟨P'', hP''⟩

end AlgebraicGeometry.Scheme.Modules
