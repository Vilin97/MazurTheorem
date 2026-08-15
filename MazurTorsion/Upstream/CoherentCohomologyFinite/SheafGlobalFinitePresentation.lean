/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFinitePresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFinitePresentationLocal
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafPresentationRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Coherence of finite-type quasicoherent sheaves

On a Noetherian affine scheme, a finite-type quasicoherent module has
a finite global presentation.  Restricting along the canonical
isomorphism with a spectrum gives the affine statement, and applying
it to every affine open gives finite-presentation data on a locally
Noetherian scheme.
-/


universe u

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private theorem presentationOfIsIso_isFinite
    {M N : X.Modules} (f : M ⟶ N) [hf : IsIso f]
    (P : M.Presentation) [P.IsFinite] :
    (@SheafOfModules.Presentation.ofIsIso.{u}
      _ _ _ _ _ _ _ _ f hf P).IsFinite := by
  constructor
  · constructor
    change Finite P.generators.I
    exact
      (SheafOfModules.Presentation.IsFinite.isFiniteType_generators
        (p := P)).finite
  · constructor
    change Finite P.relations.I
    exact
      (SheafOfModules.Presentation.IsFinite.isFiniteType_relations
        (p := P)).finite

/--
A finite-type quasicoherent module on a Noetherian affine scheme has a
finite global presentation.
-/
theorem existsFinitePresentation_of_affine
    [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    ∃ P : M.Presentation, P.IsFinite := by
  let N : (Spec Γ(X, ⊤)).Modules :=
    M.restrict X.isoSpec.inv
  haveI : N.IsFiniteType := inferInstance
  haveI : N.IsQuasicoherent := inferInstance
  obtain ⟨P, hP⟩ :=
    exists_finite_presentation_of_isFiniteType_isQuasicoherent N
  letI : P.IsFinite := hP
  let P' :
      ((M.restrict X.isoSpec.inv).restrict
        X.isoSpec.hom).Presentation :=
    Presentation.restrict X.isoSpec.hom P
  let e :
      (M.restrict X.isoSpec.inv).restrict
          X.isoSpec.hom ≅ M :=
    restrictIsoOfIso X.isoSpec M
  letI : IsIso e.hom := e.isIso_hom
  letI : P'.IsFinite := by
    dsimp only [P']
    infer_instance
  let P'' : M.Presentation :=
    @SheafOfModules.Presentation.ofIsIso.{u}
      _ _ _ _ _ _ _ _ e.hom e.isIso_hom P'
  exact ⟨P'', by
    dsimp only [P'']
    exact presentationOfIsIso_isFinite e.hom P'⟩

/--
On a locally Noetherian scheme, every finite-type quasicoherent module
is finitely presented.
-/
theorem isFinitePresentation_of_isLocallyNoetherian
    [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    M.IsFinitePresentation := by
  have hP (U : X.affineOpens) :
      ∃ P :
          (M.restrict (U : X.Opens).ι).Presentation,
        P.IsFinite := by
    letI : IsNoetherianRing Γ(U, ⊤) :=
      IsLocallyNoetherian.component_noetherian
        ⟨⊤, isAffineOpen_top U⟩
    exact
      existsFinitePresentation_of_affine
        (M.restrict (U : X.Opens).ι)
  let P :
      ∀ U : X.affineOpens,
        (M.restrict (U : X.Opens).ι).Presentation :=
    fun U => (hP U).choose
  letI : ∀ U, (P U).IsFinite :=
    fun U => (hP U).choose_spec
  exact
    isFinitePresentation_of_affineOpenPresentations M P

end AlgebraicGeometry.Scheme.Modules
