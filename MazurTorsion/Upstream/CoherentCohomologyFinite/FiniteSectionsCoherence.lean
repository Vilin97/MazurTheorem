/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFinitePresentationFromSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenRestrictionFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFinitePresentationLocal
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A finite-section criterion for coherent module sheaves

On a locally Noetherian scheme, a quasicoherent module is finitely
presented if its sections over every affine open are finite.  The proof
constructs finite presentations on the affine-open restrictions and
assembles them using the standard affine cover.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/--
A quasicoherent module on a locally Noetherian scheme with finite
sections on every affine open is finitely presented.
-/
theorem isFinitePresentation_of_finiteAffineSections
    [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent]
    (hfin :
      ∀ U : X.Opens, IsAffineOpen U →
        Module.Finite Γ(X, U) Γ(M, U)) :
    M.IsFinitePresentation := by
  have hP (U : X.affineOpens) :
      ∃ P :
          (M.restrict (U : X.Opens).ι).Presentation,
        P.IsFinite := by
    letI : IsNoetherianRing Γ(U, ⊤) :=
      IsLocallyNoetherian.component_noetherian
        ⟨⊤, isAffineOpen_top U⟩
    have himage :
        (U : X.Opens).ι ''ᵁ
            (⊤ : (↑(U : X.Opens) : Scheme.{u}).Opens) =
          (U : X.Opens) := by
      rw [(U : X.Opens).ι.image_top_eq_opensRange,
        Scheme.Opens.opensRange_ι]
    have hImage :
        Module.Finite
          Γ(X, (U : X.Opens).ι ''ᵁ
            (⊤ : (↑(U : X.Opens) : Scheme.{u}).Opens))
          Γ(M, (U : X.Opens).ι ''ᵁ
            (⊤ : (↑(U : X.Opens) : Scheme.{u}).Opens)) := by
      rw [himage]
      exact hfin (U : X.Opens) U.2
    have htop :
        Module.Finite Γ(U, ⊤)
          Γ(M.restrict (U : X.Opens).ι, ⊤) :=
      finiteRestrictSections_of_finiteImageSections
        (U : X.Opens).ι M
          (⊤ : (↑(U : X.Opens) : Scheme.{u}).Opens)
          hImage
    exact
      existsFinitePresentation_of_affine_of_finiteTopSections
        (M.restrict (U : X.Opens).ι) htop
  let P :
      ∀ U : X.affineOpens,
        (M.restrict (U : X.Opens).ι).Presentation :=
    fun U => (hP U).choose
  letI : ∀ U, (P U).IsFinite :=
    fun U => (hP U).choose_spec
  exact
    isFinitePresentation_of_affineOpenPresentations M P

end AlgebraicGeometry.Scheme.Modules
