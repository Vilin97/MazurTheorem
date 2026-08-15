/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowPositiveTwist
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationPositiveTwistInput
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreLeray
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleRestrictionIsoMonotone

/-!
# Acyclic positive twists on the canonical Chow modification

The three geometric inputs are kept explicit here:

* compatibility of relative twists with affine restriction;
* compatibility with pushforward along the local closed embedding;
* a coordinate map which is invertible on its selected projective chart.

Relative Serre vanishing supplies one sufficiently positive degree, and
the finite-cover Leray comparison then completes the acyclic-extension
input.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace CanonicalSupportThickening

open ProjectiveSpace
open ProjectiveSpace.IsRelativeProjectiveFactorization
open ProjectiveSpace.SerreTwist

noncomputable local instance chowPositiveTwistInputSheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

variable {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of ℚ)} [IsProper f]
  {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]

/--
Relative Serre compatibility and one standard coordinate map in every
positive degree produce an acyclic positive-twist extension on the
canonical Chow modification.
-/
theorem nonempty_chowPositiveTwistAcyclicExtensionInput
    (A : CanonicalSupportThickening F)
    (hrestrict :
      let P := A.chowModification (k := ℚ) (f := f)
      P.relativeProjective.AffineRestrictionTwistCompatible
        ((Scheme.Modules.pullback P.toOriginal).obj
          A.modelModule))
    (hpushforward :
      let P := A.chowModification (k := ℚ) (f := f)
      P.relativeProjective.AffineTwistPushforwardCompatible)
    (hcoordinate :
      let P := A.chowModification (k := ℚ) (f := f)
      let N₀ :=
        (Scheme.Modules.pullback P.toOriginal).obj
          A.modelModule
      ∀ (n : ℕ)
        (r : Fin
          (P.relativeProjective.chosenDimension + 1)),
        ∃ α :
            N₀ ⟶ P.serreTwistModule (n : ℤ) N₀,
          IsIso
            ((Scheme.Modules.restrictFunctor
              (P.relativeProjective.chosenProjectiveMap ⁻¹ᵁ
                standardChart ℚ r).ι).map α)) :
    Nonempty
      (AcyclicExtensionModificationInput
        (A.chowModification (k := ℚ) (f := f))
        A.modelModule) := by
  dsimp only at hrestrict hpushforward hcoordinate ⊢
  let P := A.chowModification (k := ℚ) (f := f)
  let N₀ :=
    (Scheme.Modules.pullback P.toOriginal).obj
      A.modelModule
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  letI : IsNoetherian A.supportScheme :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field
      (A.inclusion ≫ f)
  letI : A.supportScheme.IsSeparated :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.schemeIsSeparated_of_isProper_to_field
      (A.inclusion ≫ f)
  have hpullback : CoherentModule N₀ :=
    A.chowPullback_coherent (f := f)
  letI : N₀.IsFiniteType := hpullback.1
  letI : N₀.IsQuasicoherent := hpullback.2
  obtain ⟨b, hb⟩ :=
    ProjectiveSpace.IsRelativeProjectiveFactorization.eventually_relativeProjectiveSerreTwist_pushforwardHAddEquiv
      P.relativeProjective N₀ hrestrict hpushforward
  let C :=
    A.comparisonProjectiveChart (f := f)
  obtain ⟨α, hαchart⟩ :=
    hcoordinate b C.coordinate
  letI hαchartInstance :
      IsIso
        ((Scheme.Modules.restrictFunctor
          (P.relativeProjective.chosenProjectiveMap ⁻¹ᵁ
            standardChart ℚ C.coordinate).ι).map α) :=
    hαchart
  have hαopen :
      IsIso
        ((Scheme.Modules.restrictFunctor
          (P.toOriginal ⁻¹ᵁ C.openSubscheme).ι).map α) :=
    Scheme.Modules.isIso_restrict_map_of_le
      α C.preimage_le_standardChart
  have hcohomology :
      ∀ q : ℕ,
        ((Scheme.Modules.pushforward P.toOriginal).obj
          (P.serreTwistModule (b : ℤ) N₀)).sheaf.H q ≃+
          (P.serreTwistModule (b : ℤ) N₀).sheaf.H q :=
    fun q => Classical.choice (hb b le_rfl q)
  have hsupport :
      Scheme.Modules.closedStalkSupport
          ((Scheme.Modules.pushforward P.toOriginal).obj
            (P.serreTwistModule (b : ℤ) N₀)) ≤
        Scheme.Modules.closedStalkSupport A.modelModule := by
    rw [A.modelModule_closedStalkSupport_eq_top]
    exact le_top
  exact
    ⟨P.positiveTwistAcyclicExtensionInput
      A.modelModule C b α hpullback hcohomology
      hαopen hsupport⟩

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
