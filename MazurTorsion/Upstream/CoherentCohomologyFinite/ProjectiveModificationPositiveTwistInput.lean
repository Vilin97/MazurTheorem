/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationAcyclicExtensionModel
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationSerreTwist
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationSupportChart
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectivePushforwardCoherenceUnconditional
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenUnitBaseChangeIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePushforwardMapRestrictionIso

/-!
# Positive twists as modification inputs

This file packages the formal assembly step after relative Serre
vanishing.  A morphism from the raw pullback to a positive twist,
invertible over a support-adapted isomorphism open, produces the required
comparison with the direct image.  Coherence and the open-local
isomorphism fields are then automatic.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace ProjectiveModification

open ProjectiveSpace

noncomputable local instance positiveTwistInputSheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

variable
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)}

/--
Assemble an acyclic-extension input from a coherent positive twist and
its Leray comparison.
-/
noncomputable def positiveTwistAcyclicExtensionInput
    [IsLocallyNoetherian X]
    (P : ProjectiveModification f)
    (M : X.Modules)
    (C : ComparisonProjectiveChart P M)
    (n : ℕ)
    (α :
      (Scheme.Modules.pullback P.toOriginal).obj M ⟶
        P.serreTwistModule (n : ℤ)
          ((Scheme.Modules.pullback P.toOriginal).obj M))
    (hpullback :
      CoherentModule
        ((Scheme.Modules.pullback P.toOriginal).obj M))
    (hcohomology :
      ∀ q : ℕ,
        ((Scheme.Modules.pushforward P.toOriginal).obj
          (P.serreTwistModule (n : ℤ)
            ((Scheme.Modules.pullback P.toOriginal).obj M))).sheaf.H q ≃+
          (P.serreTwistModule (n : ℤ)
            ((Scheme.Modules.pullback P.toOriginal).obj M)).sheaf.H q)
    (hα :
      IsIso
        ((Scheme.Modules.restrictFunctor
          (P.toOriginal ⁻¹ᵁ C.openSubscheme).ι).map α))
    (hsupport :
      Scheme.Modules.closedStalkSupport
          ((Scheme.Modules.pushforward P.toOriginal).obj
            (P.serreTwistModule (n : ℤ)
              ((Scheme.Modules.pullback P.toOriginal).obj M))) ≤
        Scheme.Modules.closedStalkSupport M) :
    AcyclicExtensionModificationInput P M := by
  let N₀ :=
    (Scheme.Modules.pullback P.toOriginal).obj M
  let N := P.serreTwistModule (n : ℤ) N₀
  have hN : CoherentModule N :=
    P.serreTwistModule_coherent
      (n : ℤ) N₀ hpullback
  letI : N.IsFiniteType := hN.1
  letI : N.IsQuasicoherent := hN.2
  have hpushforward :
      CoherentModule
        ((Scheme.Modules.pushforward P.toOriginal).obj N) :=
    pushforward_coherent_of_relativeProjectiveFactorization
      P.relativeProjective N
  letI :
      IsIso
        (P.toOriginal ∣_ C.openSubscheme) :=
    C.restrictedMorphismIsIso
  let hcomparison :
      M ⟶
        (Scheme.Modules.pushforward P.toOriginal).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      P.toOriginal).unit.app M ≫
      (Scheme.Modules.pushforward P.toOriginal).map α
  haveI hunit :
      IsIso
        ((Scheme.Modules.restrictFunctor
          C.openSubscheme.ι).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              P.toOriginal).unit.app M)) :=
    AlgebraicGeometry.Scheme.Modules.isIso_restrict_pullbackPushforward_unit_of_isIso_morphismRestrict
      P.toOriginal C.openSubscheme M
  haveI hpushforwardMap :
      IsIso
        ((Scheme.Modules.restrictFunctor
          C.openSubscheme.ι).map
            ((Scheme.Modules.pushforward
              P.toOriginal).map α)) :=
    AlgebraicGeometry.Scheme.Modules.isIso_restrict_pushforward_map_of_restrict
      P.toOriginal C.openSubscheme α
  haveI hcomparisonOpen :
      IsIso
        ((Scheme.Modules.restrictFunctor
          C.openSubscheme.ι).map hcomparison) := by
    dsimp only [hcomparison]
    rw [Functor.map_comp]
    exact IsIso.comp_isIso' hunit hpushforwardMap
  exact
    { modelModule := N
      modelCoherent := hN
      comparison := hcomparison
      pushforwardCoherent := hpushforward
      cohomologyComparison := hcohomology
      isomorphismOpen := C.openSubscheme
      restrictedMorphismIsIso :=
        C.restrictedMorphismIsIso
      comparisonIsIsoOnOpen := hcomparisonOpen
      pushforwardSupport_le := hsupport
      sourceZeroOrSupportPoint :=
        C.sourceZeroOrSupportPoint }

end ProjectiveModification
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
