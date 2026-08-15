/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowSupport
import MazurTorsion.Upstream.CoherentCohomologyFinite.ClosedImmersionPushforwardSupport
import MazurTorsion.Upstream.CoherentCohomologyFinite.FinitePushforwardCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationAcyclicExtensionModel
import MazurTorsion.Upstream.CoherentCohomologyFinite.RationalProjectiveCohomologyFiniteness
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeInducingOpenLift
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePushforwardMapRestrictionIso

/-!
# Chow comodels on a canonical support thickening

An acyclic extension on the Chow modification of the canonical support
thickening can be pushed through the defining closed immersion.  The
result is a coherent comodel on the original scheme, finite in
cohomology, whose comparison residuals have strictly smaller support.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace CanonicalSupportThickening

variable {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of ℚ)} [IsProper f]
  {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]

/--
Push an acyclic Chow-extension input off the canonical support
thickening to obtain the comodel required by closed-support
codévissage on the original scheme.
-/
theorem exists_chowComodel_of_acyclicExtensionInput
    (A : CanonicalSupportThickening F)
    (B :
      AcyclicExtensionModificationInput
        (A.chowModification (k := ℚ) (f := f))
        A.modelModule) :
    ∃ (E : X.Modules) (β : F ⟶ E),
      RationalSheafHFinite E ∧
      CoherentModule
        (kernel (Abelian.factorThruImage β)) ∧
      CoherentModule
        (cokernel (Abelian.image.ι β)) ∧
      (IsZero (kernel (Abelian.factorThruImage β)) ∨
        Scheme.Modules.closedStalkSupport
            (kernel (Abelian.factorThruImage β)) <
          Scheme.Modules.closedStalkSupport F) ∧
      (IsZero (cokernel (Abelian.image.ι β)) ∨
        Scheme.Modules.closedStalkSupport
            (cokernel (Abelian.image.ι β)) <
          Scheme.Modules.closedStalkSupport F) := by
  let P := A.chowModification (k := ℚ) (f := f)
  let E₀ :=
    (Scheme.Modules.pushforward P.toOriginal).obj
      B.modelModule
  let E :=
    (Scheme.Modules.pushforward A.inclusion).obj E₀
  let β₀ : A.modelModule ⟶ E₀ :=
    B.comparison
  let β : F ⟶ E :=
    A.comparisonIso.hom ≫
      (Scheme.Modules.pushforward A.inclusion).map β₀
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  letI : IsNoetherian A.supportScheme :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field
      (A.inclusion ≫ f)
  have hE₀ : CoherentModule E₀ :=
    B.pushforwardCoherent
  letI : E₀.IsFiniteType := hE₀.1
  letI : E₀.IsQuasicoherent := hE₀.2
  have hE : CoherentModule E := by
    exact
      ⟨Scheme.Modules.isFiniteType_pushforward_closedImmersion
          A.inclusion E₀,
        Scheme.Modules.isQuasicoherent_pushforward_affineHom
          A.inclusion E₀⟩
  letI : E.IsFiniteType := hE.1
  letI : E.IsQuasicoherent := hE.2
  have hresidual :
      CoherentModule
          (kernel (Abelian.factorThruImage β)) ∧
        CoherentModule
          (cokernel (Abelian.image.ι β)) :=
    AlgebraicGeometry.Scheme.Modules.comparisonResidual_isFiniteType_and_isQuasicoherent
      β
  letI :
      (kernel
        (Abelian.factorThruImage β)).IsFiniteType :=
    hresidual.1.1
  letI :
      (kernel
        (Abelian.factorThruImage β)).IsQuasicoherent :=
    hresidual.1.2
  letI :
      (cokernel
        (Abelian.image.ι β)).IsFiniteType :=
    hresidual.2.1
  letI :
      (cokernel
        (Abelian.image.ι β)).IsQuasicoherent :=
    hresidual.2.2
  have hmodel : CoherentModule A.modelModule :=
    A.modelModule_coherent
  letI : A.modelModule.IsFiniteType := hmodel.1
  letI : A.modelModule.IsQuasicoherent := hmodel.2
  have hE₀finite : RationalSheafHFinite E₀ := by
    change
      RationalSheafHFinite
        ((Scheme.Modules.pushforward P.toOriginal).obj
          B.modelModule)
    let Acyclic :=
      B.toModificationAcyclicModel
        ProjectiveSpace.coherentCohomologyFinite_rat
    exact Acyclic.pushforwardCohomologyFinite
  have hEfinite : RationalSheafHFinite E := by
    intro q
    exact
      (MazurTorsion.AlgebraicGeometry.CoherentCohomology.closedImmersion_rationalizedCohomology_finite_iff
        A.inclusion E₀ q).mp
        (hE₀finite q)
  have hsupport :
      Scheme.Modules.closedStalkSupport E ≤
        Scheme.Modules.closedStalkSupport F := by
    calc
      Scheme.Modules.closedStalkSupport E ≤
          (⟨Set.range A.inclusion,
            A.inclusion.isClosedEmbedding.isClosed_range⟩ :
            Closeds X) :=
        Scheme.Modules.closedStalkSupport_pushforward_le_range
          A.inclusion E₀
      _ = Scheme.Modules.closedStalkSupport F := by
        apply Closeds.ext
        exact A.range_inclusion
  let U := B.isomorphismOpen
  let O :=
    closedImmersionTargetOpen A.inclusion U
  haveI hβ₀preimage :
      IsIso
        ((Scheme.Modules.restrictFunctor
          (A.inclusion ⁻¹ᵁ O).ι).map β₀) := by
    rw [show A.inclusion ⁻¹ᵁ O = U by
      exact preimage_closedImmersionTargetOpen
        A.inclusion U]
    exact B.comparisonIsIsoOnOpen
  haveI hpushforwardβ₀ :
      IsIso
        ((Scheme.Modules.restrictFunctor O.ι).map
          ((Scheme.Modules.pushforward
            A.inclusion).map β₀)) :=
    Scheme.Modules.isIso_restrict_pushforward_map_of_restrict
      A.inclusion O β₀
  haveI hβopen :
      IsIso
        ((Scheme.Modules.restrictFunctor O.ι).map β) := by
    dsimp only [β]
    rw [Functor.map_comp]
    exact
      IsIso.comp_isIso'
        (inferInstanceAs
          (IsIso
            ((Scheme.Modules.restrictFunctor O.ι).map
              A.comparisonIso.hom)))
        hpushforwardβ₀
  have hdrops :
      (IsZero (kernel (Abelian.factorThruImage β)) ∨
        Scheme.Modules.closedStalkSupport
            (kernel (Abelian.factorThruImage β)) <
          Scheme.Modules.closedStalkSupport F) ∧
      (IsZero (cokernel (Abelian.image.ι β)) ∨
        Scheme.Modules.closedStalkSupport
            (cokernel (Abelian.image.ι β)) <
          Scheme.Modules.closedStalkSupport F) := by
    rcases B.sourceZeroOrSupportPoint with hzero | ⟨x, hx⟩
    · have hFzero : IsZero F := by
        apply A.comparisonIso.isZero_iff.mpr
        exact
          (Scheme.Modules.pushforward
            A.inclusion).map_isZero hzero
      have hFbot :=
        Scheme.Modules.closedStalkSupport_eq_bot_of_isZero
          F hFzero
      have hKle :
          Scheme.Modules.closedStalkSupport
              (kernel (Abelian.factorThruImage β)) ≤
            Scheme.Modules.closedStalkSupport F :=
        Scheme.Modules.closedStalkSupport_le_of_mono
          (kernel.ι (Abelian.factorThruImage β))
      have hQle :
          Scheme.Modules.closedStalkSupport
              (cokernel (Abelian.image.ι β)) ≤
            Scheme.Modules.closedStalkSupport F :=
        (Scheme.Modules.closedStalkSupport_le_of_epi
          (cokernel.π (Abelian.image.ι β))).trans hsupport
      have hKbot :
          Scheme.Modules.closedStalkSupport
              (kernel (Abelian.factorThruImage β)) = ⊥ := by
        apply le_antisymm
        · simpa [hFbot] using hKle
        · exact bot_le
      have hQbot :
          Scheme.Modules.closedStalkSupport
              (cokernel (Abelian.image.ι β)) = ⊥ := by
        apply le_antisymm
        · simpa [hFbot] using hQle
        · exact bot_le
      exact
        ⟨Or.inl
            ((AlgebraicGeometry.Scheme.Modules.isZero_iff_closedStalkSupport_eq_bot
              (kernel
                (Abelian.factorThruImage β))).mpr hKbot),
          Or.inl
            ((AlgebraicGeometry.Scheme.Modules.isZero_iff_closedStalkSupport_eq_bot
              (cokernel
                (Abelian.image.ι β))).mpr hQbot)⟩
    · let y : O :=
        ⟨A.inclusion (U.ι x),
          mem_targetOpenOfIsInducing
            A.inclusion
            A.inclusion.isClosedEmbedding.isInducing
            U (U.ι x) x.property⟩
      have hy :
          O.ι y ∈
            Scheme.Modules.closedStalkSupport F := by
        change
          A.inclusion (U.ι x) ∈
            (Scheme.Modules.closedStalkSupport F : Set X)
        rw [← A.range_inclusion]
        exact ⟨U.ι x, rfl⟩
      exact
        ⟨Or.inr
            (AlgebraicGeometry.Scheme.Modules.closedStalkSupport_kernel_factorThruImage_lt
              O.ι β y hy),
          Or.inr
            (AlgebraicGeometry.Scheme.Modules.closedStalkSupport_cokernel_image_ι_lt
              O.ι β hsupport y hy)⟩
  exact
    ⟨E, β, hEfinite, hresidual.1,
      hresidual.2, hdrops.1, hdrops.2⟩

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
