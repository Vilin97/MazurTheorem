/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineKernelFinitePresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFinitePresentationLocal
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Kernels of coherent module sheaves

On a locally Noetherian scheme, kernels of morphisms between
finite-type quasicoherent module sheaves are finitely presented.  The
proof is local on affine opens: exactness of restriction identifies
the restricted kernel with the kernel of the restricted morphism, and
Noetherian affine algebra supplies a finite global presentation.
-/


universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/--
On a locally Noetherian scheme, the kernel of a morphism between
finite-type quasicoherent modules is finitely presented.
-/
theorem isFinitePresentation_kernel
    [IsLocallyNoetherian X]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsFiniteType] [N.IsFiniteType]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsFinitePresentation := by
  have hPresentation (U : X.affineOpens) :
      ∃ P :
          ((kernel f).restrict (U : X.Opens).ι).Presentation,
        P.IsFinite := by
    let fU :=
      (restrictFunctor (U : X.Opens).ι).map f
    haveI :
        ((restrictFunctor
          (U : X.Opens).ι).obj M).IsFiniteType :=
      inferInstance
    haveI :
        ((restrictFunctor
          (U : X.Opens).ι).obj N).IsFiniteType :=
      inferInstance
    haveI :
        ((restrictFunctor
          (U : X.Opens).ι).obj M).IsQuasicoherent :=
      inferInstance
    haveI :
        ((restrictFunctor
          (U : X.Opens).ι).obj N).IsQuasicoherent :=
      inferInstance
    letI : IsNoetherianRing Γ(U, ⊤) :=
      IsLocallyNoetherian.component_noetherian
        ⟨⊤, isAffineOpen_top U⟩
    obtain ⟨P, hP⟩ :=
      existsFinitePresentation_kernel_affine fU
    letI : P.IsFinite := hP
    let eKernel :
        (kernel f).restrict (U : X.Opens).ι ≅
          kernel fU :=
      PreservesKernel.iso
        (restrictFunctor (U : X.Opens).ι) f
    letI : IsIso eKernel.inv := eKernel.isIso_inv
    let P' :
        ((kernel f).restrict
          (U : X.Opens).ι).Presentation :=
      @SheafOfModules.Presentation.ofIsIso.{u}
        _ _ _ _ _ _ _ _ eKernel.inv eKernel.isIso_inv P
    have hP' : P'.IsFinite := by
      dsimp only [P']
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
    exact ⟨P', hP'⟩
  let P :
      ∀ U : X.affineOpens,
        ((kernel f).restrict
          (U : X.Opens).ι).Presentation :=
    fun U => (hPresentation U).choose
  letI : ∀ U, (P U).IsFinite :=
    fun U => (hPresentation U).choose_spec
  exact
    isFinitePresentation_of_affineOpenPresentations
      (kernel f) P

/--
The kernel in the preceding theorem is again finite-type and
quasicoherent; these instances are consequences of its finite
presentation.
-/
theorem kernel_isFiniteType_and_isQuasicoherent
    [IsLocallyNoetherian X]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsFiniteType] [N.IsFiniteType]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsFiniteType ∧
      (kernel f).IsQuasicoherent := by
  letI : SheafOfModules.IsFinitePresentation.{u, u, u} (kernel f) :=
    isFinitePresentation_kernel f
  exact
    ⟨SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (kernel f),
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (kernel f)⟩

end AlgebraicGeometry.Scheme.Modules
