/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineKernelFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafRestrictionExactness
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeRestriction

/-!
# Finite presentations of kernels on Noetherian affine schemes

For a morphism between finite-type quasicoherent modules on a
Noetherian affine scheme, its kernel has a finite global
presentation.  On a spectrum this follows from finite generation of
kernel sections and affine tilde reconstruction.  The general affine
case is transported across the canonical isomorphism with its
spectrum.
-/


universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

private theorem presentationOfIsIso_isFinite
    {Y : Scheme.{u}} {M N : Y.Modules}
    (f : M ⟶ N) [hf : IsIso f]
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
The kernel of a morphism between finite-type quasicoherent modules on
a Noetherian spectrum has a finite global presentation.
-/
theorem existsFinitePresentation_kernel_spec
    {R : CommRingCat.{u}} [IsNoetherianRing (R : Type u)]
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsFiniteType] [N.IsFiniteType]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  letI : (kernel f).IsQuasicoherent :=
    isQuasicoherent_kernel_coherentCohomology f
  exact
    exists_finite_presentation_of_finite_sections
      (kernel f) (finiteTopSections_kernel f)

variable {X : Scheme.{u}}

/--
The kernel of a morphism between finite-type quasicoherent modules on
a Noetherian affine scheme has a finite global presentation.
-/
theorem existsFinitePresentation_kernel_affine
    [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsFiniteType] [N.IsFiniteType]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  let fSpec :=
    (restrictFunctor X.isoSpec.inv).map f
  haveI :
      ((restrictFunctor X.isoSpec.inv).obj M).IsFiniteType :=
    inferInstance
  haveI :
      ((restrictFunctor X.isoSpec.inv).obj N).IsFiniteType :=
    inferInstance
  haveI :
      ((restrictFunctor X.isoSpec.inv).obj M).IsQuasicoherent :=
    inferInstance
  haveI :
      ((restrictFunctor X.isoSpec.inv).obj N).IsQuasicoherent :=
    inferInstance
  obtain ⟨P, hP⟩ :=
    existsFinitePresentation_kernel_spec fSpec
  letI : P.IsFinite := hP
  let eKernel :
      (kernel f).restrict X.isoSpec.inv ≅ kernel fSpec :=
    PreservesKernel.iso (restrictFunctor X.isoSpec.inv) f
  letI : IsIso eKernel.inv := eKernel.isIso_inv
  let P' :
      ((kernel f).restrict X.isoSpec.inv).Presentation :=
    @SheafOfModules.Presentation.ofIsIso.{u}
      _ _ _ _ _ _ _ _ eKernel.inv eKernel.isIso_inv P
  letI : P'.IsFinite := by
    dsimp only [P']
    exact presentationOfIsIso_isFinite eKernel.inv P
  let P'' :
      (((kernel f).restrict X.isoSpec.inv).restrict
        X.isoSpec.hom).Presentation :=
    Presentation.restrict X.isoSpec.hom P'
  let eCancel :
      ((kernel f).restrict X.isoSpec.inv).restrict
          X.isoSpec.hom ≅ kernel f :=
    restrictIsoOfIso X.isoSpec (kernel f)
  letI : IsIso eCancel.hom := eCancel.isIso_hom
  letI : P''.IsFinite := by
    dsimp only [P'']
    infer_instance
  let P''' : (kernel f).Presentation :=
    @SheafOfModules.Presentation.ofIsIso.{u}
      _ _ _ _ _ _ _ _ eCancel.hom eCancel.isIso_hom P''
  exact ⟨P''', by
    dsimp only [P''']
    exact presentationOfIsIso_isFinite eCancel.hom P''⟩

end AlgebraicGeometry.Scheme.Modules
