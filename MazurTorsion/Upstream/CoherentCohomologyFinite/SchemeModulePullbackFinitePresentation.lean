/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePullbackQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFinitePresentationCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFinitePresentationFromGlobal

/-!
# Finite presentation under scheme-module pullback

The local presentations constructed for pullback preserve their
generator and relation index types at every transport step.  Thus
finite quasicoherent presentation data, and hence finite presentation
of a module sheaf, is preserved by arbitrary scheme morphisms.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}

/-- Finiteness of a presentation survives local pullback and the open
base-change isomorphism. -/
instance pullbackRestrictionPresentation_isFinite
    (U : Y.Opens)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    (pullbackRestrictionPresentation f U P).IsFinite := by
  let Plocal :=
    Presentation.pullback (f ∣_ U) P
  let hPlocal : Plocal.IsFinite :=
    Presentation.pullback_isFinite (f ∣_ U) P
  change
    (@SheafOfModules.Presentation.ofIsIso
      _ _ _ _ _ _ _ _
      ((pullbackRestrictBaseChangeIso f U).app M).hom
      ((pullbackRestrictBaseChangeIso f U).app M).isIso_hom
      Plocal).IsFinite
  constructor
  · constructor
    dsimp only [SheafOfModules.Presentation.ofIsIso,
      SheafOfModules.GeneratingSections.ofEpi]
    change Finite Plocal.generators.I
    exact hPlocal.isFiniteType_generators.finite
  · constructor
    dsimp only [SheafOfModules.Presentation.ofIsIso,
      SheafOfModules.GeneratingSections.ofEpi]
    change Finite Plocal.relations.I
    exact hPlocal.isFiniteType_relations.finite

/--
The complete presentation transported from a target slice site to its
inverse-image slice site is finite.
-/
theorem pullbackOverPresentation_isFinite
    (U : Y.Opens) (P : (M.over U).Presentation)
    (hP : P.IsFinite) :
    (pullbackOverPresentation f U P).IsFinite := by
  letI : P.IsFinite := hP
  let Ptarget :=
    Presentation.restrictOfOver U M P
  letI : Ptarget.IsFinite :=
    Presentation.restrictOfOver_isFinite U M P
  let Prestrict :=
    pullbackRestrictionPresentation f U Ptarget
  letI : Prestrict.IsFinite :=
    pullbackRestrictionPresentation_isFinite f U Ptarget
  change
    (Presentation.overOfRestrict
      (f ⁻¹ᵁ U) ((pullback f).obj M) Prestrict).IsFinite
  exact
    Presentation.overOfRestrict_isFinite
      (f ⁻¹ᵁ U) ((pullback f).obj M) Prestrict

/-- Arbitrary scheme-module pullback preserves finite presentation. -/
theorem isFinitePresentation_pullback
    (M : Y.Modules) [M.IsFinitePresentation] :
    ((pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ :=
    SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  letI : q.IsFinitePresentation := hq
  let V : q.I → X.Opens :=
    fun i => f ⁻¹ᵁ (q.X i : Y.Opens)
  have hV :
      (Opens.grothendieckTopology X).CoversTop V :=
    TopologicalSpace.Opens.coversTop_of_iSup_eq_top V
      (f.iSup_preimage_eq_top
        ((TopologicalSpace.Opens.coversTop_iff_iSup_eq_top
          q.X).mp q.coversTop))
  apply
    isFinitePresentation_of_coversTop
      ((pullback f).obj M) V hV
  intro i
  letI :
      HasSheafify
        ((Opens.grothendieckTopology X).over (V i))
        AddCommGrpCat :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafifyAddCommGrp _
  letI :
      HasWeakSheafify
        ((Opens.grothendieckTopology X).over (V i))
        AddCommGrpCat :=
    HasSheafify.isRightAdjoint
  letI :
      ((Opens.grothendieckTopology X).over (V i))
        |>.WEqualsLocallyBijective AddCommGrpCat :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.wEqualsLocallyBijectiveAddCommGrp _
  letI :
      ((Opens.grothendieckTopology X).over (V i))
        |>.HasSheafCompose
          (forget₂ RingCat AddCommGrpCat) :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafComposeAddCommGrp _
  let P :=
    pullbackOverPresentation
      f (q.X i : Y.Opens) (q.presentation i)
  have hP : P.IsFinite :=
    pullbackOverPresentation_isFinite
      f (q.X i : Y.Opens) (q.presentation i)
      (SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation i)
  exact
    SheafOfModules.Presentation.isFinitePresentation
      (C := Over (V i)) P hP

/-- Instance form of preservation of finite presentation by pullback. -/
instance pullback_isFinitePresentation
    (M : Y.Modules) [M.IsFinitePresentation] :
    ((pullback f).obj M).IsFinitePresentation :=
  isFinitePresentation_pullback f M

end AlgebraicGeometry.Scheme.Modules
