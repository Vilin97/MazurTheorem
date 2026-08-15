/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverCoversTop
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePullbackLocalPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAddCommGrpSiteInstances

/-!
# Quasicoherence under scheme-module pullback

Pull back the local presentations in quasicoherent data to their
inverse-image opens.  These opens cover the source, so quasicoherence
glues by `IsQuasicoherent.of_coversTop`.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Arbitrary scheme-module pullback preserves quasicoherence. -/
theorem isQuasicoherent_pullback
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := by
  obtain ⟨q⟩ :=
    SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData
      (M := M)
  let V : q.I → X.Opens :=
    fun i => f ⁻¹ᵁ (q.X i : Y.Opens)
  have hV :
      (Opens.grothendieckTopology X).CoversTop V :=
    TopologicalSpace.Opens.coversTop_of_iSup_eq_top V
      (f.iSup_preimage_eq_top
        ((TopologicalSpace.Opens.coversTop_iff_iSup_eq_top
          q.X).mp q.coversTop))
  letI :
      ∀ W : X.Opens,
        ((Opens.grothendieckTopology X).over W).HasSheafCompose
          (forget₂ RingCat AddCommGrpCat) :=
    fun _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafComposeAddCommGrp _
  letI :
      ∀ W : X.Opens,
        HasSheafify
          ((Opens.grothendieckTopology X).over W) AddCommGrpCat :=
    fun _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafifyAddCommGrp _
  letI :
      ∀ W : X.Opens,
        HasWeakSheafify
          ((Opens.grothendieckTopology X).over W) AddCommGrpCat :=
    fun _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasWeakSheafifyAddCommGrp _
  letI :
      ∀ W : X.Opens,
        ((Opens.grothendieckTopology X).over W)
          |>.WEqualsLocallyBijective AddCommGrpCat :=
    fun _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.wEqualsLocallyBijectiveAddCommGrp _
  letI :
      ∀ (U : X.Opens) (W : Over U),
        (((Opens.grothendieckTopology X).over
          U).over W).HasSheafCompose
            (forget₂ RingCat AddCommGrpCat) :=
    fun _ _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafComposeAddCommGrp _
  letI :
      ∀ (U : X.Opens) (W : Over U),
        HasSheafify
          (((Opens.grothendieckTopology X).over
            U).over W) AddCommGrpCat :=
    fun _ _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafifyAddCommGrp _
  letI :
      ∀ (U : X.Opens) (W : Over U),
        HasWeakSheafify
          (((Opens.grothendieckTopology X).over
            U).over W) AddCommGrpCat :=
    fun _ _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasWeakSheafifyAddCommGrp _
  letI :
      ∀ (U : X.Opens) (W : Over U),
        (((Opens.grothendieckTopology X).over
          U).over W).WEqualsLocallyBijective AddCommGrpCat :=
    fun _ _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.wEqualsLocallyBijectiveAddCommGrp _
  letI (i : q.I) :
      ((pullback f).obj M).over (V i) |>.IsQuasicoherent := by
    change
      (((pullback f).obj M).over
        (f ⁻¹ᵁ (q.X i : Y.Opens))).IsQuasicoherent
    exact
      (pullbackOverPresentation
        f (q.X i : Y.Opens) (q.presentation i)).isQuasicoherent
  exact
    SheafOfModules.IsQuasicoherent.of_coversTop
      ((pullback f).obj M) V hV

/-- Instance form of preservation of quasicoherence by pullback. -/
instance pullback_isQuasicoherent
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  isQuasicoherent_pullback f M

end AlgebraicGeometry.Scheme.Modules
