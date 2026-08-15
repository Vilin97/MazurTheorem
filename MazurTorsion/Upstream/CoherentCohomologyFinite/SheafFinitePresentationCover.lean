/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAddCommGrpSiteInstances

/-!
# Finite presentation on an open cover

Mathlib's `QuasicoherentData.bind` glues quasicoherent presentation data
from a cover.  Its presentation transports do not change the generator
or relation index types, so finite local data glue to finite global data.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- A presentation is finite once its two index types are finite. -/
theorem Presentation.isFinite_of_finite_indices
    {N : SheafOfModules.{u} R} (P : N.Presentation)
    (hgenerators : Finite P.generators.I)
    (hrelations : Finite P.relations.I) :
    P.IsFinite := by
  constructor
  · exact GeneratingSections.IsFiniteType.mk hgenerators
  · exact GeneratingSections.IsFiniteType.mk hrelations

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/--
The presentation used when binding local quasicoherent data.  Naming
this transport separately keeps its unchanged index types visible to
the elaborator.
-/
noncomputable def finiteBindPresentation
    {I : Type u} (U : I → X.Opens)
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).HasSheafCompose
        (forget₂ RingCat AddCommGrpCat)]
    [∀ V : X.Opens,
      HasSheafify
        ((Opens.grothendieckTopology X).over V) AddCommGrpCat]
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
        AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).HasSheafCompose
          (forget₂ RingCat AddCommGrpCat)]
    [∀ i (W : Over (U i)),
      HasSheafify
        (((Opens.grothendieckTopology X).over
          (U i)).over W) AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).WEqualsLocallyBijective AddCommGrpCat]
    (D : ∀ i, (M.over (U i)).QuasicoherentData)
    (ij : (i : I) × (D i).I) :
    (M.over ((D ij.1).X ij.2).left).Presentation :=
  letI e :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (Over.iteratedSliceEquiv ((D ij.1).X ij.2))
      (S := (X.ringCatSheaf.over (U ij.1)).over _)
      (R := X.ringCatSheaf.over _)
      (𝟙 _) (𝟙 _)
      (by ext : 2; exact X.ringCatSheaf.1.map_id _)
      (by ext : 2; exact X.ringCatSheaf.1.map_id _)
  ((((D ij.1).presentation ij.2).map e.inverse (.refl _)).ofIsIso
    (e.fullyFaithfulFunctor.preimageIso
      (by
        exact
          e.counitIso.app
            ((M.over (U ij.1)).over
              ((D ij.1).X ij.2)))).hom)

/-- The bound presentation is finite when the corresponding local
presentation is finite. -/
theorem finiteBindPresentation_isFinite
    {I : Type u} (U : I → X.Opens)
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).HasSheafCompose
        (forget₂ RingCat AddCommGrpCat)]
    [∀ V : X.Opens,
      HasSheafify
        ((Opens.grothendieckTopology X).over V) AddCommGrpCat]
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
        AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).HasSheafCompose
          (forget₂ RingCat AddCommGrpCat)]
    [∀ i (W : Over (U i)),
      HasSheafify
        (((Opens.grothendieckTopology X).over
          (U i)).over W) AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).WEqualsLocallyBijective AddCommGrpCat]
    (D : ∀ i, (M.over (U i)).QuasicoherentData)
    (hD : ∀ i, (D i).IsFinitePresentation)
    (ij : (i : I) × (D i).I) :
    (finiteBindPresentation M U D ij).IsFinite := by
  have hP :=
    (hD ij.1).isFinite_presentation ij.2
  apply
    SheafOfModules.Presentation.isFinite_of_finite_indices
  · rw [show
      (finiteBindPresentation M U D ij).generators.I =
        ((D ij.1).presentation ij.2).generators.I from rfl]
    exact hP.isFiniteType_generators.finite
  · rw [show
      (finiteBindPresentation M U D ij).relations.I =
        ((D ij.1).presentation ij.2).relations.I from rfl]
    exact hP.isFiniteType_relations.finite

/-- Bind local quasicoherent data while retaining a named presentation
transport. -/
noncomputable def finiteBindQuasicoherentData
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).HasSheafCompose
        (forget₂ RingCat AddCommGrpCat)]
    [∀ V : X.Opens,
      HasSheafify
        ((Opens.grothendieckTopology X).over V) AddCommGrpCat]
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
        AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).HasSheafCompose
          (forget₂ RingCat AddCommGrpCat)]
    [∀ i (W : Over (U i)),
      HasSheafify
        (((Opens.grothendieckTopology X).over
          (U i)).over W) AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).WEqualsLocallyBijective AddCommGrpCat]
    (D : ∀ i, (M.over (U i)).QuasicoherentData) :
    M.QuasicoherentData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hU.over (fun i => (D i).coversTop)
  presentation ij := finiteBindPresentation M U D ij

/-- The named binding of finite local data has finite presentations. -/
instance finiteBindQuasicoherentData_isFinitePresentation
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).HasSheafCompose
        (forget₂ RingCat AddCommGrpCat)]
    [∀ V : X.Opens,
      HasSheafify
        ((Opens.grothendieckTopology X).over V) AddCommGrpCat]
    [∀ V : X.Opens,
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
        AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).HasSheafCompose
          (forget₂ RingCat AddCommGrpCat)]
    [∀ i (W : Over (U i)),
      HasSheafify
        (((Opens.grothendieckTopology X).over
          (U i)).over W) AddCommGrpCat]
    [∀ i (W : Over (U i)),
      (((Opens.grothendieckTopology X).over
        (U i)).over W).WEqualsLocallyBijective AddCommGrpCat]
    (D : ∀ i, (M.over (U i)).QuasicoherentData)
    [hD : ∀ i, (D i).IsFinitePresentation] :
    (finiteBindQuasicoherentData M U hU D).IsFinitePresentation where
  isFinite_presentation ij :=
    finiteBindPresentation_isFinite M U D hD ij

/--
Finite presentation is local for a site-theoretic covering family of
opens.
-/
theorem isFinitePresentation_of_coversTop
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (hlocal : ∀ i, (M.over (U i)).IsFinitePresentation) :
    M.IsFinitePresentation := by
  letI :
      ∀ V : X.Opens,
        ((Opens.grothendieckTopology X).over V).HasSheafCompose
          (forget₂ RingCat AddCommGrpCat) :=
    fun _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafComposeAddCommGrp _
  letI :
      ∀ V : X.Opens,
        HasSheafify
          ((Opens.grothendieckTopology X).over V) AddCommGrpCat :=
    fun _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafifyAddCommGrp _
  letI :
      ∀ V : X.Opens,
        ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
          AddCommGrpCat :=
    fun _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.wEqualsLocallyBijectiveAddCommGrp _
  letI :
      ∀ i (W : Over (U i)),
        (((Opens.grothendieckTopology X).over
          (U i)).over W).HasSheafCompose
            (forget₂ RingCat AddCommGrpCat) :=
    fun _ _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafComposeAddCommGrp _
  letI :
      ∀ i (W : Over (U i)),
        HasSheafify
          (((Opens.grothendieckTopology X).over
            (U i)).over W) AddCommGrpCat :=
    fun _ _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.hasSheafifyAddCommGrp _
  letI :
      ∀ i (W : Over (U i)),
        (((Opens.grothendieckTopology X).over
          (U i)).over W).WEqualsLocallyBijective AddCommGrpCat :=
    fun _ _ =>
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.wEqualsLocallyBijectiveAddCommGrp _
  let D : ∀ i, (M.over (U i)).QuasicoherentData :=
    fun i =>
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        (M.over (U i)) (self := hlocal i)).choose
  letI (i : I) : (D i).IsFinitePresentation :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (M.over (U i)) (self := hlocal i)).choose_spec
  exact
    {
      exists_quasicoherentData :=
        ⟨finiteBindQuasicoherentData M U hU D,
          inferInstance⟩
    }

end AlgebraicGeometry.Scheme.Modules
