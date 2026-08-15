/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteAcyclicCoverCohomologyTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardCohomology

/-!
# Čech comparison for direct images

For a continuous map, the intersections in the inverse-image cover are
the inverse images of the corresponding intersections downstairs.  Thus
the section systems of a sheaf upstairs and of its direct image downstairs
agree, compatibly with restriction.  On finite acyclic covers this identifies
their global cohomology.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
  TensorProduct


noncomputable section

noncomputable local instance finiteCoverCohomologyAddCommGroup
    {Z : TopCat} (G : Z.Sheaf AddCommGrpCat) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverPushforwardCohomology

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.AbelianSheafFiniteSubsetCech
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverCohomologyTransport
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {T S : TopCat}
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- The inverse image of a finite intersection is the corresponding
finite intersection of inverse images. -/
lemma intersection_inverseImageCover
    (f : T ⟶ S) (V : ι → Opens S) (I : Finset ι) :
    intersection (fun i => (Opens.map f).obj (V i)) I =
      (Opens.map f).obj (intersection V I) := by
  classical
  change
    finiteIntersection (fun i => (Opens.map f).obj (V i)) I =
      (Opens.map f).obj (finiteIntersection V I)
  induction I using Finset.induction_on with
  | empty =>
      simp only [finiteIntersection_empty, Opens.map_top]
  | @insert i I hi ih =>
      simp only [finiteIntersection_insert, ih]
      rfl

/-- Sections of a sheaf on an intersection in the inverse-image cover
are canonically the sections of its direct image on the intersection
downstairs. -/
noncomputable def pushforwardSectionLinearEquiv
    (f : T ⟶ S)
    (G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat)
    (V : ι → Opens S) (I : Finset ι) :
    abelianSectionModule G
        (fun i => (Opens.map f).obj (V i)) I ≃ₗ[ℤ]
      abelianSectionModule
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj G)
        V I := by
  change
    G.obj.obj
        (op (intersection
          (fun i => (Opens.map f).obj (V i)) I)) ≃ₗ[ℤ]
      G.obj.obj
        (op ((Opens.map f).obj (intersection V I)))
  let e :=
    G.obj.mapIso
      (eqToIso (congrArg op
        (intersection_inverseImageCover f V I)))
  exact
    e.addCommGroupIsoToAddEquiv.toIntLinearEquiv

/-- The direct-image section identification commutes with every
restriction between finite intersections. -/
lemma pushforwardSectionLinearEquiv_restriction
    (f : T ⟶ S)
    (G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat)
    (V : ι → Opens S)
    {I J : Finset ι} (hIJ : I ⊆ J)
    (x : abelianSectionModule G
      (fun i => (Opens.map f).obj (V i)) I) :
    pushforwardSectionLinearEquiv f G V J
        (abelianSectionRestriction G
          (fun i => (Opens.map f).obj (V i)) hIJ x) =
      abelianSectionRestriction
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj G)
        V hIJ
        (pushforwardSectionLinearEquiv f G V I x) := by
  let U : ι → Opens T :=
    fun i => (Opens.map f).obj (V i)
  let a :
      op (intersection U I) ⟶
        op (intersection U J) :=
    (homOfLE (intersection_anti U hIJ)).op
  let b :
      op (intersection U J) ⟶
        op ((Opens.map f).obj (intersection V J)) :=
    eqToHom (congrArg op
      (intersection_inverseImageCover f V J))
  let c :
      op (intersection U I) ⟶
        op ((Opens.map f).obj (intersection V I)) :=
    eqToHom (congrArg op
      (intersection_inverseImageCover f V I))
  let d :
      op ((Opens.map f).obj (intersection V I)) ⟶
        op ((Opens.map f).obj (intersection V J)) :=
    ((Opens.map f).map
      (homOfLE (intersection_anti V hIJ))).op
  have harrow : a ≫ b = c ≫ d :=
    Subsingleton.elim _ _
  have hmap :
      G.obj.map a ≫ G.obj.map b =
        G.obj.map c ≫ G.obj.map d := by
    rw [← G.obj.map_comp, ← G.obj.map_comp,
      harrow]
  exact congrArg (fun k => k.hom x) hmap

/-- A cover of the target pulls back to a cover of the source. -/
lemma iSup_inverseImageCover_eq_top
    (f : T ⟶ S) (V : ι → Opens S)
    (hV : ⨆ i, V i = ⊤) :
    ⨆ i, (Opens.map f).obj (V i) = ⊤ := by
  apply Opens.ext
  ext x
  constructor
  · intro _
    trivial
  · intro _
    have hx : f x ∈ ⨆ i, V i := by
      rw [hV]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩

/--
If a finite cover downstairs and its inverse-image cover upstairs are
acyclic for the direct image and the original sheaf respectively, then
direct image preserves global cohomology in every degree.
-/
noncomputable def pushforwardHAddEquivOfAcyclicCover
    (f : T ⟶ S)
    (G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat)
    (V : ι → Opens S)
    (hV : ⨆ i, V i = ⊤)
    (hG :
      IsAcyclicOnIntersections G
        (fun i => (Opens.map f).obj (V i))
        Finset.univ)
    (hpush :
      IsAcyclicOnIntersections
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj G)
        V Finset.univ)
    (n : ℕ) :
    CategoryTheory.Sheaf.H G n ≃+
      CategoryTheory.Sheaf.H
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj G) n :=
  globalHAddEquivOfAcyclicCoverSectionEquiv
    G ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj G)
    (fun i => (Opens.map f).obj (V i)) V
    (iSup_inverseImageCover_eq_top f V hV) hV
    hG hpush
    (fun I => pushforwardSectionLinearEquiv f G V I)
    (fun J j x =>
      pushforwardSectionLinearEquiv_restriction
        f G V (Finset.erase_subset j.1 J.1) x)
    n

/-- Scheme-module form of `pushforwardHAddEquivOfAcyclicCover`. -/
noncomputable def schemePushforwardHAddEquivOfAcyclicCover
    {X Y : Scheme} (f : X ⟶ Y) (M : X.Modules)
    (V : ι → Opens Y)
    (hV : ⨆ i, V i = ⊤)
    (hM :
      IsAcyclicOnIntersections M.sheaf
        (fun i => (Opens.map f.base).obj (V i))
        Finset.univ)
    (hpush :
      IsAcyclicOnIntersections
        ((Scheme.Modules.pushforward f).obj M).sheaf
        V Finset.univ)
    (n : ℕ) :
    M.sheaf.H n ≃+
      ((Scheme.Modules.pushforward f).obj M).sheaf.H n := by
  change
    M.sheaf.H n ≃+
      CategoryTheory.Sheaf.H
        ((TopCat.Sheaf.pushforward AddCommGrpCat f.base).obj
          M.sheaf) n
  exact
    pushforwardHAddEquivOfAcyclicCover
      f.base M.sheaf V hV hM hpush n

/-- Rationalized scheme-module cohomology comparison supplied by a
finite acyclic base cover. -/
noncomputable def
    schemePushforwardRationalizedCohomologyLinearEquivOfAcyclicCover
    {X Y : Scheme} (f : X ⟶ Y) (M : X.Modules)
    (V : ι → Opens Y)
    (hV : ⨆ i, V i = ⊤)
    (hM :
      IsAcyclicOnIntersections M.sheaf
        (fun i => (Opens.map f.base).obj (V i))
        Finset.univ)
    (hpush :
      IsAcyclicOnIntersections
        ((Scheme.Modules.pushforward f).obj M).sheaf
        V Finset.univ)
    (n : ℕ) :
    ℚ ⊗[ℤ] M.sheaf.H n ≃ₗ[ℚ]
      ℚ ⊗[ℤ]
        ((Scheme.Modules.pushforward f).obj M).sheaf.H n :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalizationMapAddEquiv
    (schemePushforwardHAddEquivOfAcyclicCover
      f M V hV hM hpush n)

/-- Finite-dimensional rationalized cohomology is invariant under a
pushforward whenever the comparison is computed by finite acyclic
covers on source and target. -/
theorem schemePushforward_rationalizedCohomology_finite_iff_of_acyclicCover
    {X Y : Scheme} (f : X ⟶ Y) (M : X.Modules)
    (V : ι → Opens Y)
    (hV : ⨆ i, V i = ⊤)
    (hM :
      IsAcyclicOnIntersections M.sheaf
        (fun i => (Opens.map f.base).obj (V i))
        Finset.univ)
    (hpush :
      IsAcyclicOnIntersections
        ((Scheme.Modules.pushforward f).obj M).sheaf
        V Finset.univ)
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) ↔
      Module.Finite ℚ
        (ℚ ⊗[ℤ]
          ((Scheme.Modules.pushforward f).obj M).sheaf.H n) :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalization_finite_congr
    (schemePushforwardHAddEquivOfAcyclicCover
      f M V hV hM hpush n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverPushforwardCohomology
