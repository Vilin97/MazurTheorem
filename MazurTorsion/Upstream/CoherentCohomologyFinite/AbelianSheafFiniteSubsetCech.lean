/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteAcyclicCoverSectionCechComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechTranspose

/-!
# Normalized finite-subset Čech complexes of abelian sheaves

An abelian sheaf has canonical integer-module section groups.  This file
packages their normalized finite-subset Čech complex and compares it with
the section complex obtained after lifting the sheaf along the equivalence
between abelian groups and integer modules.
-/

open CategoryTheory Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.AbelianSheafFiniteSubsetCech

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverSectionCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeIntegerModuleSheafOpenCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {T : TopCat}
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- The additive section group on one finite intersection. -/
abbrev abelianSectionModule
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T) (I : Finset ι) : Type :=
  G.obj.obj (op (intersection U I))

/-- Restriction of abelian-sheaf sections as an integer-linear map. -/
noncomputable def abelianSectionRestriction
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    abelianSectionModule G U I →ₗ[ℤ]
      abelianSectionModule G U J :=
  (G.obj.map
    (homOfLE (intersection_anti U hIJ)).op).hom.toIntLinearMap

@[simp]
lemma abelianSectionRestriction_apply
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T)
    {I J : Finset ι} (hIJ : I ⊆ J)
    (x : abelianSectionModule G U I) :
    abelianSectionRestriction G U hIJ x =
      G.obj.map
        (homOfLE (intersection_anti U hIJ)).op x :=
  rfl

/-- Functoriality of additive section restriction. -/
lemma abelianSectionRestriction_comp
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T)
    {I J K : Finset ι}
    (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : abelianSectionModule G U I) :
    abelianSectionRestriction G U hJK
        (abelianSectionRestriction G U hIJ x) =
      abelianSectionRestriction G U
        (hIJ.trans hJK) x := by
  let a :=
    (homOfLE (intersection_anti U hIJ)).op
  let b :=
    (homOfLE (intersection_anti U hJK)).op
  let c :=
    (homOfLE
      (intersection_anti U (hIJ.trans hJK))).op
  have hmap :
      G.obj.map a ≫ G.obj.map b =
        G.obj.map c := by
    rw [← G.obj.map_comp]
    congr 1
  exact congrArg (fun f => f.hom x) hmap

/-- The normalized finite-support section Čech complex of an abelian
sheaf, in canonical integer modules. -/
noncomputable def abelianSectionCechComplex
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  finiteSubsetCechComplex
    (R := ℤ)
    (abelianSectionModule G U)
    (fun {_ _} hIJ =>
      abelianSectionRestriction G U hIJ)
    (fun hIJ hJK x =>
      abelianSectionRestriction_comp
        G U hIJ hJK x)

/-- On one open, the integer lift has the same additive section group as
the original abelian sheaf. -/
noncomputable def integerLiftSectionLinearEquiv
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (V : Opens T) :
    (integerLiftSheaf G).obj.obj (op V) ≃ₗ[ℤ]
      G.obj.obj (op V) := by
  let J := Opens.grothendieckTopology T
  let e :=
    (sheafToPresheaf J AddCommGrpCat).mapIso
      (sheafLiftForgetIsoAt J G)
  exact
    (e.app (op V)).addCommGroupIsoToAddEquiv.toIntLinearEquiv

/-- The section equivalence for the integer lift commutes with
restriction. -/
lemma integerLiftSectionLinearEquiv_restriction
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T)
    {I J : Finset ι} (hIJ : I ⊆ J)
    (x : (integerLiftSheaf G).obj.obj
      (op (intersection U I))) :
    integerLiftSectionLinearEquiv G
        (intersection U J)
        (sectionRestriction U
          (integerLiftSheaf G) hIJ x) =
      abelianSectionRestriction G U hIJ
        (integerLiftSectionLinearEquiv G
          (intersection U I) x) := by
  let Jtop := Opens.grothendieckTopology T
  let e :=
    (sheafToPresheaf Jtop AddCommGrpCat).mapIso
      (sheafLiftForgetIsoAt Jtop G)
  let a :=
    (homOfLE (intersection_anti U hIJ)).op
  have hnat := e.hom.naturality a
  exact congrArg (fun f => f.hom x) hnat

/-- For integer-module sheaves, the sheaf-theoretic target-oriented
section differential is the generic finite-subset differential. -/
lemma integerSectionPiDifferential_eq_finiteSubsetPiDifferential
    (F : ModuleSheaf (R := ℤ) T)
    (U : ι → Opens T) (q : ℕ) :
    sectionPiDifferential U F q =
      finiteSubsetPiDifferential
        (sectionModule U F)
        (sectionRestriction U F) q := by
  apply DFunLike.ext _ _
  intro x
  funext J
  rw [sectionPiDifferential_apply,
    finiteSubsetPiDifferential_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact
    (Int.cast_smul_eq_zsmul ℤ
      (insertionSign (R := ℤ) (J.1.erase j.1) j.1)
      (sectionRestriction U F
        (Finset.erase_subset j.1 J.1)
        (x (J.erase j.1 j.2)))).symm

/-- The target-oriented section complex of an integer-module sheaf is
the generic finite-product finite-subset complex. -/
noncomputable def integerSectionPiCechComplexIsoGeneric
    (F : ModuleSheaf (R := ℤ) T)
    (U : ι → Opens T) :
    sectionPiCechComplex U F ≅
      finiteSubsetPiCechComplex
        (sectionModule U F)
        (sectionRestriction U F)
        (sectionRestriction_comp U F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => Iso.refl _)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      simp only [sectionPiCechComplex,
        finiteSubsetPiCechComplex, CochainComplex.of_d,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply ModuleCat.hom_ext
      exact
        (integerSectionPiDifferential_eq_finiteSubsetPiDifferential
          F U i).symm)

/-- The lifted integer-module section complex is the finite-support
integer-linear Čech complex of the original abelian sheaf. -/
noncomputable def integerLiftSectionPiCechComplexIsoAbelian
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (U : ι → Opens T) :
    sectionPiCechComplex U (integerLiftSheaf G) ≅
      abelianSectionCechComplex G U := by
  let A := sectionModule U (integerLiftSheaf G)
  let resA : ∀ {I J : Finset ι},
      I ⊆ J → A I →ₗ[ℤ] A J :=
    fun {_ _} hIJ =>
      sectionRestriction U (integerLiftSheaf G) hIJ
  let B := abelianSectionModule G U
  let resB : ∀ {I J : Finset ι},
      I ⊆ J → B I →ₗ[ℤ] B J :=
    fun {_ _} hIJ =>
      abelianSectionRestriction G U hIJ
  exact
    (integerSectionPiCechComplexIsoGeneric
      (integerLiftSheaf G) U).trans <|
      (finiteSubsetPiCechComplexIsoOfLinearEquiv
        A resA B resB
        (sectionRestriction_comp U (integerLiftSheaf G))
        (abelianSectionRestriction_comp G U)
        (fun I =>
          integerLiftSectionLinearEquiv G
            (intersection U I.1))
        (fun J j x =>
          integerLiftSectionLinearEquiv_restriction
            G U (Finset.erase_subset j.1 J.1) x)).trans <|
        (finiteSubsetCechComplexIsoPi
          B resB
          (abelianSectionRestriction_comp G U)).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.AbelianSheafFiniteSubsetCech
