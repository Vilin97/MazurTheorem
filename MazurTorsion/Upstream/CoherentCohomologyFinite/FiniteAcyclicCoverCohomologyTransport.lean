/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteAcyclicCoverAbelianCechComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechTranspose
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Transporting cohomology between finite acyclic covers

Two finite acyclic covers with pointwise equivalent section systems have
isomorphic normalized Čech complexes and hence additively equivalent global
cohomology.  This is the abstract comparison used for a sheaf upstairs and
its direct image on an affine cover of the base.
-/

open CategoryTheory TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverCohomologyTransport

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.AbelianSheafFiniteSubsetCech
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverAbelianCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {T S : TopCat}
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/--
A pointwise integer-linear equivalence of the section systems on two
finite covers, compatible with every face restriction, induces an
isomorphism of their normalized Čech complexes.
-/
noncomputable def abelianSectionCechComplexIsoOfLinearEquiv
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (H : Sheaf (Opens.grothendieckTopology S)
      AddCommGrpCat)
    (U : ι → Opens T) (V : ι → Opens S)
    (e : ∀ {q : ℕ} (I : Simplex (ι := ι) q),
      abelianSectionModule G U I.1 ≃ₗ[ℤ]
        abelianSectionModule H V I.1)
    (he : ∀ {q : ℕ}
      (J : Simplex (ι := ι) (q + 1)) (j : ↥J.1)
      (x : abelianSectionModule G U (J.1.erase j.1)),
      e J
          (abelianSectionRestriction G U
            (Finset.erase_subset j.1 J.1) x) =
        abelianSectionRestriction H V
          (Finset.erase_subset j.1 J.1)
          (e (J.erase j.1 j.2) x)) :
    abelianSectionCechComplex G U ≅
      abelianSectionCechComplex H V := by
  let A := abelianSectionModule G U
  let B := abelianSectionModule H V
  let resA : ∀ {I J : Finset ι},
      I ⊆ J → A I →ₗ[ℤ] A J :=
    fun {_ _} hIJ =>
      abelianSectionRestriction G U hIJ
  let resB : ∀ {I J : Finset ι},
      I ⊆ J → B I →ₗ[ℤ] B J :=
    fun {_ _} hIJ =>
      abelianSectionRestriction H V hIJ
  exact
    finiteSubsetCechComplexIsoPi
        A resA (abelianSectionRestriction_comp G U) ≪≫
      finiteSubsetPiCechComplexIsoOfLinearEquiv
        A resA B resB
        (abelianSectionRestriction_comp G U)
        (abelianSectionRestriction_comp H V)
        e he ≪≫
      (finiteSubsetCechComplexIsoPi
        B resB
        (abelianSectionRestriction_comp H V)).symm

/--
Global cohomology is transported by a compatible pointwise equivalence of
section systems on two finite acyclic covers.
-/
noncomputable def globalHAddEquivOfAcyclicCoverSectionEquiv
    (G : Sheaf (Opens.grothendieckTopology T)
      AddCommGrpCat)
    (H : Sheaf (Opens.grothendieckTopology S)
      AddCommGrpCat)
    (U : ι → Opens T) (V : ι → Opens S)
    (hU : ⨆ i, U i = ⊤)
    (hV : ⨆ i, V i = ⊤)
    (hG :
      IsAcyclicOnIntersections G U Finset.univ)
    (hH :
      IsAcyclicOnIntersections H V Finset.univ)
    (e : ∀ {q : ℕ} (I : Simplex (ι := ι) q),
      abelianSectionModule G U I.1 ≃ₗ[ℤ]
        abelianSectionModule H V I.1)
    (he : ∀ {q : ℕ}
      (J : Simplex (ι := ι) (q + 1)) (j : ↥J.1)
      (x : abelianSectionModule G U (J.1.erase j.1)),
      e J
          (abelianSectionRestriction G U
            (Finset.erase_subset j.1 J.1) x) =
        abelianSectionRestriction H V
          (Finset.erase_subset j.1 J.1)
          (e (J.erase j.1 j.2) x))
    (n : ℕ) :
    CategoryTheory.Sheaf.H G n ≃+
      CategoryTheory.Sheaf.H H n := by
  let eComplex :=
    abelianSectionCechComplexIsoOfLinearEquiv
      G H U V e he
  let eHomology :=
    isoOfQuasiIsoAt eComplex.hom n
  exact
    (globalHAddEquivAbelianSectionCechHomology
      G U hU hG n).trans <|
      ((forget₂ (ModuleCat ℤ) AddCommGrpCat).mapIso
        eHomology).addCommGroupIsoToAddEquiv |>.trans <|
        (globalHAddEquivAbelianSectionCechHomology
          H V hV hH n).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteAcyclicCoverCohomologyTransport
