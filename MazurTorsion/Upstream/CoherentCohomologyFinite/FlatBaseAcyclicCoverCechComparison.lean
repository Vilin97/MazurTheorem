/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafExtLinearComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseOpenCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseLinearStandardCech
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerAcyclicCover

/-!
# Base-linear Čech comparison for flat coefficient rings

For a coefficient ring flat over `ℤ`, ordinary acyclicity of the
underlying abelian sheaf makes the represented free module sheaves
Ext-acyclic.  The normalized free-sheaf resolution therefore computes
constant-source Ext by the coefficient-linear section Čech complex.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseOpenCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type} [CommRing R] [Module.Flat ℤ R]
variable {X : Scheme.{0}}
  [X.Over (Spec (CommRingCat.of R))]
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- Integer signs in the sheaf boundary agree with coefficient-ring
signs in the generic finite-subset differential. -/
lemma sectionPiDifferential_eq_finiteSubsetPiDifferentialOver
    (U : ι → X.Opens)
    (F : ModuleSheaf (R := R) X) (q : ℕ) :
    sectionPiDifferential U F q =
      finiteSubsetPiDifferential
        (R := R)
        (sectionModule U F)
        (sectionRestriction U F) q := by
  apply LinearMap.ext
  intro x
  funext J
  rw [sectionPiDifferential_apply,
    finiteSubsetPiDifferential_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact insertionSign_int_smul_eq_ring
    (k := R) (J.1.erase j.1) j.1
    (sectionRestriction U F
      (Finset.erase_subset j.1 J.1)
      (x (J.erase j.1 j.2)))

/-- The target-oriented sheaf section complex is the generic
coefficient-linear finite-subset complex. -/
noncomputable def sectionPiCechComplexIsoFiniteSubsetOver
    (U : ι → X.Opens)
    (F : ModuleSheaf (R := R) X) :
    sectionPiCechComplex U F ≅
      finiteSubsetCechComplex
        (R := R)
        (sectionModule U F)
        (sectionRestriction U F)
        (sectionRestriction_comp U F) := by
  let ePi :
      sectionPiCechComplex U F ≅
        finiteSubsetPiCechComplex
          (R := R)
          (sectionModule U F)
          (sectionRestriction U F)
          (sectionRestriction_comp U F) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun _ => Iso.refl _)
      (by
        rintro i j (hij : i + 1 = j)
        subst hij
        simp only [sectionPiCechComplex,
          finiteSubsetPiCechComplex,
          CochainComplex.of_d, Iso.refl_hom,
          Category.comp_id, Category.id_comp]
        apply ModuleCat.hom_ext
        exact
          (sectionPiDifferential_eq_finiteSubsetPiDifferentialOver
            U F i).symm)
  exact ePi.trans
    (finiteSubsetCechComplexIsoPi
      (R := R)
      (sectionModule U F)
      (sectionRestriction U F)
      (sectionRestriction_comp U F)).symm

/-- Acyclicity on nonempty intersections makes every represented free
coefficient-module sheaf Ext-acyclic. -/
theorem freeBaseIntersection_ext_subsingleton
    (M : X.Modules)
    (U : ι → X.Opens)
    (hacyclic :
      IsAcyclicOnIntersections
        M.sheaf U Finset.univ)
    (q r : ℕ) (I : Simplex (ι := ι) q) :
    Subsingleton
      (Abelian.Ext
        (freeModuleSheaf (R := R)
          (intersection U I.1))
        (moduleSheaf (k := R) M) (r + 1)) := by
  have hI : I.1.Nonempty := by
    rw [← Finset.card_pos, I.2]
    omega
  have h :=
    hacyclic I.1 hI (Finset.subset_univ I.1)
      (r + 1) (Nat.succ_pos r)
  let e :=
    freeBaseModuleSheafExtAddEquivHPrime
      (R := R) (intersection U I.1) M (r + 1)
  exact
    ⟨fun x y =>
      e.injective (h.elim (e x) (e y))⟩

/-- Constant-source Ext is the underlying abelian group of the
coefficient-linear normalized section Čech homology. -/
noncomputable def constantBaseExtIsoFiniteSubsetSectionHomology
    (M : X.Modules)
    (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤)
    (hacyclic :
      IsAcyclicOnIntersections
        M.sheaf U Finset.univ)
    (n : ℕ) :
    AddCommGrpCat.of
        (Abelian.Ext
          (constantRankOneSheaf (R := R) X)
          (moduleSheaf (k := R) M) n) ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((finiteSubsetCechComplex
          (R := R)
          (sectionModule U (moduleSheaf (k := R) M))
          (sectionRestriction U (moduleSheaf (k := R) M))
          (sectionRestriction_comp U
            (moduleSheaf (k := R) M))).homology n) :=
  finiteSubsetFreeSheafExtIsoLinearResolutionHomology
      U hU (moduleSheaf (k := R) M)
      (freeBaseIntersection_ext_subsingleton
        M U hacyclic) n ≪≫
    (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
      ((HomologicalComplex.homologyFunctor
        (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
          (contravariantHomCocomplexIsoSectionPiCech
            U (moduleSheaf (k := R) M))) ≪≫
    (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
      ((HomologicalComplex.homologyFunctor
        (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
          (sectionPiCechComplexIsoFiniteSubsetOver
            U (moduleSheaf (k := R) M)))

/-- For an integer twist on projective space, constant-source Ext is
computed by the base-linear standard section Čech complex. -/
noncomputable def integerTwistConstantBaseExtIsoStandardCechHomology
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    (d : ℕ) (m : ℤ) (n : ℕ) :
    letI :
        (scheme R d).Over (Spec (CommRingCat.of R)) :=
      ⟨toSpec R d⟩
    AddCommGrpCat.of
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (moduleSheaf (k := R) (OInt R d m)) n) ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((baseStandardSectionCechComplex
          R d m).homology n) := by
  letI :
      (scheme R d).Over (Spec (CommRingCat.of R)) :=
    ⟨toSpec R d⟩
  let eExt :=
    constantBaseExtIsoFiniteSubsetSectionHomology
      (R := R) (X := scheme R d)
      (OInt R d m) (standardChart R)
      (iSup_standardChart R d)
      (integerStandardCover_isAcyclicOnIntersections
        R d m) n
  let C :=
    finiteSubsetCechComplex
      (R := R)
      (sectionModule (standardChart R)
        (moduleSheaf (k := R) (OInt R d m)))
      (sectionRestriction (standardChart R)
        (moduleSheaf (k := R) (OInt R d m)))
      (sectionRestriction_comp (standardChart R)
        (moduleSheaf (k := R) (OInt R d m)))
  let eComplex :
      C ≅ baseStandardSectionCechComplex R d m := by
    exact Iso.refl _
  exact eExt ≪≫
    (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
      ((HomologicalComplex.homologyFunctor
        (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
          eComplex)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison
