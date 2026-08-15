/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafExtLinearResolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseAcyclicCoverCechComparison

/-!
# Linear Čech comparison over a flat coefficient ring

This strengthens `FlatBaseAcyclicCoverCechComparison`: the comparison
between constant-source Ext and normalized Čech homology is an
isomorphism in `ModuleCat R`, not only after forgetting to additive
groups.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type} [CommRing R] [Module.Flat ℤ R]
variable {X : Scheme.{0}}
  [X.Over (Spec (CommRingCat.of R))]
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- Constant-source Ext is coefficient-linearly isomorphic to the
finite-subset section Čech homology of an acyclic cover. -/
noncomputable def constantBaseExtLinearIsoFiniteSubsetSectionHomology
    (M : X.Modules)
    (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤)
    (hacyclic :
      IsAcyclicOnIntersections
        M.sheaf U Finset.univ)
    (n : ℕ) :
    ModuleCat.of R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) X)
          (moduleSheaf (k := R) M) n) ≅
      (finiteSubsetCechComplex
        (R := R)
        (sectionModule U (moduleSheaf (k := R) M))
        (sectionRestriction U (moduleSheaf (k := R) M))
        (sectionRestriction_comp U
          (moduleSheaf (k := R) M))).homology n :=
  finiteSubsetFreeSheafExtLinearIsoResolutionHomology
      U hU (moduleSheaf (k := R) M)
      (freeBaseIntersection_ext_subsingleton
        M U hacyclic) n ≪≫
    (HomologicalComplex.homologyFunctor
      (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
        (contravariantHomCocomplexIsoSectionPiCech
          U (moduleSheaf (k := R) M)) ≪≫
    (HomologicalComplex.homologyFunctor
      (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
        (sectionPiCechComplexIsoFiniteSubsetOver
          U (moduleSheaf (k := R) M))

/-- For an integer twist on projective space, constant-source Ext is
coefficient-linearly computed by the standard section Čech complex. -/
noncomputable def integerTwistConstantBaseExtLinearIsoStandardCechHomology
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    (d : ℕ) (m : ℤ) (n : ℕ) :
    letI :
        (scheme R d).Over (Spec (CommRingCat.of R)) :=
      ⟨toSpec R d⟩
    ModuleCat.of R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (moduleSheaf (k := R) (OInt R d m)) n) ≅
      (baseStandardSectionCechComplex
        R d m).homology n := by
  letI :
      (scheme R d).Over (Spec (CommRingCat.of R)) :=
    ⟨toSpec R d⟩
  let eExt :=
    constantBaseExtLinearIsoFiniteSubsetSectionHomology
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
      C ≅ baseStandardSectionCechComplex R d m :=
    Iso.refl _
  exact eExt ≪≫
    (HomologicalComplex.homologyFunctor
      (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
        eComplex

/-- Over a Noetherian coefficient ring flat over `ℤ`, the
constant-source Ext modules of an integer twist are finite whenever the
standard Laurent coordinates are natural under restriction. -/
theorem integerTwistConstantBaseExt_finite
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    [IsNoetherianRing R]
    (d : ℕ) (m : ℤ)
    (hcoord : BaseStandardCoverCoordinatesNatural R d m)
    (n : ℕ) :
    letI :
        (scheme R d).Over (Spec (CommRingCat.of R)) :=
      ⟨toSpec R d⟩
    Module.Finite R
      (Abelian.Ext
        (constantRankOneSheaf (R := R) (scheme R d))
        (moduleSheaf (k := R) (OInt R d m)) n) := by
  letI :
      (scheme R d).Over (Spec (CommRingCat.of R)) :=
    ⟨toSpec R d⟩
  letI :
      Module.Finite R
        ((baseStandardSectionCechComplex R d m).homology n) :=
    baseStandardSectionCechHomology_finite
      R d m hcoord n
  exact Module.Finite.equiv
    (integerTwistConstantBaseExtLinearIsoStandardCechHomology
      R d m n).toLinearEquiv.symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison
