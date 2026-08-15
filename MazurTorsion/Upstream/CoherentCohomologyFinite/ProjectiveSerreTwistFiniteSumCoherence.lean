/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerOperations

/-!
# Coherence of finite sums of integer Serre twists

A finite sum of integer twists becomes a finite free module on every
standard affine chart.  This supplies finite local presentations for the
integer, negative, and multiplicity-indexed sums used in twisted-free
presentations.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafFinitePresentation

variable (k : Type) [CommRing k] (d : ℕ)

/-- Pullback of a finite sum of integer twists to a standard chart is the
finite free module on the summand index type. -/
def finiteIntegerSumChartIso {ι : Type} [Fintype ι]
    (degree : ι → ℤ) (j : Fin (d + 1)) :
    (Scheme.Modules.pullback ((cover k d).f j)).obj
        (finiteIntegerSum k d degree) ≅
      SheafOfModules.free
        (R := ((cover k d).X j).ringCatSheaf) ι :=
  PreservesCoproduct.iso
      (Scheme.Modules.pullback ((cover k d).f j))
      (fun i => OInt k d (degree i)) ≪≫
    (coproductIsCoproduct
        (fun i : ι =>
          (Scheme.Modules.pullback ((cover k d).f j)).obj
            (OInt k d (degree i)))).coconePointsIsoOfNatIso
      (SheafOfModules.isColimitFreeCofan ι)
      (Discrete.natIso fun i => integerChartIso k d (degree i.as) j)

/-- The same chartwise finite-free trivialization, expressed using
restriction to the standard open subscheme. -/
def finiteIntegerSumRestrictionChartIso
    {ι : Type} [Fintype ι]
    (degree : ι → ℤ) (j : Fin (d + 1)) :
    (finiteIntegerSum k d degree).restrict
        (standardChart k j).ι ≅
      SheafOfModules.free
        (R := (standardChart k j).toScheme.ringCatSheaf) ι :=
  (Scheme.Modules.restrictFunctorIsoPullback
      (standardChart k j).ι).app
        (finiteIntegerSum k d degree) ≪≫
    finiteIntegerSumChartIso k d degree j

/-- Slice-site form of the finite-free chart trivialization. -/
def finiteIntegerSumOverChartIso
    {ι : Type} [Fintype ι]
    (degree : ι → ℤ) (j : Fin (d + 1)) :
    (finiteIntegerSum k d degree).over
        (standardChart k j) ≅
      SheafOfModules.free
        (R := (scheme k d).ringCatSheaf.over
          (standardChart k j)) ι :=
  Scheme.Modules.chartFreeOverIso
    (standardChart k j)
    (finiteIntegerSum k d degree) ι
    (finiteIntegerSumRestrictionChartIso k d degree j)

/-- The finite free presentation of a finite sum of twists on one standard
chart. -/
def finiteIntegerSumChartPresentation
    {ι : Type} [Fintype ι]
    (degree : ι → ℤ) (j : Fin (d + 1)) :
    ((finiteIntegerSum k d degree).over
      (standardChart k j)).Presentation :=
  SheafOfModules.Presentation.ofIsIso
    (finiteIntegerSumOverChartIso k d degree j).inv
    (freePresentation
      ((scheme k d).ringCatSheaf.over
        (standardChart k j)) ι)

instance finiteIntegerSumChartPresentation_isFinite
    {ι : Type} [Fintype ι]
    (degree : ι → ℤ) (j : Fin (d + 1)) :
    (finiteIntegerSumChartPresentation
      k d degree j).IsFinite := by
  dsimp only [finiteIntegerSumChartPresentation]
  infer_instance

/-- Finite-presentation data for a finite sum of twists on the standard
affine cover. -/
def finiteIntegerSumQuasicoherentData
    {ι : Type} [Fintype ι] (degree : ι → ℤ) :
    (finiteIntegerSum k d degree).QuasicoherentData where
  I := Fin (d + 1)
  X := standardChart k
  coversTop := by
    intro W x hxW
    have hx :
        x ∈ ⨆ j : Fin (d + 1), standardChart k j := by
      rw [iSup_standardChart k d]
      trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨j, hj⟩ := hx
    exact
      ⟨standardChart k j ⊓ W, homOfLE inf_le_right,
        ⟨j, ⟨homOfLE inf_le_left⟩⟩, hj, hxW⟩
  presentation j :=
    finiteIntegerSumChartPresentation k d degree j

/-- A finite sum of integer Serre twists is finitely presented. -/
instance finiteIntegerSum_isFinitePresentation
    {ι : Type} [Fintype ι] (degree : ι → ℤ) :
    (finiteIntegerSum k d degree).IsFinitePresentation where
  exists_quasicoherentData :=
    ⟨finiteIntegerSumQuasicoherentData k d degree, by
      apply
        SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
      intro j
      exact finiteIntegerSumChartPresentation_isFinite k d degree j⟩

/-- A finite sum of negative twists is finitely presented. -/
instance finiteNegativeSum_isFinitePresentation
    {ι : Type} [Fintype ι] (degree : ι → ℕ) :
    (finiteNegativeSum k d degree).IsFinitePresentation := by
  change
    (finiteIntegerSum k d
      (fun i => -(degree i : ℤ))).IsFinitePresentation
  exact finiteIntegerSum_isFinitePresentation k d _

/-- A finite multiplicity-indexed sum of negative twists is finitely
presented. -/
instance finiteNegativeMultiplicitySum_isFinitePresentation
    {ι : Type} [Fintype ι]
    (degree multiplicity : ι → ℕ) :
    (finiteNegativeMultiplicitySum
      k d degree multiplicity).IsFinitePresentation := by
  change
    (finiteIntegerSum k d
      (fun p : Σ i, Fin (multiplicity i) =>
        -(degree p.1 : ℤ))).IsFinitePresentation
  exact finiteIntegerSum_isFinitePresentation k d _

/-- Finite integer sums are of finite type. -/
theorem finiteIntegerSum_isFiniteType
    {ι : Type} [Fintype ι] (degree : ι → ℤ) :
    (finiteIntegerSum k d degree).IsFiniteType := by
  letI : (finiteIntegerSum k d degree).IsFinitePresentation :=
    finiteIntegerSum_isFinitePresentation k d degree
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _

/-- Finite integer sums are quasicoherent. -/
theorem finiteIntegerSum_isQuasicoherent
    {ι : Type} [Fintype ι] (degree : ι → ℤ) :
    (finiteIntegerSum k d degree).IsQuasicoherent := by
  letI : (finiteIntegerSum k d degree).IsFinitePresentation :=
    finiteIntegerSum_isFinitePresentation k d degree
  exact SheafOfModules.instIsQuasicoherentOfIsFinitePresentation _

/-- Finite negative sums are of finite type. -/
theorem finiteNegativeSum_isFiniteType
    {ι : Type} [Fintype ι] (degree : ι → ℕ) :
    (finiteNegativeSum k d degree).IsFiniteType := by
  letI : (finiteNegativeSum k d degree).IsFinitePresentation :=
    finiteNegativeSum_isFinitePresentation k d degree
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _

/-- Finite negative sums are quasicoherent. -/
theorem finiteNegativeSum_isQuasicoherent
    {ι : Type} [Fintype ι] (degree : ι → ℕ) :
    (finiteNegativeSum k d degree).IsQuasicoherent := by
  letI : (finiteNegativeSum k d degree).IsFinitePresentation :=
    finiteNegativeSum_isFinitePresentation k d degree
  exact SheafOfModules.instIsQuasicoherentOfIsFinitePresentation _

/-- Finite multiplicity-indexed negative sums are of finite type. -/
theorem finiteNegativeMultiplicitySum_isFiniteType
    {ι : Type} [Fintype ι]
    (degree multiplicity : ι → ℕ) :
    (finiteNegativeMultiplicitySum
      k d degree multiplicity).IsFiniteType := by
  letI :
      (finiteNegativeMultiplicitySum
        k d degree multiplicity).IsFinitePresentation :=
    finiteNegativeMultiplicitySum_isFinitePresentation
      k d degree multiplicity
  exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _

/-- Finite multiplicity-indexed negative sums are quasicoherent. -/
theorem finiteNegativeMultiplicitySum_isQuasicoherent
    {ι : Type} [Fintype ι]
    (degree multiplicity : ι → ℕ) :
    (finiteNegativeMultiplicitySum
      k d degree multiplicity).IsQuasicoherent := by
  letI :
      (finiteNegativeMultiplicitySum
        k d degree multiplicity).IsFinitePresentation :=
    finiteNegativeMultiplicitySum_isFinitePresentation
      k d degree multiplicity
  exact SheafOfModules.instIsQuasicoherentOfIsFinitePresentation _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
