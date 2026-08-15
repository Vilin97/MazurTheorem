/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CohomologyCarrier
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafExtLinearComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.FreeModuleSheafOpenCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistFreeResolutionHomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerAcyclicCover

/-!
# Ext-acyclicity of the standard-cover free-sheaf resolution

Higher Ext from a free module sheaf represented by an open is ordinary
cohomology on that open.  The standard intersections are affine, so the
normalized standard-cover free-sheaf resolution is Ext-acyclic against
every integer Serre twist.  Combining this with the explicit linear Hom
complex proves finite-dimensionality of the rational-module Ext carrier,
and hence of the rationalized abelian-sheaf cohomology carrier.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeModuleSheafOpenCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

local instance projectiveSpaceOverQForFreeSheafExt (d : ℕ) :
    (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
  ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩

noncomputable local instance projectiveSpaceSheafHCoefficients
    (d : ℕ) (m : ℤ) (n : ℕ) :
    AddCommGroup ((OInt ℚ d m).sheaf.H n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Every represented nonempty standard intersection is Ext-acyclic in
positive degree against an integer Serre twist. -/
theorem standardCoverFreeModuleSheaf_ext_subsingleton
    (d : ℕ) (m : ℤ) (q r : ℕ)
    (I : Simplex (ι := Fin (d + 1)) q) :
    Subsingleton
      (Abelian.Ext
        (freeModuleSheaf (R := ℚ)
          (intersection (standardChart ℚ) I.1))
        (Geometric.moduleSheaf (OInt ℚ d m)) (r + 1)) := by
  have hI : I.1.Nonempty := by
    rw [← Finset.card_pos, I.2]
    omega
  letI : Nonempty ↥I.1 :=
    Finset.nonempty_coe_sort.mpr hI
  have h :=
    subsingleton_integer_H'_standardIntersection
      ℚ d m (fun i : ↥I.1 => i.1) r
  rw [← finiteIntersection_standardChart ℚ d I.1] at h
  change
    Subsingleton
      (CategoryTheory.Sheaf.H'
        (OInt ℚ d m).underlyingSheaf
        (r + 1) (intersection (standardChart ℚ) I.1)) at h
  let e :=
    freeModuleSheafExtAddEquivHPrime
      (intersection (standardChart ℚ) I.1)
      (Geometric.moduleSheaf (OInt ℚ d m)) (r + 1)
  exact
    ⟨fun x y =>
      e.injective <| h.elim (e x) (e y)⟩

/-- The Ext carrier for an integer twist is the underlying additive
group of the normalized standard-cover linear Hom-complex homology. -/
noncomputable def standardCoverModuleSheafExtIsoLinearResolutionHomology
    (d : ℕ) (m : ℤ) (n : ℕ) :
    AddCommGrpCat.of
        (Abelian.Ext
          (constantRankOneSheaf (R := ℚ) (scheme ℚ d))
          (Geometric.moduleSheaf (OInt ℚ d m)) n) ≅
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).obj
        ((contravariantHomCocomplex (standardChart ℚ)
          (Geometric.moduleSheaf (OInt ℚ d m))).homology n) :=
  finiteSubsetFreeSheafExtIsoLinearResolutionHomology
    (standardChart ℚ) (iSup_standardChart ℚ d)
    (Geometric.moduleSheaf (OInt ℚ d m))
    (standardCoverFreeModuleSheaf_ext_subsingleton d m) n

/-- The preceding additive comparison is automatically rational-linear. -/
noncomputable def standardCoverModuleSheafExtLinearEquivResolutionHomology
    (d : ℕ) (m : ℤ) (n : ℕ) :
    Abelian.Ext
        (constantRankOneSheaf (R := ℚ) (scheme ℚ d))
        (Geometric.moduleSheaf (OInt ℚ d m)) n ≃ₗ[ℚ]
      (contravariantHomCocomplex (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m))).homology n :=
  ratLinearEquivOfAddEquiv
    (standardCoverModuleSheafExtIsoLinearResolutionHomology
      d m n).addCommGroupIsoToAddEquiv

/-- Rational-module sheaf Ext for an integer twist is finite-dimensional
once its Laurent coordinates are independent of the chosen chart. -/
theorem standardCoverModuleSheafExt_finite
    (d : ℕ) (m : ℤ)
    (hchart : IntegerChartCoordinatesIndependent d m)
    (n : ℕ) :
    Module.Finite ℚ
      (Abelian.Ext
        (constantRankOneSheaf (R := ℚ) (scheme ℚ d))
        (Geometric.moduleSheaf (OInt ℚ d m)) n) := by
  letI :
      Module.Finite ℚ
        ((contravariantHomCocomplex (standardChart ℚ)
          (Geometric.moduleSheaf (OInt ℚ d m))).homology n) :=
    standardCoverContravariantHomCocomplexHomology_finite
      d m hchart n
  exact Module.Finite.equiv
    (standardCoverModuleSheafExtLinearEquivResolutionHomology
      d m n).symm

/-- Every rationalized abelian-sheaf cohomology group of an integer
Serre twist is finite-dimensional under the chart-independence seam. -/
theorem rationalizedOIntSheafH_finite
    (d : ℕ) (m : ℤ)
    (hchart : IntegerChartCoordinatesIndependent d m)
    (n : ℕ) :
    Module.Finite ℚ
      (ℚ ⊗[ℤ] (OInt ℚ d m).sheaf.H n) := by
  letI :
      Module.Finite ℚ
        (Abelian.Ext
          (constantRankOneSheaf (R := ℚ) (scheme ℚ d))
          (Geometric.moduleSheaf (OInt ℚ d m)) n) :=
    standardCoverModuleSheafExt_finite d m hchart n
  exact
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.CohomologyCarrier.rationalizedCohomology_moduleFinite_of_moduleSheafExt
      (OInt ℚ d m) n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
