/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseAcyclicCoverCechLinearComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistAcyclicCover

/-!
# Module-valued Ext from the standard projective cover

The standard affine cover is acyclic for every quasicoherent module, not
only for Serre twists.  Over a coefficient ring flat over `ℤ`, the
coefficient-linear finite-subset resolution therefore computes
constant-source Ext.  Its normalized complex has no terms above the
dimension of projective space, giving a uniform Ext bound.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open SerreTwist
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type} [CommRing R] [Module.Flat ℤ R]
variable {d : ℕ}

local instance projectiveSpaceOverBaseForModuleExt :
    (scheme R d).Over (Spec (CommRingCat.of R)) :=
  ⟨toSpec R d⟩

/-- The standard affine cover is acyclic on intersections for every
quasicoherent module on projective space. -/
theorem standardCoverModule_isAcyclicOnIntersections
    (M : (scheme R d).Modules) [M.IsQuasicoherent] :
    IsAcyclicOnIntersections
      M.sheaf (standardChart R) Finset.univ := by
  intro t ht _ q hq
  letI : Nonempty ↥t :=
    Finset.nonempty_coe_sort.mpr ht
  have h :=
    Scheme.Modules.subsingleton_H'_of_isAffineOpen
      M (standardIntersection R (fun i : ↥t => i.1))
      (q - 1)
  rw [Nat.sub_add_cancel hq] at h
  rw [finiteIntersection_standardChart R d t]
  exact h

/-- Constant-source Ext for a quasicoherent projective-space module is
computed by the coefficient-linear standard-cover section complex. -/
noncomputable def constantBaseExtLinearIsoStandardCoverHomology
    (M : (scheme R d).Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    ModuleCat.of R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (moduleSheaf (k := R) M) n) ≅
      (finiteSubsetCechComplex
        (R := R)
        (sectionModule (standardChart R)
          (moduleSheaf (k := R) M))
        (sectionRestriction (standardChart R)
          (moduleSheaf (k := R) M))
        (sectionRestriction_comp (standardChart R)
          (moduleSheaf (k := R) M))).homology n :=
  constantBaseExtLinearIsoFiniteSubsetSectionHomology
    M (standardChart R) (iSup_standardChart R d)
    (standardCoverModule_isAcyclicOnIntersections M) n

/-- A normalized finite-subset complex indexed by the `d + 1` standard
charts has zero homology in every degree strictly larger than `d`. -/
theorem standardCoverSectionCechHomology_subsingleton
    (M : (scheme R d).Modules)
    (q : ℕ) (hq : d < q) :
    Subsingleton
      ((finiteSubsetCechComplex
        (R := R)
        (sectionModule (standardChart R)
          (moduleSheaf (k := R) M))
        (sectionRestriction (standardChart R)
          (moduleSheaf (k := R) M))
        (sectionRestriction_comp (standardChart R)
          (moduleSheaf (k := R) M))).homology q) := by
  let C :=
    finiteSubsetCechComplex
      (R := R)
      (sectionModule (standardChart R)
        (moduleSheaf (k := R) M))
      (sectionRestriction (standardChart R)
        (moduleSheaf (k := R) M))
      (sectionRestriction_comp (standardChart R)
        (moduleSheaf (k := R) M))
  letI : IsEmpty (Simplex (ι := Fin (d + 1)) q) :=
    ⟨fun I => by
      have hcard :
          I.1.card ≤ Fintype.card (Fin (d + 1)) :=
        Finset.card_le_univ I.1
      rw [I.2, Fintype.card_fin] at hcard
      omega⟩
  letI : Subsingleton (C.X q) := by
    change Subsingleton
      (FiniteSubsetCochain
        (sectionModule (standardChart R)
          (moduleSheaf (k := R) M)) q)
    infer_instance
  let hX : IsZero (C.X q) :=
    ModuleCat.isZero_of_subsingleton _
  exact
    ModuleCat.subsingleton_of_isZero
      ((HomologicalComplex.ExactAt.of_isZero hX).isZero_homology)

/-- Constant-source Ext of a quasicoherent module on `ℙ^d_R` vanishes
strictly above degree `d`. -/
theorem constantBaseExt_subsingleton_of_dimension_lt
    (M : (scheme R d).Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : d < q) :
    Subsingleton
      (Abelian.Ext
        (constantRankOneSheaf (R := R) (scheme R d))
        (moduleSheaf (k := R) M) q) := by
  let e :=
    (constantBaseExtLinearIsoStandardCoverHomology M q).toLinearEquiv
  letI :
      Subsingleton
        ((finiteSubsetCechComplex
          (R := R)
          (sectionModule (standardChart R)
            (moduleSheaf (k := R) M))
          (sectionRestriction (standardChart R)
            (moduleSheaf (k := R) M))
          (sectionRestriction_comp (standardChart R)
            (moduleSheaf (k := R) M))).homology q) :=
    standardCoverSectionCechHomology_subsingleton M q hq
  exact
    ⟨fun x y =>
      e.injective (Subsingleton.elim (e x) (e y))⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
