/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetSectionCechComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistStandardCechComplex
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentChartIndependence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistAcyclicCover

/-!
# Section Čech comparison for integer Serre twists

The normalized sheaf-section complex on the standard projective cover is
identified with the explicit Laurent-coordinate Čech complex, assuming the
geometric chart-independence statement isolated below.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

local instance projectiveSpaceOverQ (d : ℕ) :
    (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
  ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩

/-- Transport between values of a module presheaf along equality of
opens, retaining the bundled linear structure. -/
def modulePresheafValueCastLinearEquiv
    {T : TopCat}
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat ℚ)
    {V W : Opens T} (h : V = W) :
    P.obj (op V) ≃ₗ[ℚ] P.obj (op W) := by
  subst W
  exact LinearEquiv.refl ℚ _

/-- Equality transport on both opens commutes with the restriction map of
a module presheaf. -/
lemma modulePresheafValueCastLinearEquiv_map
    {T : TopCat}
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat ℚ)
    {V W V' W' : Opens T}
    (hV : V = V') (hW : W = W')
    (i : W ≤ V) (i' : W' ≤ V')
    (x : P.obj (op V)) :
    modulePresheafValueCastLinearEquiv P hW
        (P.map (homOfLE i).op x) =
      P.map (homOfLE i').op
        (modulePresheafValueCastLinearEquiv P hV x) := by
  subst V'
  subst W'
  change P.map (homOfLE i).op x =
    P.map (homOfLE i').op x
  congr

/-- The finite intersection used in the free-sheaf resolution is the
usual Laurent open of the standard projective cover. -/
lemma standardCoverIntersection_eq_laurentOpen
    (d : ℕ) (I : Finset (Fin (d + 1))) :
    intersection (standardChart ℚ) I =
      laurentOpen ℚ d I := by
  change finiteIntersection (standardChart ℚ) I =
    laurentOpen ℚ d I
  rw [finiteIntersection_standardChart]
  change standardFinsetIntersection ℚ d I =
    laurentOpen ℚ d I
  exact standardFinsetIntersection_eq_laurentOpen ℚ d I

/-- Laurent coordinates for the sections on one finite standard-cover
intersection. -/
def standardCoverIntersectionSectionsLinearEquiv
    (d : ℕ) (m : ℤ) {q : ℕ}
    (I : Simplex (ι := Fin (d + 1)) q) :
    (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (op (intersection (standardChart ℚ) I.1)) ≃ₗ[ℚ]
      MonomialModule (ι := Fin (d + 1)) ℚ m I.1 := by
  exact
    (modulePresheafValueCastLinearEquiv
      (Geometric.moduleSheaf (OInt ℚ d m)).obj
      (standardCoverIntersection_eq_laurentOpen d I.1)).trans
        (standardCoverOIntSimplexSectionsLinearEquiv d m I)

@[simp]
lemma standardCoverIntersectionSectionsLinearEquiv_apply
    (d : ℕ) (m : ℤ) {q : ℕ}
    (I : Simplex (ι := Fin (d + 1)) q)
    (x : (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
      (op (intersection (standardChart ℚ) I.1))) :
    standardCoverIntersectionSectionsLinearEquiv d m I x =
      integerChartLaurentSectionsLinearEquiv d m I.1
        (standardCoverSimplexChosenVertex I)
        (modulePresheafValueCastLinearEquiv
          (Geometric.moduleSheaf (OInt ℚ d m)).obj
          (standardCoverIntersection_eq_laurentOpen d I.1) x) :=
  rfl

/-- The precise restriction-naturality statement needed to compare the
sheaf section complex with Laurent coordinates. -/
structure StandardCoverCoordinatesNatural
    (d : ℕ) (m : ℤ) : Prop where
  restriction :
    ∀ {q : ℕ}
      (J : Simplex (ι := Fin (d + 1)) (q + 1))
      (j : ↥J.1)
      (x : sectionModule (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m))
        (J.1.erase j.1)),
      standardCoverIntersectionSectionsLinearEquiv d m J
          (sectionRestriction (standardChart ℚ)
            (Geometric.moduleSheaf (OInt ℚ d m))
            (Finset.erase_subset j.1 J.1) x) =
        restriction (R := ℚ)
          (Finset.erase_subset j.1 J.1)
          (standardCoverIntersectionSectionsLinearEquiv
            d m (J.erase j.1 j.2) x)

/-- Chart-independence of Laurent coordinates on every nonempty Laurent
open. -/
structure IntegerChartCoordinatesIndependent
    (d : ℕ) (m : ℤ) : Prop where
  coordinate_eq :
    ∀ (I : Finset (Fin (d + 1))) (i j : ↥I)
      (x : (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (op (laurentOpen ℚ d I))),
      integerChartLaurentSectionsLinearEquiv d m I i x =
        integerChartLaurentSectionsLinearEquiv d m I j x

/-- Transporting a section restriction from finite standard intersections
to Laurent opens gives the canonical Laurent-open restriction. -/
lemma standardCoverIntersectionRestriction_cast
    (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J)
    (x : sectionModule (standardChart ℚ)
      (Geometric.moduleSheaf (OInt ℚ d m)) I) :
    modulePresheafValueCastLinearEquiv
        (Geometric.moduleSheaf (OInt ℚ d m)).obj
        (standardCoverIntersection_eq_laurentOpen d J)
        (sectionRestriction (standardChart ℚ)
          (Geometric.moduleSheaf (OInt ℚ d m)) hIJ x) =
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.map
        (homOfLE (laurentOpen_mono ℚ d hIJ)).op
        (modulePresheafValueCastLinearEquiv
          (Geometric.moduleSheaf (OInt ℚ d m)).obj
          (standardCoverIntersection_eq_laurentOpen d I) x) := by
  exact modulePresheafValueCastLinearEquiv_map
    (Geometric.moduleSheaf (OInt ℚ d m)).obj
    (standardCoverIntersection_eq_laurentOpen d I)
    (standardCoverIntersection_eq_laurentOpen d J)
    (intersection_anti (standardChart ℚ) hIJ)
    (laurentOpen_mono ℚ d hIJ)
    x

/-- Restriction is compatible with Laurent coordinates when the source
chart is retained on the target intersection. -/
lemma standardCoverCoordinateRestriction_same_chart
    (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (i : ↥I)
    (x : sectionModule (standardChart ℚ)
      (Geometric.moduleSheaf (OInt ℚ d m)) I) :
    integerChartLaurentSectionsLinearEquiv d m J
        ⟨i.1, hIJ i.2⟩
        (modulePresheafValueCastLinearEquiv
          (Geometric.moduleSheaf (OInt ℚ d m)).obj
          (standardCoverIntersection_eq_laurentOpen d J)
          (sectionRestriction (standardChart ℚ)
            (Geometric.moduleSheaf (OInt ℚ d m)) hIJ x)) =
      restriction (R := ℚ) hIJ
        (integerChartLaurentSectionsLinearEquiv d m I i
          (modulePresheafValueCastLinearEquiv
            (Geometric.moduleSheaf (OInt ℚ d m)).obj
            (standardCoverIntersection_eq_laurentOpen d I) x)) := by
  rw [standardCoverIntersectionRestriction_cast d m hIJ x]
  exact integerChartLaurentSectionsLinearEquiv_restriction
    d m hIJ i
      (modulePresheafValueCastLinearEquiv
        (Geometric.moduleSheaf (OInt ℚ d m)).obj
        (standardCoverIntersection_eq_laurentOpen d I) x)

/-- Chart independence identifies the canonical simplex coordinate with
the coordinate in any selected chart of that simplex. -/
lemma standardCoverIntersectionSectionsLinearEquiv_eq_chart
    (d : ℕ) (m : ℤ)
    (hchart : IntegerChartCoordinatesIndependent d m)
    {q : ℕ}
    (I : Simplex (ι := Fin (d + 1)) q)
    (i : ↥I.1)
    (x : sectionModule (standardChart ℚ)
      (Geometric.moduleSheaf (OInt ℚ d m)) I.1) :
    standardCoverIntersectionSectionsLinearEquiv d m I x =
      integerChartLaurentSectionsLinearEquiv d m I.1 i
        (modulePresheafValueCastLinearEquiv
          (Geometric.moduleSheaf (OInt ℚ d m)).obj
          (standardCoverIntersection_eq_laurentOpen d I.1) x) := by
  exact
    (standardCoverIntersectionSectionsLinearEquiv_apply
      d m I x).trans
      (hchart.coordinate_eq I.1
        (standardCoverSimplexChosenVertex I) i
        (modulePresheafValueCastLinearEquiv
          (Geometric.moduleSheaf (OInt ℚ d m)).obj
          (standardCoverIntersection_eq_laurentOpen d I.1) x))

/-- One face restriction commutes with Laurent coordinates when those
coordinates are chart-independent. -/
lemma standardCoverCoordinateRestriction_of_chart_independent
    (d : ℕ) (m : ℤ)
    (hchart : IntegerChartCoordinatesIndependent d m) :
    ∀ {q : ℕ}
      (J : Simplex (ι := Fin (d + 1)) (q + 1))
      (j : ↥J.1)
      (x : sectionModule (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m))
        (J.1.erase j.1)),
      standardCoverIntersectionSectionsLinearEquiv d m J
          (sectionRestriction (standardChart ℚ)
            (Geometric.moduleSheaf (OInt ℚ d m))
            (Finset.erase_subset j.1 J.1) x) =
        restriction (R := ℚ)
          (Finset.erase_subset j.1 J.1)
          (standardCoverIntersectionSectionsLinearEquiv
            d m (J.erase j.1 j.2) x) := by
  intro q J j x
  let I : Simplex (ι := Fin (d + 1)) q :=
    J.erase j.1 j.2
  let i : ↥I.1 := standardCoverSimplexChosenVertex I
  let iJ : ↥J.1 :=
    ⟨i.1, Finset.erase_subset j.1 J.1 i.2⟩
  have htarget :
      standardCoverIntersectionSectionsLinearEquiv d m J
          (sectionRestriction (standardChart ℚ)
            (Geometric.moduleSheaf (OInt ℚ d m))
            (Finset.erase_subset j.1 J.1) x) =
        integerChartLaurentSectionsLinearEquiv
          d m J.1 iJ
          (modulePresheafValueCastLinearEquiv
            (Geometric.moduleSheaf (OInt ℚ d m)).obj
            (standardCoverIntersection_eq_laurentOpen d J.1)
            (sectionRestriction (standardChart ℚ)
              (Geometric.moduleSheaf (OInt ℚ d m))
              (Finset.erase_subset j.1 J.1) x)) :=
    standardCoverIntersectionSectionsLinearEquiv_eq_chart
      d m hchart J iJ
      (sectionRestriction (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m))
        (Finset.erase_subset j.1 J.1) x)
  have hsame :=
    standardCoverCoordinateRestriction_same_chart
      d m (Finset.erase_subset j.1 J.1) i x
  have hsource :=
    standardCoverIntersectionSectionsLinearEquiv_apply
      d m I x
  exact htarget.trans <| hsame.trans <|
    congrArg
      (restriction (R := ℚ)
        (Finset.erase_subset j.1 J.1))
      hsource.symm

/-- Chart-independent Laurent coordinates commute with every face
restriction of the normalized standard-cover complex. -/
theorem standardCoverCoordinatesNatural_of_chart_independent
    (d : ℕ) (m : ℤ)
    (hchart : IntegerChartCoordinatesIndependent d m) :
    StandardCoverCoordinatesNatural d m where
  restriction J j x :=
    standardCoverCoordinateRestriction_of_chart_independent
      d m hchart J j x

/-- Under restriction-natural Laurent coordinates, the target-oriented
section complex of the standard projective cover is the normalized Laurent
Čech complex. -/
def standardCoverSectionPiCechComplexIsoStandardCech
    (d : ℕ) (m : ℤ)
    (hcoord : StandardCoverCoordinatesNatural d m) :
    sectionPiCechComplex (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m)) ≅
      standardCoverOIntCechComplex d m := by
  let A := sectionModule (standardChart ℚ)
    (Geometric.moduleSheaf (OInt ℚ d m))
  let resA : ∀ {I J : Finset (Fin (d + 1))},
      I ⊆ J → A I →ₗ[ℚ] A J :=
    fun {_ _} hIJ =>
      sectionRestriction (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m)) hIJ
  let B := fun I : Finset (Fin (d + 1)) =>
    MonomialModule (ι := Fin (d + 1)) ℚ m I
  let resB : ∀ {I J : Finset (Fin (d + 1))},
      I ⊆ J → B I →ₗ[ℚ] B J :=
    fun {_ _} hIJ =>
      restriction (R := ℚ) (d := m) hIJ
  exact
    (sectionPiCechComplexIsoGeneric
      (standardChart ℚ)
      (Geometric.moduleSheaf (OInt ℚ d m))).trans <|
      (finiteSubsetPiCechComplexIsoOfLinearEquiv
        A resA B resB
        (sectionRestriction_comp
          (standardChart ℚ)
          (Geometric.moduleSheaf (OInt ℚ d m)))
        (standardCoverLaurentRestriction_comp d m)
        (fun I =>
          standardCoverIntersectionSectionsLinearEquiv d m I)
        hcoord.restriction).trans <|
        (finiteSubsetCechComplexIsoPi B resB
          (standardCoverLaurentRestriction_comp d m)).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
