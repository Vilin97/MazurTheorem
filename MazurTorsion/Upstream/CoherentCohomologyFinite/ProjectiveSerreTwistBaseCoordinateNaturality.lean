/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseLinearStandardCech

/-!
# Naturality of base-linear Laurent coordinates

The chart-independent Laurent description of integer-twist sections
commutes with every face restriction in the finite standard projective
cover.  This discharges the coordinate-naturality hypothesis used by the
base-linear Čech comparison over every commutative coefficient ring.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

local instance projectiveSpaceOverCoefficientRingForCoordinateNaturality
    (k : Type) [CommRing k] (d : ℕ) :
    (scheme k d).Over (Spec (CommRingCat.of k)) :=
  ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩

/-- Equality transport on both opens commutes with restriction for a
module-valued presheaf over an arbitrary coefficient ring. -/
lemma modulePresheafValueCastLinearEquivOver_map
    {k : Type} [CommRing k] {T : TopCat}
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat k)
    {V W V' W' : Opens T}
    (hV : V = V') (hW : W = W')
    (i : W ≤ V) (i' : W' ≤ V')
    (x : P.obj (op V)) :
    modulePresheafValueCastLinearEquivOver P hW
        (P.map (homOfLE i).op x) =
      P.map (homOfLE i').op
        (modulePresheafValueCastLinearEquivOver P hV x) := by
  subst V'
  subst W'
  change P.map (homOfLE i).op x =
    P.map (homOfLE i').op x
  congr

/-- The finite standard-cover intersection is the corresponding Laurent
basic open. -/
lemma baseStandardCoverIntersection_eq_laurentOpen
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) :
    intersection (standardChart k) I =
      laurentOpen k d I :=
  (standardCoverIntersection_eq_standardIntersection
    k d I).trans
      (standardFinsetIntersection_eq_laurentOpen k d I)

@[simp]
lemma baseStandardCoverSectionsLinearEquiv_apply
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {q : ℕ} (I : Simplex (ι := Fin (d + 1)) q)
    (x : baseStandardSectionModule k d m I.1) :
    baseStandardCoverSectionsLinearEquiv k d m I x =
      integerChartLaurentSectionsLinearEquivOver
        k d m I.1 (standardCoverSimplexChosenVertex I)
        (modulePresheafValueCastLinearEquivOver
          (moduleSheaf (k := k) (OInt k d m)).obj
          (baseStandardCoverIntersection_eq_laurentOpen
            k d I.1) x) :=
  rfl

/-- Transporting a base-linear standard-cover restriction to Laurent
opens gives the canonical Laurent-open restriction. -/
lemma baseStandardCoverRestriction_cast
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J)
    (x : baseStandardSectionModule k d m I) :
    modulePresheafValueCastLinearEquivOver
        (moduleSheaf (k := k) (OInt k d m)).obj
        (baseStandardCoverIntersection_eq_laurentOpen
          k d J)
        (baseStandardSectionRestriction k d m hIJ x) =
      (moduleSheaf (k := k) (OInt k d m)).obj.map
        (homOfLE (laurentOpen_mono k d hIJ)).op
        (modulePresheafValueCastLinearEquivOver
          (moduleSheaf (k := k) (OInt k d m)).obj
          (baseStandardCoverIntersection_eq_laurentOpen
            k d I) x) := by
  exact modulePresheafValueCastLinearEquivOver_map
    (moduleSheaf (k := k) (OInt k d m)).obj
    (baseStandardCoverIntersection_eq_laurentOpen k d I)
    (baseStandardCoverIntersection_eq_laurentOpen k d J)
    (intersection_anti (standardChart k) hIJ)
    (laurentOpen_mono k d hIJ)
    x

/-- Restriction commutes with the base-linear Laurent equivalence when
the source chart remains in the target intersection. -/
lemma baseStandardCoverCoordinateRestriction_same_chart
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (i : ↥I)
    (x : baseStandardSectionModule k d m I) :
    integerChartLaurentSectionsLinearEquivOver
        k d m J ⟨i.1, hIJ i.2⟩
        (modulePresheafValueCastLinearEquivOver
          (moduleSheaf (k := k) (OInt k d m)).obj
          (baseStandardCoverIntersection_eq_laurentOpen
            k d J)
          (baseStandardSectionRestriction k d m hIJ x)) =
      restriction (R := k) hIJ
        (integerChartLaurentSectionsLinearEquivOver
          k d m I i
          (modulePresheafValueCastLinearEquivOver
            (moduleSheaf (k := k) (OInt k d m)).obj
            (baseStandardCoverIntersection_eq_laurentOpen
              k d I) x)) := by
  rw [baseStandardCoverRestriction_cast k d m hIJ x]
  simp only [integerChartLaurentSectionsLinearEquivOver_apply]
  exact integerChartLaurentCoordinateOver_restriction
    k d m hIJ i
      (modulePresheafValueCastLinearEquivOver
        (moduleSheaf (k := k) (OInt k d m)).obj
        (baseStandardCoverIntersection_eq_laurentOpen
          k d I) x)

/-- The canonical simplex coordinate equals the coordinate in any chosen
chart of that simplex. -/
lemma baseStandardCoverSectionsLinearEquiv_eq_chart
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {q : ℕ} (I : Simplex (ι := Fin (d + 1)) q)
    (i : ↥I.1)
    (x : baseStandardSectionModule k d m I.1) :
    baseStandardCoverSectionsLinearEquiv k d m I x =
      integerChartLaurentSectionsLinearEquivOver
        k d m I.1 i
        (modulePresheafValueCastLinearEquivOver
          (moduleSheaf (k := k) (OInt k d m)).obj
          (baseStandardCoverIntersection_eq_laurentOpen
            k d I.1) x) := by
  rw [baseStandardCoverSectionsLinearEquiv_apply]
  simp only [integerChartLaurentSectionsLinearEquivOver_apply]
  exact integerChartLaurentCoordinateOver_eq
    k d m I.1 (standardCoverSimplexChosenVertex I) i
      (modulePresheafValueCastLinearEquivOver
        (moduleSheaf (k := k) (OInt k d m)).obj
        (baseStandardCoverIntersection_eq_laurentOpen
          k d I.1) x)

/-- One face restriction commutes with the canonical base-linear Laurent
coordinates. -/
lemma baseStandardCoverCoordinateRestriction
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ) :
    ∀ {q : ℕ}
      (J : Simplex (ι := Fin (d + 1)) (q + 1))
      (j : ↥J.1)
      (x : baseStandardSectionModule k d m
        (J.1.erase j.1)),
      baseStandardCoverSectionsLinearEquiv k d m J
          (baseStandardSectionRestriction k d m
            (Finset.erase_subset j.1 J.1) x) =
        restriction (R := k)
          (Finset.erase_subset j.1 J.1)
          (baseStandardCoverSectionsLinearEquiv
            k d m (J.erase j.1 j.2) x) := by
  intro q J j x
  let I : Simplex (ι := Fin (d + 1)) q :=
    J.erase j.1 j.2
  let i : ↥I.1 := standardCoverSimplexChosenVertex I
  let iJ : ↥J.1 :=
    ⟨i.1, Finset.erase_subset j.1 J.1 i.2⟩
  have htarget :
      baseStandardCoverSectionsLinearEquiv k d m J
          (baseStandardSectionRestriction k d m
            (Finset.erase_subset j.1 J.1) x) =
        integerChartLaurentSectionsLinearEquivOver
          k d m J.1 iJ
          (modulePresheafValueCastLinearEquivOver
            (moduleSheaf (k := k) (OInt k d m)).obj
            (baseStandardCoverIntersection_eq_laurentOpen
              k d J.1)
            (baseStandardSectionRestriction k d m
              (Finset.erase_subset j.1 J.1) x)) :=
    baseStandardCoverSectionsLinearEquiv_eq_chart
      k d m J iJ
      (baseStandardSectionRestriction k d m
        (Finset.erase_subset j.1 J.1) x)
  have hsame :=
    baseStandardCoverCoordinateRestriction_same_chart
      k d m (Finset.erase_subset j.1 J.1) i x
  have hsource :=
    baseStandardCoverSectionsLinearEquiv_apply
      k d m I x
  exact htarget.trans <| hsame.trans <|
    congrArg
      (restriction (R := k)
        (Finset.erase_subset j.1 J.1))
      hsource.symm

/-- Laurent coordinates on the finite standard cover are restriction
natural over every commutative coefficient ring and for every integer
Serre twist. -/
theorem baseStandardCoverCoordinatesNatural
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ) :
    BaseStandardCoverCoordinatesNatural k d m where
  restriction J j x :=
    baseStandardCoverCoordinateRestriction
      k d m J j x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
