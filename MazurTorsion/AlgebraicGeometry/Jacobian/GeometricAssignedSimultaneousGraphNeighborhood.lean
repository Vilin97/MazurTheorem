/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedAffineRootCoordinates

/-!
# Simultaneous graph neighbourhoods on an assigned affine chart

For one split tuple sheet, every occurrence graph has an open neighbourhood
that removes the other étale sheets.  A union of those opens contains all
the selected graphs, but does not preserve every graph-ideal identity on the
whole union.  The correct common neighbourhood is their finite intersection,
after restricting the refinement base to the locus where every selected
graph lands in that intersection.

This file carries out that simultaneous restriction support by support.  It
then base changes each support intersection to the common base open and
exhibits every selected occurrence graph as a section there.  The named
downstream consumer is `PointedIncidenceDescent`, where this is the topology
needed before comparing the restricted incidence ideal with the full
independent-root graph product.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedSimultaneousGraphNeighborhood

open GeometricAssignedAffineChart
open GeometricAssignedAffineRootCoordinates
open EqualCoordinateClosedImmersion
open EtaleGraphNeighborhood
open FiniteSupportEtaleCoordinates
open SplitFiniteBaseChange
open SmoothCurveEtaleCoordinate

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K))) [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
variable {V : (commonAffineBase K C d z).left.Opens}
variable (hVs : (action K C d z).IsStableOpen V)
variable {T : Type u} [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
variable (m : ℕ)
variable (E : pullback ((componentToBasePower K C d z).left ∣_ V) q ≅
  Spec (.of (Fin m → T)))
variable (hE : E.hom ≫ EtaleSplitChart.splitProjection T m =
  pullback.snd ((componentToBasePower K C d z).left ∣_ V) q)

/-- Projection from a support-indexed curve-family ambient to the common
block-refinement base. -/
noncomputable def supportAmbientToBase
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    supportAmbient K C d z hVs q a ⟶
      (componentFpqcBlockRefinement K C d z hVs q).left :=
  pullback.snd
    ((affineComponentToCoordinateLine K C d z a).left ≫
      (coordinateLine K).hom)
    (refinementToBase K C d z hVs q ≫
      (commonAffineBase K C d z).hom)

@[reassoc]
theorem occurrenceAmbientIsoSupportAmbient_hom_snd (i : Fin d) :
    (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i) =
      pullback.snd
        ((affineComponentToCoordinateLine K C d z
          (geometricPointSupportIndex K C d z i)).left ≫
            (coordinateLine K).hom)
        (occurrenceCoordinate K C d z hVs q i ≫
          (coordinateLine K).hom) := by
  simp only [occurrenceAmbientIsoSupportAmbient,
    supportAmbientToBase, pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem supportEqualCoordinateInclusion_comp_base (i : Fin d) :
    (occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
        (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom) ≫
      supportAmbientToBase K C d z hVs q
        (geometricPointSupportIndex K C d z i) =
    pullback.snd
      (affineComponentToCoordinateLine K C d z
        (geometricPointSupportIndex K C d z i)).left
      (occurrenceCoordinate K C d z hVs q i) := by
  rw [Category.assoc,
    occurrenceAmbientIsoSupportAmbient_hom_snd]
  exact equalCoordinateInclusion_snd
    (coordinateLine K).hom
    (affineComponentToCoordinateLine K C d z
      (geometricPointSupportIndex K C d z i)).left
    (occurrenceCoordinate K C d z hVs q i)

@[reassoc]
theorem occurrenceGraph_comp_snd (j : Fin m) (i : Fin d) :
    occurrenceGraph K C d z hVs q m E hE j i ≫
        pullback.snd
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left :=
  pullback.lift_snd _ _ _

/-- The selected occurrence graph, viewed directly in its common support
ambient. -/
noncomputable def graphToSupportAmbient (j : Fin m) (i : Fin d) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      supportAmbient K C d z hVs q
        (geometricPointSupportIndex K C d z i) :=
  occurrenceGraph K C d z hVs q m E hE j i ≫
    occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
      (occurrenceAmbientIsoSupportAmbient K C d z hVs q i).hom

@[reassoc]
theorem graphToSupportAmbient_comp_base (j : Fin m) (i : Fin d) :
    graphToSupportAmbient K C d z hVs q m E hE j i ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i) =
      𝟙 (componentFpqcBlockRefinement K C d z hVs q).left := by
  calc
    graphToSupportAmbient K C d z hVs q m E hE j i ≫
          supportAmbientToBase K C d z hVs q
            (geometricPointSupportIndex K C d z i) =
        occurrenceGraph K C d z hVs q m E hE j i ≫
          ((occurrenceEqualCoordinateInclusion K C d z hVs q i ≫
              (occurrenceAmbientIsoSupportAmbient
                K C d z hVs q i).hom) ≫
            supportAmbientToBase K C d z hVs q
              (geometricPointSupportIndex K C d z i)) := by
      simp only [graphToSupportAmbient, Category.assoc]
    _ = occurrenceGraph K C d z hVs q m E hE j i ≫
        pullback.snd
          (affineComponentToCoordinateLine K C d z
            (geometricPointSupportIndex K C d z i)).left
          (occurrenceCoordinate K C d z hVs q i) := by
      rw [supportEqualCoordinateInclusion_comp_base]
    _ = 𝟙 (componentFpqcBlockRefinement K C d z hVs q).left :=
      occurrenceGraph_comp_snd K C d z hVs q m E hE j i

/-- The simultaneous support neighbourhood is the intersection of all
chosen occurrence-isolating opens in the one curve-family ambient. -/
noncomputable def supportIntersectionOpen (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z)) :
    (supportAmbient K C d z hVs q a).Opens :=
  ⨅ i : OccurrencesAtSupport K C d z a,
    occurrenceOpenAtSupport K C d z hVs q m E hE j a i

theorem supportIntersectionOpen_le_occurrenceOpenAtSupport (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    supportIntersectionOpen K C d z hVs q m E hE j a ≤
      occurrenceOpenAtSupport K C d z hVs q m E hE j a i :=
  iInf_le (fun i : OccurrencesAtSupport K C d z a ↦
    occurrenceOpenAtSupport K C d z hVs q m E hE j a i) i

/-- A support-owned occurrence graph with its codomain rewritten using the
proof that its owner is `a`. -/
noncomputable def graphToSupportAmbientAtSupport (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left ⟶
      supportAmbient K C d z hVs q a := by
  rcases i with ⟨i, rfl⟩
  exact graphToSupportAmbient K C d z hVs q m E hE j i

/-- The base locus on which one occurrence graph lands in the common
intersection for its support owner. -/
noncomputable abbrev supportAdmissibleBaseOpen (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
  graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ⁻¹ᵁ
    supportIntersectionOpen K C d z hVs q m E hE j a

/-- Restrict the refinement base until every occurrence graph lands in the
common intersection belonging to every support owner. -/
noncomputable def simultaneousBaseOpen (j : Fin m) :
    (componentFpqcBlockRefinement K C d z hVs q).left.Opens :=
  ⨅ a : Fin (geometricDistinctSupportCard K C d z),
    ⨅ i : OccurrencesAtSupport K C d z a,
      supportAdmissibleBaseOpen K C d z hVs q m E hE j a i

theorem simultaneousBaseOpen_le_supportAdmissibleBaseOpen (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    simultaneousBaseOpen K C d z hVs q m E hE j ≤
      supportAdmissibleBaseOpen K C d z hVs q m E hE j a i :=
  iInf_le_of_le a (iInf_le_of_le i le_rfl)

/-- After the common base restriction, every selected graph factors through
the intersection of all isolating opens belonging to its support owner. -/
noncomputable def graphToSupportIntersection (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (simultaneousBaseOpen K C d z hVs q m E hE j).toScheme ⟶
      (supportIntersectionOpen K C d z hVs q m E hE j a).toScheme :=
  (componentFpqcBlockRefinement K C d z hVs q).left.homOfLE
      (simultaneousBaseOpen_le_supportAdmissibleBaseOpen
        K C d z hVs q m E hE j a i) ≫
    (graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i ∣_
      supportIntersectionOpen K C d z hVs q m E hE j a)

@[reassoc]
theorem graphToSupportIntersection_comp_ι (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportIntersection K C d z hVs q m E hE j a i ≫
        (supportIntersectionOpen K C d z hVs q m E hE j a).ι =
      (simultaneousBaseOpen K C d z hVs q m E hE j).ι ≫
        graphToSupportAmbientAtSupport K C d z hVs q m E hE j a i := by
  rw [graphToSupportIntersection, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- Every restricted occurrence graph is a section over the simultaneous
base open. -/
@[reassoc]
theorem graphToSupportIntersection_comp_base (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportIntersection K C d z hVs q m E hE j a i ≫
        (supportIntersectionOpen K C d z hVs q m E hE j a).ι ≫
          supportAmbientToBase K C d z hVs q a =
      (simultaneousBaseOpen K C d z hVs q m E hE j).ι := by
  rw [← Category.assoc, graphToSupportIntersection_comp_ι,
    Category.assoc]
  rcases i with ⟨i, rfl⟩
  change (simultaneousBaseOpen K C d z hVs q m E hE j).ι ≫
      graphToSupportAmbient K C d z hVs q m E hE j i ≫
        supportAmbientToBase K C d z hVs q
          (geometricPointSupportIndex K C d z i) =
    (simultaneousBaseOpen K C d z hVs q m E hE j).ι
  rw [graphToSupportAmbient_comp_base, Category.comp_id]

/-- Base change the simultaneous support intersection to the common base
open on which all selected graphs land in it. -/
noncomputable abbrev supportIntersectionBaseChange (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z)) : Scheme.{u} :=
  pullback
    ((supportIntersectionOpen K C d z hVs q m E hE j a).ι ≫
      supportAmbientToBase K C d z hVs q a)
    (simultaneousBaseOpen K C d z hVs q m E hE j).ι

/-- The selected occurrence graph as a genuine section of the base-changed
simultaneous support neighbourhood. -/
noncomputable def graphToSupportIntersectionBaseChange (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    (simultaneousBaseOpen K C d z hVs q m E hE j).toScheme ⟶
      supportIntersectionBaseChange K C d z hVs q m E hE j a :=
  pullback.lift
    (graphToSupportIntersection K C d z hVs q m E hE j a i)
    (𝟙 _)
    (by
      simpa only [Category.id_comp] using
        (graphToSupportIntersection_comp_base
          K C d z hVs q m E hE j a i))

@[reassoc]
theorem graphToSupportIntersectionBaseChange_comp_snd (j : Fin m)
    (a : Fin (geometricDistinctSupportCard K C d z))
    (i : OccurrencesAtSupport K C d z a) :
    graphToSupportIntersectionBaseChange
        K C d z hVs q m E hE j a i ≫
      pullback.snd
        ((supportIntersectionOpen K C d z hVs q m E hE j a).ι ≫
          supportAmbientToBase K C d z hVs q a)
        (simultaneousBaseOpen K C d z hVs q m E hE j).ι =
      𝟙 (simultaneousBaseOpen K C d z hVs q m E hE j).toScheme :=
  pullback.lift_snd _ _ _

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedSimultaneousGraphNeighborhood
