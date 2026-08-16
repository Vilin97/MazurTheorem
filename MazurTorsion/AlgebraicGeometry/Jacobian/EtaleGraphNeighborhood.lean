/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EqualCoordinateClosedImmersion

/-!
# Open neighbourhoods isolating étale graphs

Let `X → S` be separated and étale, let `B → S` be arbitrary, and choose a
lift `B → X`.  Inside `X ×[G] B`, equality of the two `S`-coordinates is a
closed subscheme.  Its étale graph is an open-and-closed component.  Removing
the other components from the relative ambient product produces an open
neighbourhood in which the whole equal-coordinate closed subscheme is exactly
the chosen graph.

The named downstream consumer is `GeometricAssignedIncidenceNeighborhood`,
which applies the construction to every ordered occurrence in a coherent
split support chart.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphNeighborhood

open ClosedComponentNeighborhood
open EqualCoordinateClosedImmersion
open EtaleGraphCoproduct

variable {G S X B : Scheme.{u}}
variable (s : S ⟶ G) (f : X ⟶ S) [Etale f] [IsSeparated f]
variable (q : B ⟶ S) (sectionMap : B ⟶ X)
variable (sectionMap_coordinate : sectionMap ≫ f = q)

/-- The graph of the chosen lift in the equal-coordinate fiber product. -/
noncomputable abbrev graph : B ⟶ pullback f q :=
  pullback.lift sectionMap (𝟙 B) (by
    simpa only [Category.id_comp] using sectionMap_coordinate)

/-- After deleting the complementary equal-coordinate sheets, the selected
graph is the entire pullback of the equal-coordinate closed subscheme. -/
theorem exists_open_graph_isPullback [IsSeparated s] :
    ∃ (W : Scheme.{u}) (E : pullback f q ≅ B ⨿ W)
      (U : (ambient s f q).Opens) (graphToU : B ⟶ U.toScheme),
      graph f q sectionMap sectionMap_coordinate ≫ E.hom = coprod.inl ∧
      IsPullback graphToU
        (graph f q sectionMap sectionMap_coordinate) U.ι
        (equalCoordinateInclusion s f q) := by
  obtain ⟨W, E, hE⟩ := exists_graphCoproduct_of_etale
    f q sectionMap sectionMap_coordinate
  let b : B ⟶ pullback f q := leftSummand E
  have hgraph : graph f q sectionMap sectionMap_coordinate = b := by
    apply (cancel_mono E.hom).mp
    rw [hE]
    simp only [b, leftSummand, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  obtain ⟨U, graphToU, hU⟩ :=
    exists_open_isPullback_firstSummand
      (equalCoordinateInclusion s f q) E
  refine ⟨W, E, U, graphToU, hE, ?_⟩
  rw [hgraph]
  exact hU

end MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphNeighborhood
