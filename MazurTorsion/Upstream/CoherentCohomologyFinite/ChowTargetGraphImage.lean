/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowGraphToProjectiveClosure

/-!
# The Chow graph image inside the target-closure product

The relative graph first lands in the product of the original scheme
with the projective target closure.  Its scheme-theoretic image there
is canonically isomorphic to the graph closure originally formed in
the larger relative projective space.  This smaller realization is the
convenient one for restricting along opens of the target closure.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

namespace ChowRationalProjectiveMapData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (D : ChowRationalProjectiveMapData f)

/-- The scheme-theoretic image of the factored graph in
`X × D.targetClosure`. -/
abbrev targetGraphImage : Scheme.{u} :=
  D.graphToTargetRelative.image

/-- The original graph map into relative projective space factors
through the closed immersion of the smaller graph image. -/
theorem relativeProjectiveGraph_factor_targetGraphImage :
    relativeProjectiveGraph
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase =
      D.graphToTargetRelative.toImage ≫
        (D.graphToTargetRelative.imageι ≫
          D.targetRelativeToRelativeProjective) := by
  rw [← Category.assoc,
    Scheme.Hom.toImage_imageι,
    D.graphToTargetRelative_targetRelativeToRelativeProjective]

/-- The original graph closure maps canonically to the smaller graph
image. -/
def graphClosureToTargetGraphImage :
    projectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase ⟶
      D.targetGraphImage := by
  letI :
      IsClosedImmersion
        D.targetRelativeToRelativeProjective :=
    D.isClosedImmersion_targetRelativeToRelativeProjective
  letI :
      IsClosedImmersion
        (D.graphToTargetRelative.imageι ≫
          D.targetRelativeToRelativeProjective) :=
    inferInstance
  exact
    SchemeTheoreticImage.toClosedFactor
      (relativeProjectiveGraph
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase)
      D.graphToTargetRelative.toImage
      (D.graphToTargetRelative.imageι ≫
        D.targetRelativeToRelativeProjective)
      D.relativeProjectiveGraph_factor_targetGraphImage

/-- The smaller graph image maps canonically back to the original
graph closure. -/
def targetGraphImageToGraphClosure :
    D.targetGraphImage ⟶
      projectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase := by
  letI :
      IsClosedImmersion D.graphClosureToTargetRelative :=
    D.isClosedImmersion_graphClosureToTargetRelative
  letI :
      IsClosedImmersion
        D.targetRelativeToRelativeProjective :=
    D.isClosedImmersion_targetRelativeToRelativeProjective
  exact
    SchemeTheoreticImage.toClosedFactor
      D.graphToTargetRelative
      (relativeProjectiveGraph
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase).toImage
      D.graphClosureToTargetRelative
      (by
        apply
          (cancel_mono
            D.targetRelativeToRelativeProjective).mp
        rw [D.graphToTargetRelative_targetRelativeToRelativeProjective]
        rw [Category.assoc]
        unfold graphClosureToTargetRelative
        rw [SchemeTheoreticImage.toClosedFactor_comp,
          Scheme.Hom.toImage_imageι])

/-- The map from the original closure to the smaller image recovers
its closed immersion in the target-relative product. -/
@[reassoc]
theorem graphClosureToTargetGraphImage_imageι :
    D.graphClosureToTargetGraphImage ≫
        D.graphToTargetRelative.imageι =
      D.graphClosureToTargetRelative := by
  letI :
      IsClosedImmersion
        D.targetRelativeToRelativeProjective :=
    D.isClosedImmersion_targetRelativeToRelativeProjective
  apply
    (cancel_mono
      D.targetRelativeToRelativeProjective).mp
  rw [Category.assoc]
  unfold graphClosureToTargetGraphImage
  rw [SchemeTheoreticImage.toClosedFactor_comp]
  unfold graphClosureToTargetRelative
  rw [SchemeTheoreticImage.toClosedFactor_comp]

/-- The reverse map also recovers the closed immersion of the smaller
image. -/
@[reassoc]
theorem targetGraphImageToGraphClosure_graphClosureToTargetRelative :
    D.targetGraphImageToGraphClosure ≫
        D.graphClosureToTargetRelative =
      D.graphToTargetRelative.imageι := by
  letI :
      IsClosedImmersion D.graphClosureToTargetRelative :=
    D.isClosedImmersion_graphClosureToTargetRelative
  unfold targetGraphImageToGraphClosure
  rw [SchemeTheoreticImage.toClosedFactor_comp]

/-- The two realizations of the graph closure are canonically
isomorphic. -/
def graphClosureIsoTargetGraphImage :
    projectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase ≅
      D.targetGraphImage where
  hom := D.graphClosureToTargetGraphImage
  inv := D.targetGraphImageToGraphClosure
  hom_inv_id := by
    letI :
        IsClosedImmersion D.graphClosureToTargetRelative :=
      D.isClosedImmersion_graphClosureToTargetRelative
    apply (cancel_mono D.graphClosureToTargetRelative).mp
    rw [Category.assoc,
      D.targetGraphImageToGraphClosure_graphClosureToTargetRelative,
      D.graphClosureToTargetGraphImage_imageι,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono D.graphToTargetRelative.imageι).mp
    rw [Category.assoc,
      D.graphClosureToTargetGraphImage_imageι,
      D.targetGraphImageToGraphClosure_graphClosureToTargetRelative,
      Category.id_comp]

/-- Under the canonical isomorphism, the projection to the target
closure is the second projection of the smaller graph image. -/
@[reassoc]
theorem graphClosureIsoTargetGraphImage_hom_target :
    D.graphClosureIsoTargetGraphImage.hom ≫
        D.graphToTargetRelative.imageι ≫
          pullback.snd f D.targetClosureToSpec =
      D.graphClosureToTargetClosure := by
  dsimp only [graphClosureIsoTargetGraphImage]
  rw [← Category.assoc,
    D.graphClosureToTargetGraphImage_imageι]
  rfl

end ChowRationalProjectiveMapData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
