/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowRationalProjectiveClosure
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeTheoreticImageClosedFactor

/-!
# The Chow graph over the projective target closure

The relative graph factors through the fiber product with the
scheme-theoretic closure of its projective component.  Taking
scheme-theoretic images therefore gives a canonical map from the Chow
graph closure to that absolute projective closure.

This map is proper, has dense image, and restricts to the identity
identification of the common dense open.  The remaining monomorphism in
Chow's lemma is equivalently the monomorphism of this proper birational
map.
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

/-- The relative product of the original scheme with the projective
closure of the rational-map image. -/
abbrev targetRelativeScheme : Scheme.{u} :=
  pullback f D.targetClosureToSpec

/-- The original graph with its projective component factored through
the target closure. -/
def graphToTargetRelative :
    D.domain ⟶ D.targetRelativeScheme :=
  pullback.lift D.toOriginalOpen D.toTargetClosure
    D.toTargetClosure_targetClosureToSpec.symm

/-- The closed embedding of the smaller relative product into the
relative standard projective space. -/
def targetRelativeToRelativeProjective :
    D.targetRelativeScheme ⟶
      relativeScheme f D.dimension :=
  pullback.map
    f D.targetClosureToSpec
    f (toSpec k D.dimension)
    (𝟙 X) D.targetClosureEmbedding
    (𝟙 (Spec (CommRingCat.of k)))
    (by simp)
    (by simp [targetClosureToSpec])

/-- The smaller relative product is closed in relative projective
space. -/
theorem isClosedImmersion_targetRelativeToRelativeProjective :
    IsClosedImmersion
      D.targetRelativeToRelativeProjective := by
  letI : MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg => by
      letI : IsClosedImmersion f := hf
      letI : IsClosedImmersion g := hg
      exact inferInstance⟩
  exact
    MorphismProperty.pullbackMap
      (P := @IsClosedImmersion)
      (by infer_instance)
      (by
        exact
          D.isClosedImmersion_targetClosureEmbedding)
      (by simp)
      (by simp [targetClosureToSpec])

/-- The closed relative-product embedding preserves the original-scheme
projection. -/
@[reassoc]
theorem targetRelativeToRelativeProjective_toOriginal :
    D.targetRelativeToRelativeProjective ≫
        relativeToBase f D.dimension =
      pullback.fst f D.targetClosureToSpec := by
  change
    pullback.lift
          (pullback.fst f D.targetClosureToSpec ≫ 𝟙 X)
          (pullback.snd f D.targetClosureToSpec ≫
            D.targetClosureEmbedding) _ ≫
        pullback.fst f (toSpec k D.dimension) =
      pullback.fst f D.targetClosureToSpec
  rw [pullback.lift_fst]
  simp

/-- On projective components, the closed relative-product embedding is
the target-closure embedding. -/
@[reassoc]
theorem targetRelativeToRelativeProjective_toProjective :
    D.targetRelativeToRelativeProjective ≫
        relativeToProjective f D.dimension =
      pullback.snd f D.targetClosureToSpec ≫
        D.targetClosureEmbedding := by
  change
    pullback.lift
          (pullback.fst f D.targetClosureToSpec ≫ 𝟙 X)
          (pullback.snd f D.targetClosureToSpec ≫
            D.targetClosureEmbedding) _ ≫
        pullback.snd f (toSpec k D.dimension) =
      pullback.snd f D.targetClosureToSpec ≫
        D.targetClosureEmbedding
  rw [pullback.lift_snd]

/-- The factored graph recovers the original relative projective
graph. -/
@[reassoc]
theorem graphToTargetRelative_targetRelativeToRelativeProjective :
    D.graphToTargetRelative ≫
        D.targetRelativeToRelativeProjective =
      relativeProjectiveGraph
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase := by
  apply pullback.hom_ext
  · rw [Category.assoc,
      D.targetRelativeToRelativeProjective_toOriginal]
    dsimp only [graphToTargetRelative,
      relativeProjectiveGraph]
    rw [pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc,
      D.targetRelativeToRelativeProjective_toProjective]
    dsimp only [graphToTargetRelative,
      relativeProjectiveGraph]
    rw [← Category.assoc,
      pullback.lift_snd,
      D.toTargetClosure_targetClosureEmbedding,
      pullback.lift_snd]

/-- The graph closure maps canonically to the closed relative product
with the target closure. -/
def graphClosureToTargetRelative :
    projectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase ⟶
      D.targetRelativeScheme :=
  by
    letI :
        IsClosedImmersion
          D.targetRelativeToRelativeProjective :=
      D.isClosedImmersion_targetRelativeToRelativeProjective
    exact
      SchemeTheoreticImage.toClosedFactor
        (relativeProjectiveGraph
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase)
        D.graphToTargetRelative
        D.targetRelativeToRelativeProjective
        D.graphToTargetRelative_targetRelativeToRelativeProjective.symm

/-- The graph closure remains closed inside the smaller relative
product. -/
theorem isClosedImmersion_graphClosureToTargetRelative :
    IsClosedImmersion D.graphClosureToTargetRelative := by
  letI :
      IsClosedImmersion
        D.targetRelativeToRelativeProjective :=
    D.isClosedImmersion_targetRelativeToRelativeProjective
  change
    IsClosedImmersion
      (SchemeTheoreticImage.toClosedFactor
        (relativeProjectiveGraph
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase)
        D.graphToTargetRelative
        D.targetRelativeToRelativeProjective
        D.graphToTargetRelative_targetRelativeToRelativeProjective.symm)
  infer_instance

/-- The canonical proper map from the Chow graph closure to the
absolute projective closure of the rational-map image. -/
def graphClosureToTargetClosure :
    projectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase ⟶
      D.targetClosure :=
  D.graphClosureToTargetRelative ≫
    pullback.snd f D.targetClosureToSpec

/-- Composing with the target-closure embedding recovers the usual
second projection of the projective graph closure. -/
@[reassoc]
theorem graphClosureToTargetClosure_targetClosureEmbedding :
    D.graphClosureToTargetClosure ≫
        D.targetClosureEmbedding =
      projectiveGraphClosureToProjective
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase := by
  letI :
      IsClosedImmersion
        D.targetRelativeToRelativeProjective :=
    D.isClosedImmersion_targetRelativeToRelativeProjective
  calc
    D.graphClosureToTargetClosure ≫
          D.targetClosureEmbedding =
        D.graphClosureToTargetRelative ≫
          (pullback.snd f D.targetClosureToSpec ≫
            D.targetClosureEmbedding) := by
      simp [graphClosureToTargetClosure, Category.assoc]
    _ =
        D.graphClosureToTargetRelative ≫
          D.targetRelativeToRelativeProjective ≫
            relativeToProjective f D.dimension := by
      rw [D.targetRelativeToRelativeProjective_toProjective]
    _ =
        projectiveGraphClosureι
            f D.dimension D.toOriginalOpen
              D.toProjective D.overBase ≫
          relativeToProjective f D.dimension := by
      rw [← Category.assoc]
      exact congrArg
        (fun g => g ≫ relativeToProjective f D.dimension)
        (SchemeTheoreticImage.toClosedFactor_comp
          (relativeProjectiveGraph
            f D.dimension D.toOriginalOpen
              D.toProjective D.overBase)
          D.graphToTargetRelative
          D.targetRelativeToRelativeProjective
          D.graphToTargetRelative_targetRelativeToRelativeProjective.symm)
    _ = _ := rfl

/-- On the common dense open, the graph-to-closure map is the original
dense-open map into the target closure. -/
@[reassoc]
theorem toProjectiveGraphClosure_graphClosureToTargetClosure :
    toProjectiveGraphClosure
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase ≫
        D.graphClosureToTargetClosure =
      D.toTargetClosure := by
  apply (cancel_mono D.targetClosureEmbedding).mp
  rw [Category.assoc,
    D.graphClosureToTargetClosure_targetClosureEmbedding,
    toProjectiveGraphClosure_toProjective,
    D.toTargetClosure_targetClosureEmbedding]

/-- If the original scheme is proper, the graph-to-target-closure map
is proper. -/
theorem isProper_graphClosureToTargetClosure
    [IsProper f] :
    IsProper D.graphClosureToTargetClosure := by
  letI :
      IsClosedImmersion D.targetClosureEmbedding :=
    D.isClosedImmersion_targetClosureEmbedding
  letI :
      IsProper
        (D.graphClosureToTargetClosure ≫
          D.targetClosureEmbedding) := by
    rw [D.graphClosureToTargetClosure_targetClosureEmbedding]
    infer_instance
  exact
    IsProper.of_comp
      D.graphClosureToTargetClosure
      D.targetClosureEmbedding

/-- The graph-to-target-closure map has dense image. -/
theorem dense_graphClosureToTargetClosure :
    Dense
      (Set.range
        D.graphClosureToTargetClosure.base) := by
  apply D.dense_toTargetClosure.mono
  rintro z ⟨x, rfl⟩
  refine
    ⟨(toProjectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase).base x, ?_⟩
  have hbase :=
    congrArg
      (fun g => g.base)
      D.toProjectiveGraphClosure_graphClosureToTargetClosure
  exact
    congrArg (fun g => g x) hbase

/-- The graph closure and the absolute target closure share the common
dense open. -/
theorem graphClosureTargetBirational :
    IsBirational
      D.targetClosure
      (projectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase) := by
  letI : IsImmersion D.toProjective :=
    D.isImmersion_toProjective
  letI : QuasiCompact D.toProjective :=
    D.quasiCompact_toProjective
  letI : IsOpenImmersion D.toOriginalOpen :=
    D.isOpenImmersion_toOriginalOpen
  letI : QuasiCompact D.toOriginalOpen :=
    D.quasiCompact_toOriginalOpen
  letI : IsImmersion D.toOriginalOpen :=
    inferInstance
  letI : IsOpenImmersion D.toTargetClosure :=
    D.isOpenImmersion_toTargetClosure
  letI :
      IsOpenImmersion
        (toProjectiveGraphClosure
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) :=
    isOpenImmersion_toProjectiveGraphClosure
      f D.dimension D.toOriginalOpen
        D.toProjective D.overBase
  exact
    ⟨D.domain, D.toTargetClosure,
      toProjectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase,
      inferInstance, inferInstance,
      D.dense_toTargetClosure,
      denseRange_toProjectiveGraphClosure
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase⟩

/-- The remaining graph-projection monomorphism is equivalently the
monomorphism of the proper birational map to the projective target
closure. -/
theorem mono_graphClosureToProjective_iff_targetClosure
    [IsProper f] :
    Mono
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) ↔
      Mono D.graphClosureToTargetClosure := by
  constructor
  · intro h
    letI :
        Mono
          (D.graphClosureToTargetClosure ≫
            D.targetClosureEmbedding) := by
      rw [D.graphClosureToTargetClosure_targetClosureEmbedding]
      exact h
    exact
      mono_of_mono
        D.graphClosureToTargetClosure
        D.targetClosureEmbedding
  · intro h
    letI : Mono D.graphClosureToTargetClosure := h
    letI :
        IsClosedImmersion D.targetClosureEmbedding :=
      D.isClosedImmersion_targetClosureEmbedding
    letI : Mono D.targetClosureEmbedding :=
      inferInstance
    rw [← D.graphClosureToTargetClosure_targetClosureEmbedding]
    infer_instance

end ChowRationalProjectiveMapData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
