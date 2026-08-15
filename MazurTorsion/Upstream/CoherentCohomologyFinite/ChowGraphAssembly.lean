/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowChartCompletions
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModification

/-!
# The residual graph-assembly statement in Chow's lemma

All graph-closure machinery is already formalized.  To obtain an
*absolute* projective model, it remains to assemble the finite chart maps
into one rational map to projective space for which the second projection
of the graph closure is a closed immersion.

`ChowGraphEmbeddingData` states exactly that residual datum.
`projectiveModificationOfChowGraph` proves that it implies the full
projective modification required by the cohomological dévissage.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- The precise graph datum which turns a dense open of `X` into an
absolute projective modification.  The decisive final field says that the
second projection of the scheme-theoretic graph closure is closed. -/
structure ChowGraphEmbeddingData
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) where
  dimension : ℕ
  domain : Scheme.{u}
  toOriginalOpen : domain ⟶ X
  toProjective : domain ⟶ scheme k dimension
  overBase :
    toOriginalOpen ≫ f =
      toProjective ≫ toSpec k dimension
  isOpenImmersion_toOriginalOpen :
    IsOpenImmersion toOriginalOpen
  quasiCompact_toOriginalOpen :
    QuasiCompact toOriginalOpen
  dense_toOriginalOpen :
    Dense (Set.range toOriginalOpen.base)
  isClosedImmersion_graphClosureToProjective :
    IsClosedImmersion
      (projectiveGraphClosureToProjective
        f dimension toOriginalOpen toProjective overBase)

/-- A graph datum with closed second projection produces the full
projective modification: relative projectivity comes from the first
projection, while absolute projectivity comes from the second. -/
def projectiveModificationOfChowGraph
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (D : ChowGraphEmbeddingData f) :
    ProjectiveModification f := by
  letI : IsOpenImmersion D.toOriginalOpen :=
    D.isOpenImmersion_toOriginalOpen
  letI : QuasiCompact D.toOriginalOpen :=
    D.quasiCompact_toOriginalOpen
  letI :
      IsClosedImmersion
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) :=
    D.isClosedImmersion_graphClosureToProjective
  exact
    {
      model :=
        projectiveGraphClosure
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
      toOriginal :=
        projectiveGraphClosureToBase
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
      relativeProjective :=
        isRelativeProjectiveFactorization_projectiveGraphClosureToBase
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
      projectiveOverBase :=
        ⟨D.dimension,
          projectiveGraphClosureToProjective
            f D.dimension D.toOriginalOpen
              D.toProjective D.overBase,
          inferInstance,
          (projectiveGraphClosure_projection_condition
            f D.dimension D.toOriginalOpen
              D.toProjective D.overBase).symm⟩
      commonOpen := D.domain
      toOriginalOpen := D.toOriginalOpen
      toModelOpen :=
        toProjectiveGraphClosure
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
      isOpenImmersion_toOriginalOpen := inferInstance
      isOpenImmersion_toModelOpen :=
        isOpenImmersion_toProjectiveGraphClosure
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
      dense_toOriginalOpen := D.dense_toOriginalOpen
      dense_toModelOpen :=
        denseRange_toProjectiveGraphClosure
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
      toModelOpen_toOriginal :=
        toProjectiveGraphClosure_toBase
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
    }

/-- The exact finite-chart gluing assertion left after the local
completions and product bookkeeping: the finite relative affine cover
must yield a rational projective map with closed graph projection. -/
def FiniteChartGraphEmbeddingAssembly
    (k : Type u) [CommRing k] : Prop :=
  ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f]
    (_ : Chow.RelativeAffineCoverData k f),
    Nonempty (ChowGraphEmbeddingData f)

/-- The residual graph-embedding assembly implies the projective
modification assembly used by the proper cohomology reduction. -/
theorem finiteAffineCoverProjectiveAssembly_of_graphEmbedding
    (k : Type u) [CommRing k]
    (hgraph : FiniteChartGraphEmbeddingAssembly k) :
    FiniteAffineCoverProjectiveAssembly k := by
  intro X f _ c
  obtain ⟨D⟩ := hgraph f c
  exact ⟨projectiveModificationOfChowGraph D⟩

/-- Consequently, the residual graph-embedding assembly alone gives a
projective modification of every proper scheme over the affine base. -/
theorem exists_projectiveModification_of_graphEmbeddingAssembly
    (k : Type u) [CommRing k]
    (hgraph : FiniteChartGraphEmbeddingAssembly k)
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (ProjectiveModification f) :=
  exists_projectiveModification_of_proper
    k
    (finiteAffineCoverProjectiveAssembly_of_graphEmbedding
      k hgraph)
    f

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
