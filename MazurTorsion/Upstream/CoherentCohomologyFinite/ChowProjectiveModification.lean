/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowCanonicalGraphReduction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowTargetCompletionCoverage

/-!
# Chow's projective modification over a field

For a proper scheme over a field, choose a finite affine cover and a
common dense affine open.  Map that common open to the finite product
of the projective completions of all cover charts, and use the explicit
Segre embeddings to place the product in one standard projective
space.

The completion-interior argument proves that the second projection of
the graph closure is a monomorphism.  Since that projection is proper,
it is a closed immersion.  The graph closure is therefore projective
over the field and gives the desired projective modification.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- The chosen canonical Chow graph projection is a monomorphism for
every proper scheme over a field. -/
theorem canonicalChowGraphProjectionMonomorphisms
    (k : Type u) [Field k] :
    CanonicalChowGraphProjectionMonomorphisms k := by
  intro X f _
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  let c :=
    Chow.properCommonDenseRelativeAffineCoverData k f
  unfold properChowGraphProjection
    properChowRationalProjectiveMapData
  exact c.mono_graphClosureToProjective

/-- The finite-chart graph-monomorphism assembly is unconditional over
a field. -/
theorem finiteChartGraphMonomorphismAssembly_field
    (k : Type u) [Field k] :
    FiniteChartGraphMonomorphismAssembly k :=
  finiteChartGraphMonomorphismAssembly_of_canonical
    k
    (canonicalChowGraphProjectionMonomorphisms k)

/-- The finite-affine-cover projective assembly is unconditional over
a field. -/
theorem finiteAffineCoverProjectiveAssembly_field
    (k : Type u) [Field k] :
    FiniteAffineCoverProjectiveAssembly k :=
  finiteAffineCoverProjectiveAssembly_of_canonicalChowGraphs
    k
    (canonicalChowGraphProjectionMonomorphisms k)

/-- A chosen projective modification of a proper scheme over a field,
obtained from the canonical finite-chart Chow graph. -/
def projectiveModificationOfProperToField
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    ProjectiveModification f := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  let c :=
    Chow.properCommonDenseRelativeAffineCoverData k f
  let D := c.toRationalProjectiveMapData
  have hmono :
      Mono
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) :=
    c.mono_graphClosureToProjective
  exact
    (D.toGraphMonomorphismData hmono).toProjectiveModification

/-- Every proper scheme over a field admits a projective modification. -/
theorem exists_projectiveModification_of_proper_to_field
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (ProjectiveModification f) :=
  ⟨projectiveModificationOfProperToField k f⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
