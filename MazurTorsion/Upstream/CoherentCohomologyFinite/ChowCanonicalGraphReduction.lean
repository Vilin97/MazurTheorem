/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowRationalProjectiveMap

/-!
# The canonical remaining graph condition in Chow's lemma

For a proper scheme over a field, `ChowRationalProjectiveMapData`
constructs the rational map to one standard projective space
unconditionally.  This file chooses that map and isolates the sole
remaining geometric assertion: the second projection of its graph
closure is a monomorphism.

The projection is already proper, so this assertion is equivalent to
being a closed immersion.  Once it is supplied, all existing Chow
assembly interfaces follow without any additional choices.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- A chosen dense rational projective map attached to a proper scheme
over a field. -/
def properChowRationalProjectiveMapData
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    ChowRationalProjectiveMapData f := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  exact
    (Chow.properCommonDenseRelativeAffineCoverData
      k f).toRationalProjectiveMapData

/-- The second projection of the graph closure of the chosen Chow
rational map. -/
def properChowGraphProjection
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    projectiveGraphClosure
        f (properChowRationalProjectiveMapData k f).dimension
        (properChowRationalProjectiveMapData k f).toOriginalOpen
        (properChowRationalProjectiveMapData k f).toProjective
        (properChowRationalProjectiveMapData k f).overBase ⟶
      scheme k
        (properChowRationalProjectiveMapData k f).dimension :=
  projectiveGraphClosureToProjective
    f (properChowRationalProjectiveMapData k f).dimension
    (properChowRationalProjectiveMapData k f).toOriginalOpen
    (properChowRationalProjectiveMapData k f).toProjective
    (properChowRationalProjectiveMapData k f).overBase

/-- The canonical graph projection is proper. -/
theorem isProper_properChowGraphProjection
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    IsProper (properChowGraphProjection k f) := by
  let D := properChowRationalProjectiveMapData k f
  letI : QuasiCompact D.toOriginalOpen :=
    D.quasiCompact_toOriginalOpen
  change
    IsProper
      (projectiveGraphClosureToProjective
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase)
  infer_instance

/-- For the chosen Chow graph, the remaining monomorphism condition is
equivalent to the closed-immersion conclusion needed for projectivity. -/
theorem isClosedImmersion_properChowGraphProjection_iff_mono
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    IsClosedImmersion (properChowGraphProjection k f) ↔
      Mono (properChowGraphProjection k f) := by
  let D := properChowRationalProjectiveMapData k f
  letI : QuasiCompact D.toOriginalOpen :=
    D.quasiCompact_toOriginalOpen
  exact
    isClosedImmersion_projectiveGraphClosureToProjective_iff_mono
      f D.dimension D.toOriginalOpen
        D.toProjective D.overBase

/-- The exact remaining statement for the canonical finite-chart Chow
construction. -/
def CanonicalChowGraphProjectionMonomorphisms
    (k : Type u) [Field k] : Prop :=
  ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f],
    Mono (properChowGraphProjection k f)

/-- Monomorphisms for the canonical graph projections imply the
finite-chart graph-monomorphism assembly. -/
theorem finiteChartGraphMonomorphismAssembly_of_canonical
    (k : Type u) [Field k]
    (hmono : CanonicalChowGraphProjectionMonomorphisms k) :
    FiniteChartGraphMonomorphismAssembly k := by
  intro X f _ _
  let D := properChowRationalProjectiveMapData k f
  have hD :
      Mono
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) := by
    exact hmono f
  exact ⟨D.toGraphMonomorphismData hD⟩

/-- Consequently, the canonical graph condition supplies the complete
finite-affine-cover projective assembly. -/
theorem finiteAffineCoverProjectiveAssembly_of_canonicalChowGraphs
    (k : Type u) [Field k]
    (hmono : CanonicalChowGraphProjectionMonomorphisms k) :
    FiniteAffineCoverProjectiveAssembly k :=
  finiteAffineCoverProjectiveAssembly_of_graphMonomorphism
    k
    (finiteChartGraphMonomorphismAssembly_of_canonical
      k hmono)

/-- Under the canonical graph condition, every proper scheme over the
field has a projective modification. -/
theorem exists_projectiveModification_of_canonicalChowGraphs
    (k : Type u) [Field k]
    (hmono : CanonicalChowGraphProjectionMonomorphisms k)
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (ProjectiveModification f) :=
  exists_projectiveModification_of_proper
    k
    (finiteAffineCoverProjectiveAssembly_of_canonicalChowGraphs
      k hmono)
    f

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
