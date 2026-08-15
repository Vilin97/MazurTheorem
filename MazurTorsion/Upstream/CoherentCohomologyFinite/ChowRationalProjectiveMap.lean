/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowCommonDomainProjectiveMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowGraphMonomorphismAssembly
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteProjectiveProductMapImmersion
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveModification
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreProductChartTransitionGeometry

/-!
# A rational projective map for Chow's construction

The finite-product step in the usual proof of Chow's lemma is now
unconditional: the explicit Segre construction embeds every finite
product of the chosen chart completions in one standard projective
space.

This file packages the resulting rational map.  Its domain is a common
dense affine open in the original scheme, and the map is compatible
with the fixed affine base.  The package deliberately stops before the
last assertion in Chow's lemma, namely that the second projection of
the graph closure is a monomorphism.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- A dense open of a scheme together with a compatible map to one
standard projective space.  These are exactly the inputs needed to form
the projective graph closure in Chow's construction. -/
structure ChowRationalProjectiveMapData
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) where
  dimension : ℕ
  domain : Scheme.{u}
  toOriginalOpen : domain ⟶ X
  toProjective : domain ⟶ scheme k dimension
  overBase :
    toOriginalOpen ≫ f =
      toProjective ≫ toSpec k dimension
  isImmersion_toProjective :
    IsImmersion toProjective
  quasiCompact_toProjective :
    QuasiCompact toProjective
  isOpenImmersion_toOriginalOpen :
    IsOpenImmersion toOriginalOpen
  quasiCompact_toOriginalOpen :
    QuasiCompact toOriginalOpen
  dense_toOriginalOpen :
    Dense (Set.range toOriginalOpen.base)

namespace ChowRationalProjectiveMapData

/-- Closing the graph of the rational projective map gives a genuine
relative projective modification. -/
def toRelativeProjectiveModification
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (D : ChowRationalProjectiveMapData f) :
    RelativeProjectiveModification f := by
  letI : IsOpenImmersion D.toOriginalOpen :=
    D.isOpenImmersion_toOriginalOpen
  letI : QuasiCompact D.toOriginalOpen :=
    D.quasiCompact_toOriginalOpen
  exact
    relativeProjectiveModificationOfGraph
      f D.dimension D.toOriginalOpen D.toProjective
      D.overBase D.dense_toOriginalOpen

/-- Once the second projection of the graph closure is known to be a
monomorphism, rational projective-map data becomes the graph datum used
by the projective-modification assembly. -/
def toGraphMonomorphismData
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (D : ChowRationalProjectiveMapData f)
    (hmono :
      Mono
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase)) :
    ChowGraphMonomorphismData f :=
  {
    dimension := D.dimension
    domain := D.domain
    toOriginalOpen := D.toOriginalOpen
    toProjective := D.toProjective
    overBase := D.overBase
    isOpenImmersion_toOriginalOpen :=
      D.isOpenImmersion_toOriginalOpen
    quasiCompact_toOriginalOpen :=
      D.quasiCompact_toOriginalOpen
    dense_toOriginalOpen := D.dense_toOriginalOpen
    mono_graphClosureToProjective := hmono
  }

end ChowRationalProjectiveMapData

namespace Chow.CommonDenseRelativeAffineCoverData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}

/-- The common dense affine domain maps to one standard projective
space.  The finite product of chart completions is converted to a
single projective space by the explicit Segre embedding. -/
def toRationalProjectiveMapData
    [IsLocallyNoetherian X]
    (c : Chow.CommonDenseRelativeAffineCoverData k f) :
    ChowRationalProjectiveMapData f := by
  let A :=
    c.finiteProjectiveAmbientWithMap
      (standardSegreEmbeddings k)
  let d := A.1.projective.choose
  let i := A.1.projective.choose_spec.choose
  have hi :
      IsClosedImmersion i :=
    A.1.projective.choose_spec.choose_spec.1
  have hbase :
      i ≫ toSpec k d = A.1.toSpec :=
    A.1.projective.choose_spec.choose_spec.2
  have hcomponent :
      ∀ j,
        IsImmersion
          (c.projectiveCompletionMapFrom j).hom := by
    intro j
    letI :
        IsOpenImmersion
          (c.projectiveCompletion j).openMap :=
      (c.projectiveCompletion j).isOpenImmersion_openMap
    dsimp only [projectiveCompletionMapFrom,
      domainToProjectiveCompletion]
    infer_instance
  have hambient :
      IsImmersion A.2.hom := by
    exact
      StandardProjectiveModel.isImmersion_finiteFiberProductWithMap
        (standardSegreEmbeddings k)
        (fun j => (c.projectiveCompletion j).model)
        (fun j => c.projectiveCompletionMapFrom j)
        hcomponent
  letI : IsImmersion A.2.hom := hambient
  letI : IsClosedImmersion i := hi
  refine
    {
      dimension := d
      domain := c.domain
      toOriginalOpen := c.domainInclusion
      toProjective := A.2.hom ≫ i
      overBase := ?_
      isImmersion_toProjective := inferInstance
      quasiCompact_toProjective := inferInstance
      isOpenImmersion_toOriginalOpen := inferInstance
      quasiCompact_toOriginalOpen := inferInstance
      dense_toOriginalOpen := c.dense_range_domainInclusion
    }
  change
    c.domainToBase =
      (A.2.hom ≫ i) ≫ toSpec k d
  rw [Category.assoc, hbase, A.2.overBase]

end Chow.CommonDenseRelativeAffineCoverData

/-- Every proper scheme over a field has the dense rational projective
map used in the finite-chart proof of Chow's lemma. -/
theorem exists_chowRationalProjectiveMapData_of_proper
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (ChowRationalProjectiveMapData f) := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  obtain ⟨c⟩ :=
    Chow.exists_commonDenseRelativeAffineCoverData_of_proper
      k f
  exact ⟨c.toRationalProjectiveMapData⟩

/-- A chosen common-dense relative affine cover of a proper scheme over
a field.  Keeping this choice visible lets the later finite-chart
extension argument refer back to the individual chart completions. -/
def Chow.properCommonDenseRelativeAffineCoverData
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Chow.CommonDenseRelativeAffineCoverData k f :=
  Classical.choice
    (Chow.exists_commonDenseRelativeAffineCoverData_of_proper
      k f)

/-- In particular, every proper scheme over a field has a birational
relative projective modification, without an integrality hypothesis. -/
theorem exists_relativeProjectiveModification_of_proper_to_field
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (RelativeProjectiveModification f) := by
  obtain ⟨D⟩ :=
    exists_chowRationalProjectiveMapData_of_proper k f
  exact ⟨D.toRelativeProjectiveModification⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
