/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteProjectiveProducts
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveClosure
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeAffineCoverData

/-!
# Projective completions of every chart in a finite affine cover

Each chart of `RelativeAffineCoverData` is a finite-type affine scheme
over the fixed coefficient ring.  Its scheme-theoretic projective closure
therefore gives an actual projective model containing that chart as a
dense open.  Assuming only the isolated Segre interface, the finitely many
models have a chosen projective iterated fiber product.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- A projective completion, over the fixed coefficient ring, of one
chart in a relative affine cover. -/
structure ChartProjectiveCompletion
    (k : Type u) [CommRing k]
    {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (c : RelativeAffineCoverData k f)
    (i : c.toAffineCoverData.ι) where
  model : StandardProjectiveModel k
  openMap :
    Spec (c.toAffineCoverData.R i) ⟶ model.carrier
  isOpenImmersion_openMap :
    IsOpenImmersion openMap
  dense_openMap :
    Dense (Set.range openMap.base)
  openMap_toSpec :
    openMap ≫ model.toSpec =
      Spec.map (c.baseMap i)

/-- Every chart in relative affine cover data has a projective completion
over the same coefficient ring. -/
theorem exists_chartProjectiveCompletion
    (k : Type u) [CommRing k]
    {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (c : RelativeAffineCoverData k f)
    (i : c.toAffineCoverData.ι) :
    Nonempty (ChartProjectiveCompletion k c i) := by
  letI : Algebra k (c.toAffineCoverData.R i) :=
    (c.baseMap i).hom.toAlgebra
  letI : Algebra.FiniteType k (c.toAffineCoverData.R i) :=
    RingHom.finiteType_algebraMap.mp (by
      simpa [RingHom.algebraMap_toAlgebra] using
        c.finiteType_baseMap i)
  obtain
      ⟨d, φ, hφ, hopen, hdense, -, hprojective, -, hbase⟩ :=
    exists_projectiveClosure_of_finiteType
      k (c.toAffineCoverData.R i)
  let model : StandardProjectiveModel k :=
    { carrier := projectiveClosure φ
      toSpec := projectiveClosureToSpec φ
      projective := hprojective }
  refine
    ⟨{
      model := model
      openMap := toProjectiveClosure φ
      isOpenImmersion_openMap := hopen
      dense_openMap := hdense
      openMap_toSpec := ?_ }⟩
  simpa [model, RingHom.algebraMap_toAlgebra] using hbase

/-- A chosen projective completion of one chart. -/
def chartProjectiveCompletion
    (k : Type u) [CommRing k]
    {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (c : RelativeAffineCoverData k f)
    (i : c.toAffineCoverData.ι) :
    ChartProjectiveCompletion k c i :=
  Classical.choice (exists_chartProjectiveCompletion k c i)

/-- Assuming scheme-level Segre embeddings, the projective completions of
all charts in a nonempty finite affine cover have a chosen projective
iterated fiber product. -/
def finiteChartProjectiveAmbient
    (k : Type u) [CommRing k]
    (hsegre : StandardSegreEmbeddings k)
    {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (c : RelativeAffineCoverData k f)
    [Nonempty c.toAffineCoverData.ι] :
    StandardProjectiveModel k :=
  StandardProjectiveModel.finiteFiberProduct hsegre
    (fun i => (chartProjectiveCompletion k c i).model)

/-- The chosen finite chart ambient is projective over the fixed
coefficient ring. -/
theorem finiteChartProjectiveAmbient_projective
    (k : Type u) [CommRing k]
    (hsegre : StandardSegreEmbeddings k)
    {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (c : RelativeAffineCoverData k f)
    [Nonempty c.toAffineCoverData.ι] :
    IsProjectiveFactorization
      (finiteChartProjectiveAmbient
        k hsegre c).toSpec :=
  (finiteChartProjectiveAmbient k hsegre c).projective

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
