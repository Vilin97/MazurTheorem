/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineChartProjectiveModification
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowAffineCoverData

/-!
# Finite affine covers over a fixed affine base

For a proper morphism to `Spec k`, every chart in a finite affine cover
inherits a finite-type `k`-algebra structure.  This file stores the
corresponding ring map and its exact compatibility with the structural
morphism; these are the local inputs to the graph-closure construction.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- Finite affine cover data equipped with its maps from a fixed
coefficient ring. -/
structure RelativeAffineCoverData
    (k : Type u) [CommRing k] {X : Scheme.{u}}
    (structureMap : X ⟶ Spec (CommRingCat.of k))
    extends AffineCoverData X where
  /-- The coefficient-ring map on each affine chart. -/
  baseMap : (i : toAffineCoverData.ι) →
    CommRingCat.of k ⟶ toAffineCoverData.R i
  /-- Every chart algebra is of finite type over the coefficient ring. -/
  finiteType_baseMap :
    ∀ i, (baseMap i).hom.FiniteType
  /-- The chart structural morphism is induced by `baseMap`. -/
  chart_toBase :
    ∀ i, toAffineCoverData.f i ≫ structureMap =
      Spec.map (baseMap i)

/-- A proper morphism to an affine base has a finite relative affine
cover whose chart algebras are of finite type. -/
theorem exists_relativeAffineCoverData
    (k : Type u) [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (RelativeAffineCoverData k f) := by
  obtain ⟨c⟩ := exists_affineCoverData_of_proper f
  refine ⟨{
    toAffineCoverData := c
    baseMap := fun i =>
      Spec.preimage (c.f i ≫ f)
    finiteType_baseMap := ?_
    chart_toBase := ?_ }⟩
  · intro i
    apply
      (HasRingHomProperty.Spec_iff
        (P := @LocallyOfFiniteType)).mp
    simpa using
      (inferInstance :
        LocallyOfFiniteType (c.f i ≫ f))
  · intro i
    exact (Spec.map_preimage (c.f i ≫ f)).symm

/-- The substantive local construction attached to a chart of a proper
finite relative affine cover. -/
theorem chart_has_projectiveModification
    (k : Type u) [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (c : RelativeAffineCoverData k f)
    (i : c.toAffineCoverData.ι) :
    letI : Algebra k (c.toAffineCoverData.R i) :=
      (c.baseMap i).hom.toAlgebra
    ∃ (d : ℕ)
      (φ :
        MvPolynomial (Fin d) k →ₐ[k]
          c.toAffineCoverData.R i)
      (hbase :
        c.toAffineCoverData.f i ≫ f =
          affineChartImmersion φ ≫ toSpec k d),
      Function.Surjective φ ∧
      IsOpenImmersion
        (toProjectiveGraphClosure
          f d (c.toAffineCoverData.f i)
            (affineChartImmersion φ) hbase) ∧
      Dense
        (Set.range
          (toProjectiveGraphClosure
            f d (c.toAffineCoverData.f i)
              (affineChartImmersion φ) hbase).base) ∧
      IsRelativeProjectiveFactorization f
        (projectiveGraphClosureToBase
          f d (c.toAffineCoverData.f i)
            (affineChartImmersion φ) hbase) := by
  letI : Algebra k (c.toAffineCoverData.R i) :=
    (c.baseMap i).hom.toAlgebra
  letI : Algebra.FiniteType k (c.toAffineCoverData.R i) :=
    RingHom.finiteType_algebraMap.mp (by
      simpa [RingHom.algebraMap_toAlgebra] using
        c.finiteType_baseMap i)
  letI : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated f
  have hchart :
      c.toAffineCoverData.f i ≫ f =
        Spec.map
          (CommRingCat.ofHom
            (algebraMap k (c.toAffineCoverData.R i))) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      c.chart_toBase i
  obtain
      ⟨d, φ, hbase, hφ, hopen, hdense, hrelative,
        -, -, -⟩ :=
    exists_projectiveModification_of_affineOpen
      k (c.toAffineCoverData.R i) X f
        (c.toAffineCoverData.f i) hchart
  exact
    ⟨d, φ, hbase, hφ, hopen, hdense, hrelative⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
