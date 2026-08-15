/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.Birational
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeAffineCoverData

/-!
# Birational relative projective modifications

For an integral proper scheme over an affine base, choose one affine chart.
It is dense, and the closure of its projective graph gives a birational
projective morphism back to the original scheme.

This is a genuine relative projective modification.  It is not yet the
stronger Chow output asserting that the model itself is projective over
the coefficient ring; that strengthening is exactly the finite-chart
assembly isolated in `ProjectiveModification`.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- A relatively projective morphism which is an isomorphism on a
specified common dense open. -/
structure RelativeProjectiveModification
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) where
  model : Scheme.{u}
  toOriginal : model ⟶ X
  relativeProjective :
    IsRelativeProjectiveFactorization f toOriginal
  commonOpen : Scheme.{u}
  toOriginalOpen : commonOpen ⟶ X
  toModelOpen : commonOpen ⟶ model
  isOpenImmersion_toOriginalOpen :
    IsOpenImmersion toOriginalOpen
  isOpenImmersion_toModelOpen :
    IsOpenImmersion toModelOpen
  dense_toOriginalOpen :
    Dense (Set.range toOriginalOpen.base)
  dense_toModelOpen :
    Dense (Set.range toModelOpen.base)
  toModelOpen_toOriginal :
    toModelOpen ≫ toOriginal = toOriginalOpen

namespace RelativeProjectiveModification

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}

/-- A relative projective modification is proper over the original
scheme. -/
theorem isProper_toOriginal
    (P : RelativeProjectiveModification f) :
    IsProper P.toOriginal :=
  P.relativeProjective.isProper

/-- If the original scheme is proper over the coefficient ring, so is
the model. -/
theorem isProper_toBase
    (P : RelativeProjectiveModification f) [IsProper f] :
    IsProper (P.toOriginal ≫ f) := by
  letI : IsProper P.toOriginal := P.isProper_toOriginal
  infer_instance

/-- A relative projective modification is birational to the original
scheme. -/
theorem isBirational
    (P : RelativeProjectiveModification f) :
    IsBirational X P.model :=
  ⟨P.commonOpen, P.toOriginalOpen, P.toModelOpen,
    P.isOpenImmersion_toOriginalOpen,
    P.isOpenImmersion_toModelOpen,
    P.dense_toOriginalOpen,
    P.dense_toModelOpen⟩

end RelativeProjectiveModification

/-- Closing a projective graph over a dense open produces a relative
projective modification. -/
def relativeProjectiveModificationOfGraph
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (d : ℕ)
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    (p : U ⟶ scheme k d)
    (hbase : u ≫ f = p ≫ toSpec k d)
    (hdense : Dense (Set.range u.base)) :
    RelativeProjectiveModification f where
  model :=
    projectiveGraphClosure f d u p hbase
  toOriginal :=
    projectiveGraphClosureToBase f d u p hbase
  relativeProjective :=
    isRelativeProjectiveFactorization_projectiveGraphClosureToBase
      f d u p hbase
  commonOpen := U
  toOriginalOpen := u
  toModelOpen :=
    toProjectiveGraphClosure f d u p hbase
  isOpenImmersion_toOriginalOpen := inferInstance
  isOpenImmersion_toModelOpen :=
    isOpenImmersion_toProjectiveGraphClosure
      f d u p hbase
  dense_toOriginalOpen := hdense
  dense_toModelOpen :=
    denseRange_toProjectiveGraphClosure
      f d u p hbase
  toModelOpen_toOriginal :=
    toProjectiveGraphClosure_toBase
      f d u p hbase

/-- Every integral scheme proper over an affine base has a birational
relative projective modification obtained by closing the graph of one
finite-type affine chart. -/
theorem exists_relativeProjectiveModification_of_proper
    (k : Type u) [CommRing k]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [IsIntegral X] :
    Nonempty (RelativeProjectiveModification f) := by
  obtain ⟨c⟩ :=
    Chow.exists_relativeAffineCoverData k f
  let x : X :=
    Classical.choice (inferInstance : Nonempty X)
  obtain ⟨i, hx⟩ :=
    c.toAffineCoverData.covers x
  have hdense :
      Dense
        (Set.range
          (c.toAffineCoverData.f i).base) :=
    (c.toAffineCoverData.f i).isOpenEmbedding.isOpen_range.dense
      ⟨x, hx⟩
  letI : Algebra k (c.toAffineCoverData.R i) :=
    (c.baseMap i).hom.toAlgebra
  obtain
      ⟨d, φ, hbase, -, -, -, -⟩ :=
    Chow.chart_has_projectiveModification k f c i
  haveI : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated f
  haveI : QuasiCompact (c.toAffineCoverData.f i) :=
    inferInstance
  exact
    ⟨relativeProjectiveModificationOfGraph
      f d (c.toAffineCoverData.f i)
      (affineChartImmersion φ) hbase hdense⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
