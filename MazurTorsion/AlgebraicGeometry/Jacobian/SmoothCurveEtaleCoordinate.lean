/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EtaleFiniteNeighborhood
import MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced

/-!
# Étale affine-line coordinates with finite point neighborhoods

The standard-smooth chart of a relative smooth curve gives an algebra map
from a one-variable polynomial ring.  This file turns that algebra map into
an actual étale morphism of affine schemes and immediately applies Zariski's
main theorem to isolate a chosen curve point in a finite étale open-and-
closed component after an étale base change.

The named downstream consumer is the finite-support local chart in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveEtaleCoordinate

/-- The one-variable polynomial coordinate ring used by a curve chart. -/
abbrev coordinateRing (K : Type u) [Field K] :=
  MvPolynomial (Fin 1) Γ(Spec (.of K), ⊤)

/-- An affine neighborhood of a curve point equipped with an étale
one-dimensional coordinate. -/
structure PointChart (K : Type u) [Field K] (X : Scheme.{u}) (x : X) where
  V : X.affineOpens
  mem : x ∈ (V : X.Opens)
  coordinate : coordinateRing K →+* Γ(X, (V : X.Opens))
  coordinate_etale : coordinate.Etale

namespace PointChart

/-- The scheme morphism represented by the étale coordinate ring map. -/
noncomputable def schemeMap
    {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (c : PointChart K X x) :
    (c.V : X.Opens).toScheme ⟶ Spec (.of (coordinateRing K)) :=
  c.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom c.coordinate)

instance schemeMap_etale
    {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (c : PointChart K X x) : Etale c.schemeMap := by
  haveI : Etale (Spec.map (CommRingCat.ofHom c.coordinate)) :=
    HasRingHomProperty.Spec_iff.mpr c.coordinate_etale
  dsimp only [schemeMap]
  infer_instance

instance schemeMap_isSeparated
    {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (c : PointChart K X x) : IsSeparated c.schemeMap := by
  dsimp only [schemeMap]
  infer_instance

/-- Zariski's main theorem isolates the selected curve point in a finite
étale open-and-closed component after an étale base change of its affine-
line coordinate. -/
theorem exists_isCompl_finiteEtale
    {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (c : PointChart K X x) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Spec (.of (coordinateRing K))),
      Etale g ∧ c.schemeMap (⟨x, c.mem⟩ : (c.V : X.Opens).toScheme) ∈
        Set.range g ∧
      ∃ (V W : (pullback c.schemeMap g).Opens) (v : V),
        IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd c.schemeMap g) ∧
          Etale (V.ι ≫ pullback.snd c.schemeMap g) ∧
            pullback.fst c.schemeMap g v.1 = ⟨x, c.mem⟩ := by
  exact EtaleFiniteNeighborhood.exists_isCompl_finiteEtale
    c.schemeMap (⟨x, c.mem⟩ : (c.V : X.Opens).toScheme)

end PointChart

/-- Every point of a smooth relative curve has an affine étale
one-dimensional coordinate chart. -/
theorem exists_pointChart
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] (x : X) :
    Nonempty (PointChart K X x) := by
  obtain ⟨V, hx, g, hg⟩ :=
    SmoothCurveReduced.exists_affineOpen_etaleCoordinate K X f x
  let e : (V : X.Opens) ≤ f ⁻¹ᵁ (⊤ : (Spec (.of K)).Opens) := by simp
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, (V : X.Opens)) :=
    (f.appLE ⊤ (V : X.Opens) e).hom.toAlgebra
  exact ⟨⟨V, hx, g.toRingHom, hg⟩⟩

end MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveEtaleCoordinate
