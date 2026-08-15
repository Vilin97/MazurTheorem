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

/-- The affine base written in the global-section coordinates used by the
standard-smooth chart API. -/
noncomputable def coordinateBase (K : Type u) [Field K] : Scheme.{u} :=
  Spec (.of Γ(Spec (.of K), ⊤))

/-- The global-section presentation of the ground field has the expected
affine spectrum. -/
noncomputable def coordinateBaseIso (K : Type u) [Field K] :
    coordinateBase K ≅ Spec (.of K) :=
  Scheme.Spec.mapIso (Scheme.ΓSpecIso (.of K)).symm.op

instance coordinateBase_nonempty (K : Type u) [Field K] :
    Nonempty (coordinateBase K) := by
  let y : Spec (.of K) := Classical.choice inferInstance
  exact ⟨(coordinateBaseIso K).inv y⟩

instance coordinateBase_subsingleton (K : Type u) [Field K] :
    Subsingleton (coordinateBase K) := by
  constructor
  intro x y
  let e := coordinateBaseIso K
  calc
    x = e.inv (e.hom x) := by
      have h := congrArg (fun q : coordinateBase K ⟶ coordinateBase K ↦ q x)
        e.hom_inv_id
      exact h.symm
    _ = e.inv (e.hom y) := congrArg e.inv (Subsingleton.elim _ _)
    _ = y := by
      have h := congrArg (fun q : coordinateBase K ⟶ coordinateBase K ↦ q y)
        e.hom_inv_id
      exact h

/-- The affine coordinate line as a scheme over the global-section copy of
the ground field. -/
noncomputable def coordinateLine (K : Type u) [Field K] :
    Over (coordinateBase K) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : Γ(Spec (.of K), ⊤) →+* coordinateRing K)))

/-- The ground-ring map on an affine curve chart induced by the structure
morphism. -/
noncomputable def restrictionBaseRingHom
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) (V : X.affineOpens) :
    Γ(Spec (.of K), ⊤) →+* Γ(X, (V : X.Opens)) :=
  (f.appLE ⊤ (V : X.Opens) (by simp)).hom

/-- An affine neighborhood of a curve point equipped with an étale
one-dimensional coordinate. -/
structure PointChart (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) (x : X) where
  V : X.affineOpens
  mem : x ∈ (V : X.Opens)
  coordinate : coordinateRing K →+* Γ(X, (V : X.Opens))
  coordinate_etale : coordinate.Etale
  coordinate_comp :
    coordinate.comp (MvPolynomial.C :
      Γ(Spec (.of K), ⊤) →+* coordinateRing K) =
        restrictionBaseRingHom K X f V

namespace PointChart

/-- The scheme morphism represented by the étale coordinate ring map. -/
noncomputable def schemeMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) :
    (c.V : X.Opens).toScheme ⟶ Spec (.of (coordinateRing K)) :=
  c.V.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom c.coordinate)

/-- The source affine curve chart, regarded over the same affine base as its
coordinate line. -/
noncomputable def sourceOver
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) : Over (coordinateBase K) :=
  Over.mk (c.schemeMap ≫ (coordinateLine K).hom)

/-- The étale coordinate morphism as an arrow over the affine ground-field
copy. -/
noncomputable def schemeMapOver
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) : c.sourceOver ⟶ coordinateLine K :=
  Over.homMk c.schemeMap rfl

instance schemeMap_etale
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) : Etale c.schemeMap := by
  haveI : Etale (Spec.map (CommRingCat.ofHom c.coordinate)) :=
    HasRingHomProperty.Spec_iff.mpr c.coordinate_etale
  dsimp only [schemeMap]
  infer_instance

instance schemeMap_isSeparated
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) : IsSeparated c.schemeMap := by
  dsimp only [schemeMap]
  infer_instance

/-- Zariski's main theorem isolates the selected curve point in a finite
étale open-and-closed component after an étale base change of its affine-
line coordinate. -/
theorem exists_isCompl_finiteEtale
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Spec (.of (coordinateRing K))),
      Etale g ∧ c.schemeMap (⟨x, c.mem⟩ : (c.V : X.Opens).toScheme) ∈
        Set.range g ∧
      ∃ (V W : (pullback c.schemeMap g).Opens) (v : V),
        IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd c.schemeMap g) ∧
          Etale (V.ι ≫ pullback.snd c.schemeMap g) ∧
            pullback.fst c.schemeMap g v.1 = ⟨x, c.mem⟩ := by
  exact EtaleFiniteNeighborhood.exists_isCompl_finiteEtale
    c.schemeMap (⟨x, c.mem⟩ : (c.V : X.Opens).toScheme)

/-- The finite étale point component supplied by Zariski's main theorem,
packaged for subsequent finite-family assembly. -/
structure FiniteNeighborhood
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) where
  base : Scheme.{u}
  baseMap : base ⟶ (coordinateLine K).left
  baseMap_etale : Etale baseMap
  point_mem_range : c.schemeMap (⟨x, c.mem⟩ : (c.V : X.Opens).toScheme) ∈
    Set.range baseMap
  selectedOpen : (pullback c.schemeMap baseMap).Opens
  otherOpen : (pullback c.schemeMap baseMap).Opens
  selectedPoint : ↥selectedOpen
  isCompl : IsCompl selectedOpen otherOpen
  selected_isFinite :
    IsFinite (selectedOpen.ι ≫ pullback.snd c.schemeMap baseMap)
  selected_etale :
    Etale (selectedOpen.ι ≫ pullback.snd c.schemeMap baseMap)
  selectedPoint_fst :
    pullback.fst c.schemeMap baseMap selectedPoint.1 = ⟨x, c.mem⟩

/-- A finite neighborhood exists for every chosen curve coordinate chart. -/
theorem nonempty_finiteNeighborhood
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) : Nonempty (FiniteNeighborhood c) := by
  obtain ⟨U, g, hg, hrange, V, W, v, hcompl, hfinite, hetale, hfst⟩ :=
    c.exists_isCompl_finiteEtale
  exact ⟨⟨U, g, hg, hrange, V, W, v, hcompl, hfinite, hetale, hfst⟩⟩

/-- A chosen finite étale component around the selected curve point. -/
noncomputable def finiteNeighborhood
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X}
    (c : PointChart K X f x) : FiniteNeighborhood c :=
  Classical.choice (nonempty_finiteNeighborhood c)

namespace FiniteNeighborhood

/-- A chosen point of the étale coordinate base lying below the selected
component point. -/
noncomputable def basePoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : n.base :=
  Classical.choose n.point_mem_range

@[simp]
theorem baseMap_basePoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) :
    n.baseMap n.basePoint = c.schemeMap (⟨x, c.mem⟩ :
      (c.V : X.Opens).toScheme) :=
  Classical.choose_spec n.point_mem_range

/-- The étale base change, regarded over the affine ground-field copy. -/
noncomputable def baseOver
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : Over (coordinateBase K) :=
  Over.mk (n.baseMap ≫ (coordinateLine K).hom)

/-- The selected finite étale component over the same affine base. -/
noncomputable def componentOver
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : Over (coordinateBase K) :=
  Over.mk (n.selectedOpen.ι ≫ pullback.snd c.schemeMap n.baseMap ≫
    n.baseMap ≫ (coordinateLine K).hom)

/-- The selected component as a morphism over the affine ground-field copy. -/
noncomputable def componentToBase
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : n.componentOver ⟶ n.baseOver :=
  Over.homMk (n.selectedOpen.ι ≫ pullback.snd c.schemeMap n.baseMap) rfl

/-- The selected component maps back to the affine curve chart through the
first pullback projection. -/
noncomputable def componentToChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) :
    n.selectedOpen.toScheme ⟶ (c.V : X.Opens).toScheme :=
  n.selectedOpen.ι ≫ pullback.fst c.schemeMap n.baseMap

/-- The selected finite étale component mapped to the original curve. -/
noncomputable def componentToCurve
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : n.selectedOpen.toScheme ⟶ X :=
  n.componentToChart ≫ c.V.1.ι

@[simp]
theorem componentToCurve_selectedPoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : n.componentToCurve n.selectedPoint = x := by
  change c.V.1.ι (pullback.fst c.schemeMap n.baseMap n.selectedPoint.1) = x
  rw [n.selectedPoint_fst]
  rfl

instance componentToBase_isFinite
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : IsFinite n.componentToBase.left :=
  n.selected_isFinite

instance componentToBase_etale
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} {c : PointChart K X f x}
    (n : FiniteNeighborhood c) : Etale n.componentToBase.left :=
  n.selected_etale

end FiniteNeighborhood

end PointChart

/-- Every point of a smooth relative curve has an affine étale
one-dimensional coordinate chart. -/
theorem exists_pointChart
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] (x : X) :
    Nonempty (PointChart K X f x) := by
  obtain ⟨V, hx, g, hg⟩ :=
    SmoothCurveReduced.exists_affineOpen_etaleCoordinate K X f x
  let e : (V : X.Opens) ≤ f ⁻¹ᵁ (⊤ : (Spec (.of K)).Opens) := by simp
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, (V : X.Opens)) :=
    (f.appLE ⊤ (V : X.Opens) e).hom.toAlgebra
  refine ⟨⟨V, hx, g.toRingHom, hg, ?_⟩⟩
  apply RingHom.ext fun r ↦ ?_
  exact g.commutes r

end MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveEtaleCoordinate
