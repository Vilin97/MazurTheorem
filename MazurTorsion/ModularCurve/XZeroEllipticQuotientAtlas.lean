/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveCubic
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Stable affine charts for finite actions on a Weierstrass cubic

This file supplies the geometric input needed to form the quotient of the
concrete projective Weierstrass cubic over `ℚ` by a finite abstract group.
It does not assume a stable affine atlas.

For a point `x` of the cubic, the orbit of `x` gives finitely many points of
the ambient projective plane.  At each of these points, the degree-one forms
belonging to the corresponding homogeneous prime form a proper subspace.  As
`ℚ` is infinite, finitely many proper subspaces do not cover the degree-one
piece.  A linear form outside their union defines one projective basic open
containing the whole orbit.  Pulling this open back along the cubic's closed
immersion gives an affine open of the cubic, and
`SchemeAction.exists_isStableOpen_isAffineOpen` refines it to a stable affine
neighbourhood.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

/-- The degree-one homogeneous forms vanishing at a point of projective two-space. -/
def degreeOneVanishingSubmodule (p : projectivePlane ℚ) :
    Submodule ℚ (homogeneousPieces ℚ 1) :=
  Submodule.comap (homogeneousPieces ℚ 1).subtype
    (p.asHomogeneousIdeal.toIdeal.restrictScalars ℚ)

@[simp]
theorem mem_degreeOneVanishingSubmodule_iff (p : projectivePlane ℚ)
    (q : homogeneousPieces ℚ 1) :
    q ∈ degreeOneVanishingSubmodule p ↔
      (q : MvPolynomial (Fin 3) ℚ) ∈ p.asHomogeneousIdeal :=
  Iff.rfl

/-- Relevance of a projective prime says that its degree-one vanishing subspace is proper. -/
theorem degreeOneVanishingSubmodule_ne_top (p : projectivePlane ℚ) :
    degreeOneVanishingSubmodule p ≠ ⊤ := by
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem p
  intro hp
  have hXi :
      (⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℚ i⟩ : homogeneousPieces ℚ 1) ∈
        degreeOneVanishingSubmodule p := by
    rw [hp]
    trivial
  exact hi ((mem_degreeOneVanishingSubmodule_iff p _).mp hXi)

/-- A single degree-one form avoids every point in a finite orbit in the ambient projective
plane.  This is the only place where infinitude of the ground field is used. -/
theorem exists_degreeOne_not_mem_ambient_orbit
    {G : Type*} [Group G] [Finite G]
    (W : WeierstrassCurve ℚ) (sigma : SchemeAction G (scheme W)) (x : scheme W) :
    ∃ q : homogeneousPieces ℚ 1, ∀ g : G,
      (q : MvPolynomial (Fin 3) ℚ) ∉
        (inclusion W (sigma.hom g x)).asHomogeneousIdeal := by
  obtain ⟨q, hq⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun g : G ↦ degreeOneVanishingSubmodule (inclusion W (sigma.hom g x)))
    (fun g ↦ degreeOneVanishingSubmodule_ne_top (inclusion W (sigma.hom g x)))
  exact ⟨q, fun g ↦ by
    simpa only [mem_degreeOneVanishingSubmodule_iff] using hq g⟩

/-- Every finite orbit on the concrete projective Weierstrass cubic over `ℚ` lies in one
affine open.  The open is the pullback of an ambient projective basic open cut out by an
orbit-avoiding linear form. -/
theorem exists_affineOpen_containing_orbit
    {G : Type*} [Group G] [Finite G]
    (W : WeierstrassCurve ℚ) (sigma : SchemeAction G (scheme W)) (x : scheme W) :
    ∃ U : (scheme W).Opens, IsAffineOpen U ∧ ∀ g : G, sigma.hom g x ∈ U := by
  obtain ⟨q, hq⟩ := exists_degreeOne_not_mem_ambient_orbit W sigma x
  let Uamb : (projectivePlane ℚ).Opens :=
    Proj.basicOpen (homogeneousPieces ℚ) (q : MvPolynomial (Fin 3) ℚ)
  let U : (scheme W).Opens := inclusion W ⁻¹ᵁ Uamb
  refine ⟨U, ?_, ?_⟩
  · exact (Proj.isAffineOpen_basicOpen (homogeneousPieces ℚ)
      (q : MvPolynomial (Fin 3) ℚ) q.property (by omega)).preimage (inclusion W)
  · intro g
    change inclusion W (sigma.hom g x) ∈ Uamb
    exact (ProjectiveSpectrum.mem_basicOpen
      (homogeneousPieces ℚ) (q : MvPolynomial (Fin 3) ℚ) _).2 (hq g)

/-- The concrete projective cubic is separated as an absolute scheme. -/
instance scheme_isSeparated (W : WeierstrassCurve ℚ) : (scheme W).IsSeparated where
  isSeparated_terminal_from := by
    rw [← terminal.comp_from (structureMap W)]
    infer_instance

/-- Every point of the cubic has a stable affine neighbourhood for a finite group action. -/
theorem exists_stableAffineOpen
    {G : Type*} [Group G] [Finite G]
    (W : WeierstrassCurve ℚ) (sigma : SchemeAction G (scheme W)) (x : scheme W) :
    ∃ V : (scheme W).Opens,
      sigma.IsStableOpen V ∧ IsAffineOpen V ∧ x ∈ V := by
  obtain ⟨U, hUa, horbit⟩ := exists_affineOpen_containing_orbit W sigma x
  exact sigma.exists_isStableOpen_isAffineOpen hUa x horbit

/-- A point-indexed stable affine atlas, chosen from the explicit orbit construction above. -/
def stableAffineAtlas
    {G : Type*} [Group G] [Finite G]
    (W : WeierstrassCurve ℚ) (sigma : SchemeAction G (scheme W)) :
    scheme W → (scheme W).Opens :=
  fun x ↦ (exists_stableAffineOpen W sigma x).choose

theorem stableAffineAtlas_isStable
    {G : Type*} [Group G] [Finite G]
    (W : WeierstrassCurve ℚ) (sigma : SchemeAction G (scheme W)) (x : scheme W) :
    sigma.IsStableOpen (stableAffineAtlas W sigma x) :=
  (exists_stableAffineOpen W sigma x).choose_spec.1

theorem stableAffineAtlas_isAffine
    {G : Type*} [Group G] [Finite G]
    (W : WeierstrassCurve ℚ) (sigma : SchemeAction G (scheme W)) (x : scheme W) :
    IsAffineOpen (stableAffineAtlas W sigma x) :=
  (exists_stableAffineOpen W sigma x).choose_spec.2.1

theorem mem_stableAffineAtlas
    {G : Type*} [Group G] [Finite G]
    (W : WeierstrassCurve ℚ) (sigma : SchemeAction G (scheme W)) (x : scheme W) :
    x ∈ stableAffineAtlas W sigma x :=
  (exists_stableAffineOpen W sigma x).choose_spec.2.2

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
