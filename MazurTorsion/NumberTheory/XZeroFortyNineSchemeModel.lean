/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.XZeroFortyNineReduction
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePointComparison

/-!
# The represented rational `X_0(49)` target

The equation `y² = x(x² + 21x + 112)` used in the order-49 descent already
defines a reduced projective Weierstrass cubic scheme.  This module identifies
its scheme-valued rational points with the affine-coordinate point group and
lifts the checked two-point classification to actual morphisms from `Spec Q`.

There is a small distinction between arbitrary scheme morphisms and points in
the slice over `Spec Q`.  Every endomorphism of `Spec Q` is the identity, so an
arbitrary rational point has a canonical slice-category lift.  The existing
projective-cubic point comparison then proves bijectivity without postulating
a point-set equivalence.

This is only the represented target over `Q`.  It does not identify the cubic
with the rational fibre of a coarse `Gamma_0(49)` moduli space, construct a
modular classifying map, or prove noncuspidality of a classified family.  The
named downstream consumer is
`MazurTorsion.XZeroFortyNine.etaPointToScheme`, which maps the checked eta
chart into this scheme.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

namespace MazurTorsion.XZeroFortyNine.SchemeModel

/-- The reduced projective cubic underlying the explicit rational
`X_0(49)` model. -/
abbrev scheme : Scheme := WeierstrassProjectiveCubic.scheme curve

/-- Every scheme endomorphism of `Spec Q` is the identity. -/
theorem specRat_endomorphism_eq_id
    (f : Spec (.of ℚ) ⟶ Spec (.of ℚ)) : f = 𝟙 _ := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  apply Subsingleton.elim

universe u

@[simp]
private theorem affinePointOverMorphism_left
    {K : Type u} [Field K]
    (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    (affinePointOverMorphism W P).left = affinePointMorphism W P := by
  cases P <;> rfl

private theorem affinePointOverMorphism_bijective
    {K : Type u} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Bijective (affinePointOverMorphism W) := by
  constructor
  · intro P Q h
    apply affinePointMorphism_injective W
    have hleft := congrArg (fun f => f.left) h
    rw [affinePointOverMorphism_left, affinePointOverMorphism_left] at hleft
    simpa only [AffineCommGroupScheme.testObject,
      WeierstrassProjectiveCubic.toOver] using hleft
  · intro g
    obtain ⟨P, hP⟩ := projectivePointOverMorphism_surjective W g
    exact ⟨P.toAffineLift, hP⟩

/-- Regard an arbitrary morphism from `Spec Q` as a point over `Spec Q`.
The compatibility triangle is automatic because `Q` has no nontrivial ring
endomorphisms. -/
noncomputable def overPointOfMorphism (g : Spec (.of ℚ) ⟶ scheme) :
    AffineCommGroupScheme.testObject (R := ℚ) ℚ ⟶
      WeierstrassProjectiveCubic.toOver curve :=
  Over.homMk g (by
    apply Spec.homEquiv.injective
    apply CommRingCat.hom_ext
    apply Subsingleton.elim)

@[simp]
theorem overPointOfMorphism_left (g : Spec (.of ℚ) ⟶ scheme) :
    (overPointOfMorphism g).left = g :=
  rfl

/-- Coordinate points exhaust all scheme-valued rational points of the
explicit reduced projective cubic. -/
theorem affinePointMorphism_bijective :
    Function.Bijective (affinePointMorphism curve) := by
  constructor
  · exact affinePointMorphism_injective curve
  · intro g
    obtain ⟨P, hP⟩ := (affinePointOverMorphism_bijective curve).2
      (overPointOfMorphism g)
    refine ⟨P, ?_⟩
    have hleft := congrArg (fun f => f.left) hP
    rw [affinePointOverMorphism_left, overPointOfMorphism_left] at hleft
    simpa only [AffineCommGroupScheme.testObject,
      WeierstrassProjectiveCubic.toOver] using hleft

/-- The canonical equivalence between coordinate points and honest rational
points of the explicit projective cubic scheme. -/
noncomputable def rationalPointEquiv :
    curve.toAffine.Point ≃ (Spec (.of ℚ) ⟶ scheme) :=
  Equiv.ofBijective (affinePointMorphism curve) affinePointMorphism_bijective

@[simp]
theorem rationalPointEquiv_apply (P : curve.toAffine.Point) :
    rationalPointEquiv P = affinePointMorphism curve P :=
  rfl

/-- The point at infinity as an actual rational point of the projective
cubic scheme. -/
noncomputable def infinityCusp : Spec (.of ℚ) ⟶ scheme :=
  rationalPointEquiv 0

/-- The finite point `(0,0)` as an actual rational point of the projective
cubic scheme. -/
noncomputable def finiteCusp : Spec (.of ℚ) ⟶ scheme :=
  rationalPointEquiv T

/-- The two rational cusps are distinct as scheme morphisms. -/
theorem infinityCusp_ne_finiteCusp : infinityCusp ≠ finiteCusp := by
  intro h
  have hpoints : (0 : curve.toAffine.Point) = T :=
    rationalPointEquiv.injective h
  exact WeierstrassCurve.Affine.Point.some_ne_zero
    nonsingular_zero_zero hpoints.symm

/-- Every rational point of the represented projective cubic is one of its
two rational cusps. -/
theorem point_eq_infinityCusp_or_finiteCusp
    (g : Spec (.of ℚ) ⟶ scheme) :
    g = infinityCusp ∨ g = finiteCusp := by
  obtain ⟨P, rfl⟩ := affinePointMorphism_bijective.2 g
  obtain rfl | rfl := point_eq_zero_or_T P
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A rational scheme point is noncuspidal when it avoids both represented
cusp morphisms. -/
def IsNoncuspidal (g : Spec (.of ℚ) ⟶ scheme) : Prop :=
  g ≠ infinityCusp ∧ g ≠ finiteCusp

/-- The represented rational target has no noncuspidal rational point. -/
theorem not_isNoncuspidal (g : Spec (.of ℚ) ⟶ scheme) :
    ¬ IsNoncuspidal g := by
  intro h
  obtain hg | hg := point_eq_infinityCusp_or_finiteCusp g
  · exact h.1 hg
  · exact h.2 hg

end MazurTorsion.XZeroFortyNine.SchemeModel
