/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Scheme-theoretic images inside a closed factor

If a morphism factors through a closed immersion, its
scheme-theoretic image is a closed subscheme of that closed factor.
This elementary universal property is useful when the factor is affine:
the image is then affine as well.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

namespace SchemeTheoreticImage

/-- The scheme-theoretic image of `f = g ≫ j` maps canonically to the
closed factor of the factorization. -/
def toClosedFactor
    {X A Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ A) (j : A ⟶ Y)
    [IsClosedImmersion j] (h : f = g ≫ j) :
    f.image ⟶ A :=
  IsClosedImmersion.lift j f.imageι (by
    rw [Scheme.IdealSheafData.ker_subschemeι, h]
    exact Scheme.Hom.le_ker_comp g j)

/-- The map from the scheme-theoretic image to a closed factor followed
by that factor recovers the image immersion. -/
@[reassoc (attr := simp)]
theorem toClosedFactor_comp
    {X A Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ A) (j : A ⟶ Y)
    [IsClosedImmersion j] (h : f = g ≫ j) :
    toClosedFactor f g j h ≫ j = f.imageι :=
  IsClosedImmersion.lift_fac j f.imageι _

/-- The original map to the closed factor is the map to the
scheme-theoretic image followed by `toClosedFactor`. -/
@[reassoc (attr := simp)]
theorem toImage_toClosedFactor
    {X A Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ A) (j : A ⟶ Y)
    [IsClosedImmersion j] (h : f = g ≫ j) :
    f.toImage ≫ toClosedFactor f g j h = g := by
  rw [← cancel_mono j, Category.assoc,
    toClosedFactor_comp, Scheme.Hom.toImage_imageι, h]

/-- The scheme-theoretic image is a closed subscheme of every closed
factor through which the original morphism factors. -/
instance isClosedImmersion_toClosedFactor
    {X A Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ A) (j : A ⟶ Y)
    [IsClosedImmersion j] (h : f = g ≫ j) :
    IsClosedImmersion (toClosedFactor f g j h) := by
  letI :
      IsClosedImmersion
        (toClosedFactor f g j h ≫ j) := by
    rw [toClosedFactor_comp]
    infer_instance
  exact
    IsClosedImmersion.of_comp_isClosedImmersion
      (toClosedFactor f g j h) j

/-- A scheme-theoretic image contained in an affine closed factor is
affine. -/
theorem isAffine_image_of_closedFactor
    {X A Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ A) (j : A ⟶ Y)
    [IsClosedImmersion j] (h : f = g ≫ j)
    [IsAffine A] :
    IsAffine f.image := by
  letI :
      IsClosedImmersion (toClosedFactor f g j h) :=
    isClosedImmersion_toClosedFactor f g j h
  exact isAffine_of_isAffineHom
    (toClosedFactor f g j h)

end SchemeTheoreticImage

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
