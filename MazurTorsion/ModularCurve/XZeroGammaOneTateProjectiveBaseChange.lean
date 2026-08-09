/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveFamily
import Mathlib.AlgebraicGeometry.Limits

/-!
# Arbitrary base change of the universal projective Tate family

For every scheme morphism `t : T ⟶ tateBase R`, this file constructs the
categorical pullback of the universal projective Tate family, its projection
to `T`, and the pulled-back zero and marked sections.  The defining square and
both section identities are pinned to Mathlib's chosen pullback.

This is an arbitrary scheme base-change statement.  It deliberately does not
identify a non-affine pullback with `Proj` of a global coefficient ring, and it
does not assert the stronger affine scalar-extension comparison, a group law,
or compatibility of multiplication by an integer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

variable (R : CommRingCat.{u}) {T : Scheme.{u}} (t : T ⟶ tateBase R)

/-- The universal projective Tate family pulled back along `t`. -/
@[reducible]
noncomputable def baseChangeFamily : Scheme.{u} :=
  pullback (familyProjection R) t

/-- The comparison from the pulled-back family to the universal family. -/
noncomputable def baseChangeToFamily : baseChangeFamily R t ⟶ family R :=
  pullback.fst _ _

/-- The pulled-back Tate-family projection to `T`. -/
noncomputable def baseChangeProjection : baseChangeFamily R t ⟶ T :=
  pullback.snd _ _

/-- The defining square of the arbitrary scheme base change. -/
theorem baseChange_condition :
    baseChangeToFamily R t ≫ familyProjection R =
      baseChangeProjection R t ≫ t :=
  pullback.condition

/-- The displayed square is the chosen categorical pullback square. -/
theorem baseChange_isPullback :
    IsPullback (baseChangeToFamily R t) (baseChangeProjection R t)
      (familyProjection R) t :=
  IsPullback.of_hasPullback _ _

/-- The zero section pulled back to `T`. -/
noncomputable def baseChangeZeroSection : T ⟶ baseChangeFamily R t :=
  pullback.lift (t ≫ zeroSection R) (𝟙 T) (by
    rw [Category.assoc, zeroSection_familyProjection,
      Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem baseChangeZeroSection_toFamily :
    baseChangeZeroSection R t ≫ baseChangeToFamily R t =
      t ≫ zeroSection R :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeZeroSection_projection :
    baseChangeZeroSection R t ≫ baseChangeProjection R t = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- The marked Tate section pulled back to `T`. -/
noncomputable def baseChangeMarkedSection : T ⟶ baseChangeFamily R t :=
  pullback.lift (t ≫ markedSection R) (𝟙 T) (by
    rw [Category.assoc, markedSection_familyProjection,
      Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem baseChangeMarkedSection_toFamily :
    baseChangeMarkedSection R t ≫ baseChangeToFamily R t =
      t ≫ markedSection R :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeMarkedSection_projection :
    baseChangeMarkedSection R t ≫ baseChangeProjection R t = 𝟙 T :=
  pullback.lift_snd _ _ _

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
