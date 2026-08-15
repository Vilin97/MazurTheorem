/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeMorphismRestrictionIso

/-!
# Shrinking an isomorphism open by an upstairs open

Suppose a morphism is an isomorphism over an open `U` of its target.
An open `W` upstairs then determines a smaller target open: transport
`W` across the inverse over `U`, and include the result into the target.
The construction records its preimage, its isomorphism property, and
the elementary point-membership criterion used in support dévissage.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- Transport an upstairs open through the inverse of a morphism that is
an isomorphism over `U`. -/
def isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) : Y.Opens :=
  U.ι ''ᵁ
    (((inv (f ∣_ U)) ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ W)

/-- The transported open is contained in the original isomorphism
open. -/
theorem isomorphismTargetShrink_le
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    isomorphismTargetShrink f U W ≤ U :=
  U.ι_image_le _

/-- The inverse image of the transported open is exactly the part of
`W` lying over `U`. -/
theorem preimage_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    f ⁻¹ᵁ isomorphismTargetShrink f U W =
      (f ⁻¹ᵁ U) ⊓ W := by
  rw [isomorphismTargetShrink,
    ← image_morphismRestrict_preimage]
  simp only [← Scheme.Hom.comp_preimage,
    IsIso.hom_inv_id_assoc,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

/-- The morphism remains an isomorphism over the transported smaller
open. -/
theorem isIso_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    IsIso (f ∣_ isomorphismTargetShrink f U W) :=
  isIso_morphismRestrict_of_le f U _
    (isomorphismTargetShrink_le f U W)

/-- A target point belongs to the transported open whenever its inverse
image over `U` belongs to `W`. -/
theorem mem_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) (x : U.toScheme)
    (hx :
      (f ⁻¹ᵁ U).ι ((inv (f ∣_ U)) x) ∈ W) :
    U.ι x ∈ isomorphismTargetShrink f U W := by
  change
    x ∈ U.ι ⁻¹ᵁ isomorphismTargetShrink f U W
  rw [isomorphismTargetShrink,
    U.ι.preimage_image_eq]
  exact hx

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
