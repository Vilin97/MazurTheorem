/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingQcqsLocalization

/-!
# Base basic opens and a structural morphism

For a scheme over `Spec k`, the basic open cut out by a base-ring element
is exactly the inverse image of the corresponding distinguished open of
`Spec k`.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The global structural image of a base-ring element is the corresponding
`appTop` section. -/
lemma algebraMapOnOpen_top
    (r : k) :
    algebraMapOnOpen (k := k) (X := X) ⊤ r =
      (X ↘ Spec (CommRingCat.of k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) := by
  change
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ Spec (CommRingCat.of k)).appTop ≫
        X.presheaf.map (homOfLE le_top).op).hom r) =
      (X ↘ Spec (CommRingCat.of k)).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)
  convert ConcreteCategory.id_apply
    ((X ↘ Spec (CommRingCat.of k)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)) using 1
  rw [← X.presheaf.map_id]
  rfl

/-- A base basic open on the top open is the inverse image of the standard
distinguished open on the affine base. -/
lemma baseBasicOpen_top_eq_preimage
    (r : k) :
    baseBasicOpen (k := k) (X := X) ⊤ r =
      (X ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ
        PrimeSpectrum.basicOpen r := by
  let p := X ↘ Spec (CommRingCat.of k)
  calc
    baseBasicOpen (k := k) (X := X) ⊤ r =
        X.basicOpen
          (p.appTop
            ((Scheme.ΓSpecIso
              (CommRingCat.of k)).inv r)) := by
      unfold baseBasicOpen
      rw [algebraMapOnOpen_top (k := k) r]
    _ = p ⁻¹ᵁ
          (Spec (CommRingCat.of k)).basicOpen
            ((Scheme.ΓSpecIso
              (CommRingCat.of k)).inv r) :=
      (Scheme.preimage_basicOpen_top p _).symm
    _ = p ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
      exact congrArg
        (fun T : (Spec (CommRingCat.of k)).Opens =>
          p ⁻¹ᵁ T)
        (basicOpen_eq_of_affine
          (R := CommRingCat.of k) r)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
