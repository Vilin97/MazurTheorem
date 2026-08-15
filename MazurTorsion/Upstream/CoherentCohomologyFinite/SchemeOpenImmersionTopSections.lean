/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Top sections along open immersions

This file records the elementary formula identifying pullback of a global
function with restriction to the open range of an open immersion.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/--
Transporting the pullback of a global function across the open-immersion
section isomorphism is ordinary restriction to the open range.
-/
lemma openImmersion_appIso_inv_appTop
    {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (s : Γ(Y, ⊤)) :
    (f.appIso ⊤).inv (f.appTop s) =
      Y.presheaf.map
        (homOfLE
          (show f ''ᵁ (⊤ : X.Opens) ≤
            (⊤ : Y.Opens) from le_top)).op s := by
  have hcomp :
      f.app (⊤ : Y.Opens) ≫
        (f.appIso (f ⁻¹ᵁ (⊤ : Y.Opens))).inv =
        Y.presheaf.map
          (homOfLE
            (Set.image_preimage_subset f (⊤ : Y.Opens))).op :=
    Scheme.Hom.app_appIso_inv f (⊤ : Y.Opens)
  change
    (f.app (⊤ : Y.Opens) ≫
      (f.appIso (f ⁻¹ᵁ (⊤ : Y.Opens))).inv).hom s =
        (Y.presheaf.map
          (homOfLE
            (Set.image_preimage_subset f (⊤ : Y.Opens))).op).hom s
  exact congrArg (fun q => q.hom s) hcomp

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
