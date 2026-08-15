/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheaf
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentSections

/-!
# Base-ring scalars and sections on an open subscheme

This file records the compatibility of the structural base-ring action
with passage to an open subscheme.  It also packages the two elementary
linearity facts used when a sheaf of modules is restricted and then
trivialized.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable {k : Type} [CommRing k]
  {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of k))]

/-- The structural coefficient map on an open is the corresponding
`appLE` of the structural morphism. -/
lemma algebraMapOnOpen_eq_appLE (U : X.Opens) :
    algebraMapOnOpen (k := k) U =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom :=
  rfl

/-- Restricting a module section to the open subscheme respects the local
structure-sheaf action. -/
lemma sectionsRestrictTopAddEquiv_smul
    (M : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (x : Γ(M, U)) :
    sectionsRestrictTopAddEquiv M U ((M.smul a).hom x) =
      ((M.restrict U.ι).smul (U.topIso.inv.hom a)).hom
        (sectionsRestrictTopAddEquiv M U x) := by
  let himage : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [U.ι.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  change
    (M.restrictAppIso U.ι ⊤).inv.hom
        (M.presheaf.map (eqToHom himage).op (a • x)) =
      ((M.restrict U.ι).smul (U.topIso.inv.hom a)).hom
        ((M.restrictAppIso U.ι ⊤).inv.hom
          (M.presheaf.map (eqToHom himage).op x))
  rw [M.map_smul]
  rw [Scheme.Modules.smul_restrictAppIso_inv_apply]
  have hscalar :
      (U.ι.appIso ⊤).hom.hom
          (X.presheaf.map (eqToHom himage).op a) =
        U.topIso.inv.hom a := by
    rw [show himage = U.ι_image_top from Subsingleton.elim _ _]
    simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
    rfl
  rw [hscalar]
  rfl

/-- The map on top sections induced by an isomorphism of scheme modules
respects the structure-sheaf action. -/
lemma sectionsAddEquivOfIso_smul
    {M N : X.Modules} (e : M ≅ N)
    (a : Γ(X, ⊤)) (x : Γ(M, ⊤)) :
    sectionsAddEquivOfIso e ((M.smul a).hom x) =
      (N.smul a).hom (sectionsAddEquivOfIso e x) :=
  Scheme.Modules.Hom.app_smul e.hom a x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
