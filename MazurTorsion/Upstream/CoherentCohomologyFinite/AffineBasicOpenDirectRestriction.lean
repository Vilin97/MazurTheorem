/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineBasicOpenPresentation

/-!
# Direct restriction to an affine basic open

The iterated restriction through `D(g) ≅ Spec R_g` agrees with direct
restriction along the localization morphism `Spec R_g ⟶ Spec R`.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The basic-open restriction constructed through the open subscheme is
isomorphic to restriction along `Spec.map (R ⟶ R_g)`. -/
noncomputable def modulesRestrictBasicOpenDirectIso
    (g : R) (M : (Spec R).Modules) :
    modulesRestrictBasicOpen g M ≅
      M.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away g)))) :=
  ((Scheme.Modules.restrictFunctorComp
    (basicOpenIsoSpecAway g).inv
    (specBasicOpen g).ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr
        (specAwayToSpec_eq g)).app M

open SheafOfModules in
/-- An over-site presentation near `D(g)` gives a presentation after
direct restriction along `Spec.map (R ⟶ R_g)`. -/
noncomputable def presentationDirectAwayOfOver
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (M.over U).Presentation) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (M.restrict
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (Localization.Away g))))).Presentation :=
  @Presentation.ofIsIso.{u, u, u}
    _ _ _ _ _ _ _ _
    (modulesRestrictBasicOpenDirectIso g M).hom
    (modulesRestrictBasicOpenDirectIso g M).isIso_hom
    (presentationModulesRestrictBasicOpen M U P g hg)

end AlgebraicGeometry
