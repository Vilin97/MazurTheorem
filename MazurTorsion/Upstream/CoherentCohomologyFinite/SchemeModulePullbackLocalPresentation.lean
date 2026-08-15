/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenBaseChangeMate
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePullbackPresentation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverPresentationInverse

/-!
# Local presentations under scheme-module pullback

A presentation on a target open pulls back along the restricted
morphism.  Open base change identifies the result with the restriction
of the global pullback, after which the open-slice equivalence produces
the corresponding presentation on the inverse-image slice site.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}

/-- Pull a presentation on a geometric open restriction to the
corresponding inverse-image restriction. -/
noncomputable def pullbackRestrictionPresentation
    (U : Y.Opens)
    (P : (M.restrict U.ι).Presentation) :
    (((pullback f).obj M).restrict
      (f ⁻¹ᵁ U).ι).Presentation :=
  let Plocal :
      ((pullback (f ∣_ U)).obj
        (M.restrict U.ι)).Presentation :=
    Presentation.pullback (f ∣_ U) P
  let e := (pullbackRestrictBaseChangeIso f U).app M
  @SheafOfModules.Presentation.ofIsIso.{u, u, u}
    _ _ _ _ _ _ _ _ e.hom e.isIso_hom Plocal

/-- Pull a presentation on a target slice site to the corresponding
inverse-image slice site. -/
noncomputable def pullbackOverPresentation
    (U : Y.Opens) (P : (M.over U).Presentation) :
    (((pullback f).obj M).over (f ⁻¹ᵁ U)).Presentation :=
  Presentation.overOfRestrict
    (f ⁻¹ᵁ U) ((pullback f).obj M)
    (pullbackRestrictionPresentation f U
      (Presentation.restrictOfOver U M P))

end AlgebraicGeometry.Scheme.Modules
