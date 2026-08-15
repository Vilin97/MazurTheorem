/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OverSiteContinuity
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Transporting an over-site presentation to an affine basic open

This is the categorical bridge from the local presentations occurring in
`IsQuasicoherent` to presentations on spectra of away localizations.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The distinguished open `D(f)` in `Spec R`. -/
abbrev specBasicOpen (f : R) : (Spec R).Opens :=
  PrimeSpectrum.basicOpen f

/-- The localization morphism `Spec R_f ⟶ Spec R`, factored through
the distinguished open. -/
noncomputable abbrev specAwayToSpec (f : R) :
    Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec R :=
  (basicOpenIsoSpecAway f).inv ≫ (specBasicOpen f).ι

/-- Restriction to `D(f)`, transported along `D(f) ≅ Spec R_f`. -/
noncomputable def modulesRestrictBasicOpen (f : R)
    (M : (Spec R).Modules) :
    (Spec (CommRingCat.of (Localization.Away f))).Modules :=
  (M.restrict (specBasicOpen f).ι).restrict
    (basicOpenIsoSpecAway f).inv

/-- The iterated restriction agrees with restriction along the composite
localization morphism. -/
noncomputable def modulesRestrictBasicOpenIso (f : R)
    (M : (Spec R).Modules) :
    modulesRestrictBasicOpen f M ≅
      (Scheme.Modules.pullback (specAwayToSpec f)).obj M :=
  ((Scheme.Modules.restrictFunctorComp
    (basicOpenIsoSpecAway f).inv
    (specBasicOpen f).ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback
        (specAwayToSpec f)).app M

/-- The factored localization morphism is `Spec.map (R ⟶ R_f)`. -/
theorem specAwayToSpec_eq (f : R) :
    specAwayToSpec f =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away f))) := by
  rw [specAwayToSpec, Iso.inv_comp_eq]
  exact (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm

open SheafOfModules in
/-- A presentation on an over site restricts to a smaller over site. -/
noncomputable def presentationOverBasicOpen
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (M.over U).Presentation) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (M.over (specBasicOpen g)).Presentation :=
  let W : Over U := Over.mk (homOfLE hg)
  let e : SheafOfModules.{u}
      ((Spec R).ringCatSheaf.over W.left) ≌
      SheafOfModules.{u} (((Spec R).ringCatSheaf.over U).over W) :=
    pushforwardPushforwardEquivalence
      (Over.iteratedSliceEquiv W)
      (S := ((Spec R).ringCatSheaf.over U).over W)
      (R := (Spec R).ringCatSheaf.over W.left)
      (𝟙 _) (𝟙 _)
      (by ext : 2; exact (Spec R).ringCatSheaf.1.map_id _)
      (by ext : 2; exact (Spec R).ringCatSheaf.1.map_id _)
  let P₁ : ((M.over U).over W).Presentation :=
    P.map (pushforward (𝟙 (((Spec R).ringCatSheaf.over U).over W)))
      (by rfl)
  let P₂ : (e.inverse.obj ((M.over U).over W)).Presentation :=
    P₁.map e.inverse (.refl _)
  let iso : e.inverse.obj ((M.over U).over W) ≅ M.over W.left :=
    e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over U).over W))
  show (M.over W.left).Presentation from
    Presentation.ofIsIso.{u, u, u} iso.hom P₂

section OverRestriction

/-- Modules on `D(g)` are equivalent to modules on its over site. -/
noncomputable def modulesOverBasicOpenEquivalence (g : R) :
    (specBasicOpen g).toScheme.Modules ≌
      SheafOfModules.{u}
        ((Spec R).ringCatSheaf.over (specBasicOpen g)) :=
  (Scheme.Modules.overEquiv (specBasicOpen g)).symm

/-- The inverse over-site equivalence sends `M.over D(g)` to the usual
restriction of `M` to `D(g)`. -/
noncomputable def overBasicOpenIsoRestrict
    (g : R) (M : (Spec R).Modules) :
    (modulesOverBasicOpenEquivalence g).inverse.obj
        (M.over (specBasicOpen g)) ≅
      M.restrict (specBasicOpen g).ι := by
  change
    ((SheafOfModules.overFunctor (Spec R).ringCatSheaf (specBasicOpen g) ⋙
        (Scheme.Modules.overEquiv (specBasicOpen g)).functor).obj M) ≅
      (Scheme.Modules.restrictFunctor (specBasicOpen g).ι).obj M
  exact (Scheme.Modules.overFunctorEquiv (specBasicOpen g)).app M

end OverRestriction

end AlgebraicGeometry
