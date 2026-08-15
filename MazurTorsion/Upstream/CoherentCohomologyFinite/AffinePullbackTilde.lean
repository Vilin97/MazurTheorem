/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineTildePushforward
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Pullback of an affine tilde module

For a ring homomorphism `R ⟶ S`, pullback along
`Spec S ⟶ Spec R` agrees with extension of scalars under the affine
tilde construction.  The comparison is defined canonically by uniqueness
of left adjoints.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/--
Global sections after affine pushforward are restriction of scalars.
-/
noncomputable def pushforwardModuleSpecΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙
        moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙
        ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun N => by
      let E :=
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (evaluation (Spec R).Opensᵒᵖ (ModuleCat R)).obj
            (Opposite.op (⊤ : (Spec R).Opens))
      exact
        E.mapIso
          ((pushforwardCompModulesSpecToSheafIso φ).app N))
    (by cat_disch)

/--
The composite `tilde` then scheme-theoretic pullback is left adjoint to
affine global sections followed by restriction of scalars.
-/
noncomputable def tildePullbackAdjunction :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
      moduleSpecΓFunctor (R := S) ⋙
        ModuleCat.restrictScalars φ.hom :=
  ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
    (pushforwardModuleSpecΓIso φ)

/--
Pulling back an associated module sheaf along a morphism of affine
spectra is canonically extension of scalars followed by `tilde`.
-/
noncomputable def pullbackTildeIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (tildePullbackAdjunction φ).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      (tilde.adjunction (R := S)))

/--
The transported composite unit is the tilde unit, followed by global
sections of the scheme-theoretic pullback--pushforward unit, followed by
the affine pushforward/global-sections comparison.
-/
theorem tildePullbackAdjunction_unit_app (M : ModuleCat R) :
    (tildePullbackAdjunction φ).unit.app M =
      (tilde.adjunction (R := R)).unit.app M ≫
        moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (Spec.map φ)).unit.app (tilde M)) ≫
        (pushforwardModuleSpecΓIso φ).hom.app
          ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)) := by
  simp [tildePullbackAdjunction]
  exact Category.assoc _ _ _

/--
The affine pullback--tilde comparison intertwines the transported
scheme-theoretic unit with the extension-of-scalars composite unit.
-/
theorem pullbackTildeIso_unit (M : ModuleCat R) :
    (tildePullbackAdjunction φ).unit.app M ≫
        (moduleSpecΓFunctor (R := S) ⋙
          ModuleCat.restrictScalars φ.hom).map
            ((pullbackTildeIso φ).hom.app M) =
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
        (tilde.adjunction (R := S))).unit.app M :=
  (tildePullbackAdjunction φ).unit_leftAdjointUniq_hom_app
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      (tilde.adjunction (R := S))) M

end AlgebraicGeometry
