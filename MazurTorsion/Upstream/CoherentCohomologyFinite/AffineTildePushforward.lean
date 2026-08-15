/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineHomPushforward

/-!
# Tilde and affine pushforward

For a ring homomorphism `R ⟶ S`, pushing the tilde of an `S`-module
forward along `Spec S ⟶ Spec R` agrees with taking the tilde after
restriction of scalars.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/--
Global sections of a pushed-forward tilde module are the restriction of
scalars of the original tilde module's global sections.
-/
noncomputable def pushforwardTildeGlobalSectionsIso (N : ModuleCat S) :
    moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)) ≅
      (ModuleCat.restrictScalars φ.hom).obj
        (moduleSpecΓFunctor.obj (tilde N)) := by
  let E :=
    TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
      (evaluation (Spec R).Opensᵒᵖ (ModuleCat R)).obj
        (Opposite.op (⊤ : (Spec R).Opens))
  exact E.mapIso ((pushforwardCompModulesSpecToSheafIso φ).app (tilde N))

/--
Tilde commutes with restriction of scalars and pushforward along a morphism
of affine spectra.
-/
noncomputable def tildeRestrictScalarsIsoPushforward (N : ModuleCat S) :
    tilde ((ModuleCat.restrictScalars φ.hom).obj N) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N) := by
  letI : IsIso (tilde N).fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr ⟨N, ⟨Iso.refl _⟩⟩
  let hPushforward :
      IsIso
        ((Scheme.Modules.pushforward (Spec.map φ)).obj
          (tilde N)).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ (tilde N)
  let eΓ :
      (ModuleCat.restrictScalars φ.hom).obj N ≅
        moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)) :=
    (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop N) ≪≫
      (pushforwardTildeGlobalSectionsIso φ N).symm
  exact
    (tilde.functor R).mapIso eΓ ≪≫
      @asIso _ _ _ _
        (Scheme.Modules.fromTildeΓ
          ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)))
        hPushforward

end AlgebraicGeometry
