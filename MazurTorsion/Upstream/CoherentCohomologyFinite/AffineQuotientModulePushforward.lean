/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineTildePushforward
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteModuleTildeCoherence
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Affine descent to an ideal-quotient closed subscheme

An `R`-module annihilated by an ideal `I` carries its canonical
`R ⧸ I`-module structure.  This file identifies its tilde on `Spec R`
with the pushforward of the corresponding tilde on `Spec (R ⧸ I)`.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The closed immersion of the spectrum of an ideal quotient. -/
def idealQuotientSpecMap (I : Ideal R) :
    Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/--
The module over `R ⧸ I` induced by the assertion that `I` annihilates
the original `R`-module.
-/
noncomputable def quotientModule (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    ModuleCat (R ⧸ I) :=
  letI := h.module
  ModuleCat.of (R ⧸ I) M

/--
After restricting scalars, the quotient-ring module is canonically the
original `R`-module.
-/
noncomputable def quotientModuleRestrictionIso (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    ModuleCat.of R M ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (quotientModule I h) := by
  let f :
      ModuleCat.of R M ⟶
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h) :=
    ModuleCat.ofHom
      (X := ModuleCat.of R M)
      (Y :=
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h))
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r m => (h.mk_smul r m).symm }
  let g :
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h) ⟶
        ModuleCat.of R M :=
    ModuleCat.ofHom
      (X :=
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h))
      (Y := ModuleCat.of R M)
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r m => h.mk_smul r m }
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        ext x
        change id (id x) = x
        rfl
      inv_hom_id := by
        ext x
        change id (id x) = x
        rfl }

/-- The coherent-module candidate on the ideal-quotient spectrum. -/
noncomputable def quotientTilde (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    (Spec (.of (R ⧸ I))).Modules :=
  tilde (quotientModule I h)

/--
Affine essential-image theorem for an annihilated module: its tilde is
the pushforward of its quotient-ring tilde along the quotient-spectrum
closed immersion.
-/
noncomputable def tildeIsoPushforwardQuotientTilde (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    tilde (ModuleCat.of R M) ≅
      (Scheme.Modules.pushforward (idealQuotientSpecMap I)).obj
        (quotientTilde I h) :=
  (tilde.functor (.of R)).mapIso (quotientModuleRestrictionIso I h) ≪≫
    tildeRestrictScalarsIsoPushforward
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) (quotientModule I h)

/--
Finiteness over `R` descends to finiteness over the quotient ring when
the quotient action is induced by annihilation by `I`.
-/
theorem quotientModule_finite [Module.Finite R M] (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    Module.Finite (R ⧸ I) (quotientModule I h) := by
  letI : Module (R ⧸ I) M := h.module
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

/--
Over a Noetherian ring, the quotient-ring tilde supplied by annihilation
is a coherent module on the quotient spectrum.
-/
theorem quotientTilde_isFinitePresentation
    [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    (quotientTilde I h).IsFinitePresentation := by
  let N : ModuleCat.{u} (R ⧸ I) := quotientModule I h
  change
    (tilde (R := CommRingCat.of (R ⧸ I)) N).IsFinitePresentation
  letI hfinite :
      Module.Finite (R ⧸ I) N :=
    quotientModule_finite I h
  exact
    Scheme.Modules.tilde_isFinitePresentation_of_module_finite
      (R := CommRingCat.of (R ⧸ I)) N

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}
variable (F : (Spec R).Modules) [F.IsQuasicoherent]

/--
The module on the ideal-quotient spectrum obtained from the annihilated
global-sections module of an affine quasicoherent module.
-/
noncomputable def affineQuotientTilde (I : Ideal R)
    (h : Module.IsTorsionBySet R
      (moduleSpecΓFunctor.obj F) (I : Set R)) :
    (Spec (.of ((R : Type u) ⧸ I))).Modules :=
  quotientTilde I h

/--
Affine sheaf-level essential-image theorem: a quasicoherent module whose
global-sections module is annihilated by `I` is the pushforward of its
quotient-ring tilde.
-/
noncomputable def isoPushforward_affineQuotientTilde (I : Ideal R)
    (h : Module.IsTorsionBySet R
      (moduleSpecΓFunctor.obj F) (I : Set R)) :
    F ≅
      (pushforward (idealQuotientSpecMap I)).obj
        (affineQuotientTilde F I h) := by
  let hCounit : IsIso F.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent F
  exact
    (@asIso _ _ _ _ F.fromTildeΓ hCounit).symm ≪≫
      tildeIsoPushforwardQuotientTilde I h

omit [F.IsQuasicoherent] in
/--
If the affine global-sections module is finite over a Noetherian base, the
descended quotient-ring module sheaf is coherent.
-/
theorem affineQuotientTilde_isFinitePresentation
    [IsNoetherianRing (R : Type u)]
    [Module.Finite R (moduleSpecΓFunctor.obj F)]
    (I : Ideal R)
    (h : Module.IsTorsionBySet R
      (moduleSpecΓFunctor.obj F) (I : Set R)) :
    (affineQuotientTilde F I h).IsFinitePresentation :=
  quotientTilde_isFinitePresentation I h

/--
Finite type and quasicoherence provide the finite global-sections
hypothesis needed by the affine quotient descent.
-/
theorem affineQuotientTilde_isFinitePresentation_of_isFiniteType
    [IsNoetherianRing (R : Type u)] [F.IsFiniteType]
    (I : Ideal R)
    (h : Module.IsTorsionBySet R
      (moduleSpecΓFunctor.obj F) (I : Set R)) :
    (affineQuotientTilde F I h).IsFinitePresentation := by
  letI :
      Module.Finite R (moduleSpecΓFunctor.obj F) :=
    finite_top_sections_of_isFiniteType_isQuasicoherent F
  exact affineQuotientTilde_isFinitePresentation F I h

end AlgebraicGeometry.Scheme.Modules
