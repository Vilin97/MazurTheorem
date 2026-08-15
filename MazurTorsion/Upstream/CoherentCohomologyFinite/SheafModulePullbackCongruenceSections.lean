/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleEffectiveDescent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleRestrictionPullbackComposition

/-!
# Pullback congruence on sections

The restriction/pullback comparison for an open immersion is compatible
with replacing the immersion by an equal morphism.  This file records the
inverse and pointwise forms needed by overlap calculations.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

lemma moduleHom_mapIso_hom_app
    {X : Scheme} {M N : X.Modules}
    (e : M ⟶ N) {U V : X.Opens} (h : U = V)
    (x : Γ(M, V)) :
    (N.presheaf.mapIso (eqToIso h).op).hom.hom
        (e.app V x) =
      e.app U
        ((M.presheaf.mapIso (eqToIso h).op).hom.hom x) := by
  subst V
  simp

lemma restrictFunctorIsoPullback_congr_inv
    {X Y : Scheme} {φ ψ : X ⟶ Y}
    (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ]
    (M : Y.Modules) :
    (restrictFunctorIsoPullback ψ).hom.app M ≫
        (pullbackCongr h).inv.app M =
      (restrictFunctorCongr h).inv.app M ≫
        (restrictFunctorIsoPullback φ).hom.app M := by
  rw [← cancel_mono ((pullbackCongr h).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rw [restrictFunctorIsoPullback_congr]
  simp

lemma restrictFunctorIsoPullback_congr_inv_app
    {X Y : Scheme} {φ ψ : X ⟶ Y}
    (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ]
    (M : Y.Modules) (U : X.Opens)
    (x : Γ(M.restrict ψ, U)) :
    ((pullbackCongr h).inv.app M).app U
        (((restrictFunctorIsoPullback ψ).hom.app M).app U x) =
      ((restrictFunctorIsoPullback φ).hom.app M).app U
        (((restrictFunctorCongr h).inv.app M).app U x) := by
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply] using
    congrArg (fun q => q.app U x)
      (restrictFunctorIsoPullback_congr_inv h M)

lemma pullbackCongr_inv_app_proof_irrel
    {X Y : Scheme} {φ ψ : X ⟶ Y}
    (h h' : φ = ψ) (M : Y.Modules) (U : X.Opens)
    (x : Γ((pullback ψ).obj M, U)) :
    ((pullbackCongr h).inv.app M).app U x =
      ((pullbackCongr h').inv.app M).app U x := by
  have hh : h = h' := Subsingleton.elim _ _
  subst h'
  rfl

end AlgebraicGeometry.Scheme.Modules
