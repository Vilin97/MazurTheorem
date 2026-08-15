/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentTilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Epimorphisms from finite affine generating families

A spanning family of global sections of a quasicoherent module on an
affine spectrum induces the expected epimorphism from a finite free module
sheaf.  The construction is made through the tilde functor so that
epimorphy follows directly from surjectivity of linear combination.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- The map from the free module sheaf associated to a family of affine
global sections. -/
def freeToModuleOfTopSections
    (M : (Spec R).Modules) {ι : Type u}
    (s : ι → Γ(M, ⊤)) :
    SheafOfModules.free
      (R := (Spec R).ringCatSheaf) ι ⟶ M :=
  (tildeFinsupp (R := R) ι).inv ≫
    (tilde.functor R).map
      (ModuleCat.ofHom (Finsupp.linearCombination R s)) ≫
    M.fromTildeΓ

/-- A spanning family of affine global sections yields an epimorphism from
the corresponding free module sheaf. -/
theorem freeToModuleOfTopSections_epi
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    {ι : Type u} (s : ι → Γ(M, ⊤))
    (hs : Submodule.span R (Set.range s) = ⊤) :
    Epi (freeToModuleOfTopSections M s) := by
  let q :
      ModuleCat.of R (ι →₀ R) ⟶
        ModuleCat.of R Γ(M, ⊤) :=
    ModuleCat.ofHom (Finsupp.linearCombination R s)
  have hsurj : Function.Surjective q.hom :=
    (span_range_eq_top_iff_surjective_finsuppLinearCombination
      (R : Type u) (v := s)).mp hs
  have hq : Epi q :=
    (ModuleCat.epi_iff_surjective q).mpr hsurj
  letI : Epi q := hq
  have htilde : Epi ((tilde.functor R).map q) := by
    infer_instance
  letI : Epi ((tilde.functor R).map q) := htilde
  let e := tildeFinsupp (R := R) ι
  change Epi
    (e.inv ≫
      (tilde.functor R).map q ≫ M.fromTildeΓ)
  letI : IsIso M.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent M
  letI : Epi M.fromTildeΓ := by infer_instance
  letI : IsIso e.inv := e.isIso_inv
  letI : Epi e.inv := by
    constructor
    intro Z g h hgh
    have hcancel := congrArg (fun z => e.hom ≫ z) hgh
    exact (e.hom_inv_id_assoc g).symm.trans
      (hcancel.trans (e.hom_inv_id_assoc h))
  constructor
  intro Z g h hgh
  apply (cancel_epi M.fromTildeΓ).1
  apply (cancel_epi ((tilde.functor R).map q)).1
  apply (cancel_epi e.inv).1
  exact
    (CategoryTheory.whisker_eq e.inv
        (Category.assoc ((tilde.functor R).map q)
          M.fromTildeΓ g).symm).trans
      ((Category.assoc e.inv
        ((tilde.functor R).map q ≫ M.fromTildeΓ) g).symm.trans
        (hgh.trans
          ((Category.assoc e.inv
            ((tilde.functor R).map q ≫ M.fromTildeΓ) h).trans
            (CategoryTheory.whisker_eq e.inv
              (Category.assoc ((tilde.functor R).map q)
                M.fromTildeΓ h)))))

end AlgebraicGeometry.Scheme.Modules
