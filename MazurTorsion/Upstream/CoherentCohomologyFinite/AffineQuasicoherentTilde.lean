/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineBasicOpenExtension
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentCover

/-!
# Affine quasicoherent modules are tilde modules

A quasicoherent module sheaf on `Spec R` admits presentations on a finite
distinguished-open cover.  Presentations give the localization formula on
each member of that cover, and the finite extension-data theorem glues those
local formulas globally.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

open QuasicoherentTilde

/-- The basic-open extension data on the whole affine spectrum associated
to a quasicoherent module.  Keeping this construction generic in the
coordinate ring prevents unnecessary reduction of concrete presentation
rings at its later call sites. -/
theorem basicOpenExtensionData_top_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    QuasicoherentTilde.BasicOpenExtensionData M ⊤ := by
  rw [← QuasicoherentTilde.isLocalizing_iff_extensionData,
    ← isIso_fromTildeΓ_iff_isLocalizing]
  infer_instance

/-- A map of quasicoherent modules on an affine spectrum is an epimorphism
as soon as it is surjective on global sections. -/
theorem epi_of_appTop_surjective
    {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N)
    (hf : Function.Surjective (f.val.app (.op ⊤)).hom) :
    Epi f := by
  have hN : Epi (tilde.adjunction.counit.app N) :=
    (isIso_fromTildeΓ_of_isQuasicoherent N).epi_of_iso
  let q := moduleSpecΓFunctor.map f
  have hq : Epi q :=
    (ModuleCat.epi_iff_surjective q).mpr hf
  letI : Epi q := hq
  have hmap : Epi ((tilde.functor R).map q) := by
    infer_instance
  have hcomp : Epi
      ((tilde.functor R).map q ≫
        tilde.adjunction.counit.app N) :=
    epi_comp' hmap hN
  have hnat :
      (tilde.functor R).map q ≫
          tilde.adjunction.counit.app N =
        tilde.adjunction.counit.app M ≫ f :=
    tilde.adjunction.counit_naturality f
  constructor
  intro Z g h w
  apply hcomp.left_cancellation g h
  rw [hnat, Category.assoc, w, ← Category.assoc]

end AlgebraicGeometry.Scheme.Modules
