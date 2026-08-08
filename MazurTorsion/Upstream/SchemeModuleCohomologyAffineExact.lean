/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import MazurTorsion.Upstream.SchemeModuleCohomologyHZero

/-!
# Exactness of affine quasicoherent global sections

This file proves one of the algebraic inputs to affine acyclicity for actual
scheme modules.  If `M ⟶ N` is an epimorphism of quasicoherent modules on
`Spec R`, then the induced map on global sections is surjective.  The proof
uses Mathlib's equivalence between `R`-modules and quasicoherent modules on
`Spec R`: the counit identifies each quasicoherent module with the tilde of
its global sections, and full faithfulness of tilde reflects epimorphisms.

As a concrete cohomological consumer, the final theorem transports this
surjectivity through the checked `H⁰ ≃ Γ` comparison for Mathlib's genuine
Ext-based sheaf cohomology.

The dimension-shifting proof of positive-degree affine acyclicity still also
requires local killing of cohomology classes and closure of quasicoherent
modules under the finite cover-sheaf and cokernel constructions.  No
positive-degree vanishing statement is asserted here.

The mathematical role of this lemma in affine-vanishing arguments was
cross-checked against AINTLIB's `ForMathlib/AffineVanishing.lean` at commit
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.  This implementation uses only
the independently checked Mathlib API at this repository's exact pin.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- Global sections on `Spec R` preserve an epimorphism between actual
quasicoherent scheme modules. -/
theorem moduleSpecGlobalSections_epi_of_epi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Epi (moduleSpecΓFunctor.map f) := by
  haveI : IsIso M.fromTildeΓ := inferInstance
  haveI : IsIso N.fromTildeΓ := inferInstance
  have hnat :
      tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
        M.fromTildeΓ ≫ f := by
    exact Scheme.Modules.fromTildeΓNatTrans.naturality f
  have hright : Epi (M.fromTildeΓ ≫ f) :=
    epi_comp' (by infer_instance) (by infer_instance)
  have hcomp : Epi (tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ) :=
    hnat.symm ▸ hright
  have hmapped : Epi (tilde.map (moduleSpecΓFunctor.map f)) :=
    (epi_comp_iff_of_isIso _ N.fromTildeΓ).mp hcomp
  exact (tilde.functor R).epi_of_epi_map hmapped

/-- An epimorphism of quasicoherent modules on an affine spectrum is
surjective on genuine global sections. -/
theorem moduleSpecGlobalSections_surjective_of_epi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.app (⊤ : Opens (Spec R))) :=
  (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f)).mp
    (moduleSpecGlobalSections_epi_of_epi f)

/-- The genuine Ext-based `H⁰` functor sends an epimorphism of
quasicoherent modules on `Spec R` to a surjective group homomorphism.

This is the checked cohomological consumer of
`moduleSpecGlobalSections_surjective_of_epi`. -/
theorem moduleSpecHZero_surjective_of_epi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective ((zariskiFunctor (Spec R) 0).map f) := by
  intro y
  obtain ⟨x, hx⟩ := moduleSpecGlobalSections_surjective_of_epi f
    (hZeroEquivGlobalSections N y)
  refine ⟨(hZeroEquivGlobalSections M).symm x, ?_⟩
  apply (hZeroEquivGlobalSections N).injective
  rw [← hZeroEquivGlobalSections_naturality]
  rw [(hZeroEquivGlobalSections M).apply_symm_apply]
  exact hx

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
