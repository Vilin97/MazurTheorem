/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineCover

/-!
# Monomorphism into an affine-cover module

For a family of opens covering an affine spectrum, this file proves that the
adjunction-unit map into the product of restriction-pushforwards is a
monomorphism.  The proof is sectionwise: a section whose image is zero
restricts to zero on each member of the cover, hence is zero by the sheaf
condition.

The final short-exact declaration is a checked downstream consumer of the
monomorphism interface.  It is the exact sequence used for Kempf dimension
shifting through the quasicoherent cokernel constructed in
`SchemeModuleCohomologyAffineCover`.

The argument was cross-checked against AINTLIB's
`ForMathlib/AffineVanishing.lean` at commit
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.  The implementation here is an
independent derivation against this repository's exact Mathlib pin.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

private theorem toAffineCoverModule_app_injective
    {R : CommRingCat.{u}} {I : Type u} (M : (Spec R).Modules)
    (U : I → (Spec R).Opens) (hU : IsOpenCover U) (W : (Spec R).Opens) :
    Function.Injective ((toAffineCoverModule M U).app W) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.IsSheaf.section_ext M.isSheaf fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := hU.exists_mem x
  refine ⟨W ⊓ U i, inf_le_left, ⟨by simpa using ⟨hx, hi⟩, ?_⟩⟩
  rw [map_zero]
  have hzero :
      ((Scheme.Modules.restrictAdjunction (U i).ι).unit.app M).app W s = 0 := by
    rw [← toAffineCoverModule_comp_pi M U i]
    change
      (Pi.π (fun i ↦
        (Scheme.Modules.restrictFunctor (U i).ι ⋙
          Scheme.Modules.pushforward (U i).ι).obj M) i).app W
        ((toAffineCoverModule M U).app W s) = 0
    rw [hs]
    exact map_zero _
  rw [Scheme.Modules.restrictAdjunction_unit_app_app] at hzero
  have hle : W ⊓ U i ≤ (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    simpa only [inf_comm] using (le_refl (W ⊓ U i))
  have harrow :
      (homOfLE ((U i).ι.image_preimage_le W)).op ≫
          (homOfLE hle).op =
        (homOfLE inf_le_left).op :=
    Subsingleton.elim _ _
  calc
    M.presheaf.map (homOfLE inf_le_left).op s =
        M.presheaf.map
          ((homOfLE ((U i).ι.image_preimage_le W)).op ≫
            (homOfLE hle).op) s := by
      rw [harrow]
    _ = M.presheaf.map (homOfLE hle).op
        (M.presheaf.map
          (homOfLE ((U i).ι.image_preimage_le W)).op s) := by
      rw [Functor.map_comp]
      rfl
    _ = M.presheaf.map (homOfLE hle).op 0 := by
      exact congrArg
        (fun z ↦ M.presheaf.map (homOfLE hle).op z) hzero
    _ = 0 := by
      rw [map_zero]

/-- If the opens cover the affine spectrum, the adjunction-unit map into the
product of their restriction-pushforwards is monic. -/
theorem toAffineCoverModule_mono {R : CommRingCat.{u}}
    {I : Type u} (M : (Spec R).Modules) (U : I → (Spec R).Opens)
    (hU : IsOpenCover U) : Mono (toAffineCoverModule M U) := by
  have hmono : Mono ((Scheme.Modules.toPresheafOfModules (Spec R)).map
      (toAffineCoverModule M U)) := by
    apply PresheafOfModules.mono_of_injective
    intro W
    exact toAffineCoverModule_app_injective M U hU W.unop
  exact Functor.mono_of_mono_map
    (Scheme.Modules.toPresheafOfModules (Spec R)) hmono

/-- The cover inclusion and its ambient cokernel form a short exact sequence.
This is the dimension-shifting consumer of `toAffineCoverModule_mono`. -/
theorem affineCoverCokernel_shortExact {R : CommRingCat.{u}}
    {I : Type u} (M : (Spec R).Modules) (U : I → (Spec R).Opens)
    (hU : IsOpenCover U) :
    (ShortComplex.mk (toAffineCoverModule M U)
      (cokernel.π (toAffineCoverModule M U))
      (cokernel.condition (toAffineCoverModule M U))).ShortExact := by
  letI : Mono (toAffineCoverModule M U) :=
    toAffineCoverModule_mono M U hU
  exact ShortComplex.ShortExact.mk
    (ShortComplex.exact_cokernel (toAffineCoverModule M U))

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
