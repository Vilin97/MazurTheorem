/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafPositiveExact

/-!
# The augmented sheaf-level Cech resolution

This file proves that the augmentation into the sheaf-level Cech complex is monic for an
open cover, then packages the augmentation and the Cech complex into an acyclic cochain
complex.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private theorem cechSingletonIntersection_eq (i : Fin 1 → ι) :
    (∏ᶜ fun k : Fin 1 => U (i k)) = U (i 0) := by
  apply le_antisymm
  · exact leOfHom (Pi.π (fun k : Fin 1 => U (i k)) 0)
  · exact leOfHom (Pi.lift fun k : Fin 1 => homOfLE (by
      rw [Subsingleton.elim k 0]))

private theorem cechAugmentation_app_injective (hU : ⨆ i, U i = ⊤) (V : Opens X) :
    Function.Injective ((cechAugmentation F U).hom.app (op V)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply TopCat.Presheaf.IsSheaf.section_ext F.2
  intro x hxV
  have hxCover : x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  obtain ⟨i₀, hxi₀⟩ := Opens.mem_iSup.mp hxCover
  let i : Fin 1 → ι := fun _ => i₀
  let W : Opens X := V ⊓ (∏ᶜ fun k : Fin 1 => U (i k))
  have hWV : W ≤ V := inf_le_left
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨hxV, by simpa [i, cechSingletonIntersection_eq U i] using hxi₀⟩
  · have hi := congrArg (fun y => cechTermSectionsAddEquiv F U 0 V y i) hs
    rw [cechAugmentation_apply, map_zero, Pi.zero_apply] at hi
    simpa [W] using hi

/-- If the opens `U i` cover the whole space, the Cech augmentation is a monomorphism. -/
theorem cechAugmentation_mono (hU : ⨆ i, U i = ⊤) : Mono (cechAugmentation F U) := by
  refine CategoryTheory.Sheaf.mono_of_injective _ ?_
  intro V
  exact cechAugmentation_app_injective F U hU V.unop

/-- The sheaf-level Cech complex augmented by the original sheaf in degree zero. -/
private noncomputable def cechAugmentedComplex : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ :=
  CochainComplex.augment (cechComplex F U) (cechAugmentation F U) (by
    rw [cechComplex_d]
    exact cechAugmentation_comp F U)

private theorem cechAugmentedComplex_exactAt_zero (hU : ⨆ i, U i = ⊤) :
    (cechAugmentedComplex F U).ExactAt 0 := by
  letI := cechAugmentation_mono F U hU
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)]
  apply (ShortComplex.exact_iff_mono _ rfl).2
  change Mono (cechAugmentation F U)
  infer_instance

private theorem cechAugmentedComplex_exactAt_one (hU : ⨆ i, U i = ⊤) :
    (cechAugmentedComplex F U).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  change (cechAugmentedShortComplex F U).Exact
  exact cechAugmentedShortComplex_exact F U hU

private theorem cechAugmentedComplex_exactAt_add_two (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (cechAugmentedComplex F U).ExactAt (n + 2) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp)]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    cechAugmentedComplex, CochainComplex.augment, CochainComplex.augment_X_succ,
    CochainComplex.augment_d_succ_succ, cechComplex_X, cechComplex_d] using
      cechShortComplex_exact F U hU n

/-- The augmented sheaf-level Cech complex of an open cover is acyclic. -/
private theorem cechAugmentedComplex_acyclic (hU : ⨆ i, U i = ⊤) :
    (cechAugmentedComplex F U).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  rintro (_ | _ | n)
  · exact cechAugmentedComplex_exactAt_zero F U hU
  · exact cechAugmentedComplex_exactAt_one F U hU
  · exact cechAugmentedComplex_exactAt_add_two F U hU n

end TopCat.Sheaf
