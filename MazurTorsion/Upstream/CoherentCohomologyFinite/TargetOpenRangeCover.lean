/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Covering a morphism range by target opens

A source cover pulled back from one morphism can prove that the range
of a second morphism is covered by target opens, provided the
corresponding source preimages are contained chartwise.
-/

open AlgebraicGeometry TopologicalSpace

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- If the `Uᵢ` cover `X` and each inverse image under `a` lies in the
inverse image of `Vᵢ` under `g`, then the `Vᵢ` cover the range of
`g`. -/
theorem range_subset_iSup_of_preimage_le
    {Z X Y : Scheme.{u}} {ι : Type u}
    (a : Z ⟶ X) (g : Z ⟶ Y)
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hcover : ⨆ i, U i = ⊤)
    (hle : ∀ i, a ⁻¹ᵁ U i ≤ g ⁻¹ᵁ V i) :
    Set.range g ⊆ (⨆ i, V i : Y.Opens) := by
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ (⨆ i, a ⁻¹ᵁ U i : Z.Opens) := by
    rw [← a.preimage_iSup, hcover]
    trivial
  simp only [Opens.mem_iSup] at hz
  obtain ⟨i, hi⟩ := hz
  have hgi : g z ∈ V i :=
    hle i hi
  exact (le_iSup V i) hgi

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
