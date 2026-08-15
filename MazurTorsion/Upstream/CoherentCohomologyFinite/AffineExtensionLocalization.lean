/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineExtensionGluing

/-!
# Localizing sheaves and extension data

The abstract statement that sections on every distinguished open are an
away localization is equivalent to the elementwise existence-and-uniqueness
conditions used by the finite gluing argument.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.QuasicoherentTilde

variable {R : CommRingCat.{u}}

/-- A module sheaf on an affine spectrum is localizing exactly when its
sections satisfy basic-open extension and power-uniqueness over the terminal
open. -/
theorem isLocalizing_iff_extensionData
    (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔
      BasicOpenExtensionData M ⊤ := by
  let φ (f : R) :=
    ((modulesSpecToSheaf.obj M).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom
  refine ⟨fun h => ?_, fun h f => ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hfTop s => ?_, fun f hfTop s hs => ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      exact ⟨n, y, hy.symm⟩
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      exact ⟨n, hn⟩
  · refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
    · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
    · intro x
      obtain ⟨n, t, ht⟩ := h.existence _ _ x
      exact ⟨n, t, ht.symm⟩
    · intro x hx
      obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
      exact ⟨n, hn⟩

end AlgebraicGeometry.QuasicoherentTilde
