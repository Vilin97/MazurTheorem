/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Isomorphisms after shrinking a target open

If a scheme morphism is an isomorphism over an open subset of its
target, it remains an isomorphism over every smaller open subset.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- An isomorphism over an open remains an isomorphism after shrinking
the target open. -/
theorem isIso_morphismRestrict_of_le
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : Y.Opens) (hVU : V ≤ U)
    [IsIso (f ∣_ U)] :
    IsIso (f ∣_ V) := by
  let h :=
    IsOpenImmersion.isPullback
      (f ∣_ V)
      (X.homOfLE (f.preimage_mono hVU))
      (Y.homOfLE hVU)
      (f ∣_ U)
      (morphismRestrict_homOfLE f V U hVU).symm
      (by
        simp only [Scheme.opensRange_homOfLE,
          ← Scheme.Hom.comp_preimage,
          morphismRestrict_ι])
  exact h.isIso_fst_of_isIso

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
