/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFinitePresentation

/-!
# Coherence of the tilde of a finite module

Over a Noetherian ring, a finite module has a finite module presentation.
Applying tilde to that presentation gives a coherent module sheaf on the
affine spectrum.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (N : ModuleCat R)

/-- The tilde of a finite module over a Noetherian ring is coherent. -/
theorem tilde_isFinitePresentation_of_module_finite
    [IsNoetherianRing (R : Type u)] [Module.Finite R N] :
    (tilde N).IsFinitePresentation := by
  letI hfp : Module.FinitePresentation R N :=
    Module.finitePresentation_of_finite R N
  obtain ⟨s, hs, hker⟩ := hfp.out
  obtain ⟨t, ht⟩ := hker
  letI : Finite ↥(s : Set N) := s.finite_toSet.to_subtype
  letI : Finite ↥(t : Set ((s : Set N) →₀ R)) :=
    t.finite_toSet.to_subtype
  let P : (tilde N).Presentation :=
    presentationTilde N (s : Set N) hs
      (t : Set ((s : Set N) →₀ R)) ht
  letI : P.generators.IsFiniteType :=
    { finite := inferInstanceAs (Finite ↥(s : Set N)) }
  letI : P.relations.IsFiniteType :=
    { finite :=
        inferInstanceAs (Finite ↥(t : Set ((s : Set N) →₀ R))) }
  letI : P.IsFinite :=
    SheafOfModules.Presentation.IsFinite.mk
      (p := P) inferInstance inferInstance
  exact isFinitePresentation_of_finite_presentation (tilde N) P

end AlgebraicGeometry.Scheme.Modules
