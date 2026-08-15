/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Noetherian consequences of properness

A scheme proper over a field is quasi-compact and locally of finite type over
a Noetherian affine scheme.  This supplies the Noetherian hypotheses used by
coherent dévissage and Grothendieck vanishing.
-/

open CategoryTheory Limits AlgebraicGeometry
open TopologicalSpace

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u

/-- A scheme proper over a field is a Noetherian scheme. -/
theorem isNoetherian_of_isProper_to_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] :
    IsNoetherian X := by
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- The underlying space of a scheme proper over a field is Noetherian. -/
theorem noetherianSpace_of_isProper_to_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] :
    NoetherianSpace X := by
  letI : IsNoetherian X := isNoetherian_of_isProper_to_field f
  infer_instance

/--
A scheme proper over a field is separated as an absolute scheme.
-/
theorem schemeIsSeparated_of_isProper_to_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] :
    X.IsSeparated := by
  haveI :
      IsSeparated
        (f ≫ terminal.from (Spec (CommRingCat.of K))) :=
    inferInstance
  have h :
      f ≫ terminal.from (Spec (CommRingCat.of K)) =
        terminal.from X :=
    Subsingleton.elim _ _
  rw [h] at this
  exact ⟨this⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
