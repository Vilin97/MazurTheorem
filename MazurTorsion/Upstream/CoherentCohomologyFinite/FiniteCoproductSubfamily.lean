/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Epimorphisms detected by a coproduct subfamily

If a selected family of maps already covers an object, then adjoining
further coproduct summands does not destroy surjectivity.  The selected
source objects may map to the corresponding large-family source objects;
this form is convenient when local trivializations identify only a
subfamily of a geometric coproduct.
-/


open CategoryTheory CategoryTheory.Limits

universe v u w

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

variable {C : Type u} [Category.{v} C]

/--
A coproduct map is an epimorphism if a family factoring through some of
its summands already has epimorphic coproduct descent.
-/
theorem epi_sigmaDesc_of_epi_subfamily
    {ι : Type w} {κ : Type w}
    (A : ι → C) (B : κ → C) {Y : C}
    [HasCoproduct A] [HasCoproduct B]
    (index : κ → ι)
    (toSummand : ∀ k, B k ⟶ A (index k))
    (component : ∀ i, A i ⟶ Y)
    (hsub :
      Epi
        (Limits.Sigma.desc
          (fun k => toSummand k ≫ component (index k)))) :
    Epi (Limits.Sigma.desc component) := by
  let inclusion : (∐ B) ⟶ (∐ A) :=
    Limits.Sigma.desc
      (fun k => toSummand k ≫ Limits.Sigma.ι A (index k))
  let subfamily : (∐ B) ⟶ Y :=
    Limits.Sigma.desc
      (fun k => toSummand k ≫ component (index k))
  letI : Epi subfamily := hsub
  apply epi_of_epi_fac (f := inclusion) (h := subfamily)
  apply Limits.Sigma.hom_ext
  intro k
  simp only [inclusion, subfamily, Category.assoc,
    Limits.Sigma.ι_desc, Limits.Sigma.ι_desc_assoc]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
