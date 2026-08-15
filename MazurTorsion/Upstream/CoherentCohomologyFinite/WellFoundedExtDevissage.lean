/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CohomologyDevissage
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Ext dévissage along a well-founded support measure

Suppose every object `Y` in a class admits a morphism `E ⟶ Y` from an
object whose Ext groups are already finite.  Factoring through the image
gives two short exact sequences

`0 ⟶ ker ⟶ E ⟶ image ⟶ 0`

and

`0 ⟶ image ⟶ Y ⟶ coker ⟶ 0`.

If the kernel and cokernel either vanish or have strictly smaller support,
well-founded induction and the Ext long exact sequence prove finiteness for
`Y`.  This is the abstract homological core of Noetherian support
dévissage after Chow's lemma.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u v w t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X : C}

/-- A zero target has finite rationalized Ext in every degree. -/
theorem RationalExtFinite.of_isZero
    (X Y : C) (hY : IsZero Y) :
    RationalExtFinite X Y := by
  intro n
  have hsub : Subsingleton (Abelian.Ext X Y n) := by
    constructor
    intro e₁ e₂
    suffices ∀ e : Abelian.Ext X Y n, e = 0 by
      rw [this e₁, this e₂]
    intro e
    calc
      e = e.comp (Abelian.Ext.mk₀ (𝟙 Y)) (add_zero n) := by simp
      _ = e.comp (Abelian.Ext.mk₀ (0 : Y ⟶ Y)) (add_zero n) := by
        rw [hY.eq_of_src (𝟙 Y) 0]
      _ = 0 := by simp
  letI : Subsingleton (Abelian.Ext X Y n) := hsub
  infer_instance

/--
Well-founded kernel--image--cokernel dévissage.

The relation `r` is typically strict inclusion of closed supports.  The
model hypothesis keeps the coherence predicate `P` explicit and allows a
residual object to be zero without demanding a nonexistent strictly
smaller support at a minimal closed set.
-/
theorem rationalExtFinite_of_wellFounded_models
    {α : Type t} (r : α → α → Prop) [IsWellFounded α r]
    (rank : C → α) (P Good : C → Prop)
    (hmodel :
      ∀ (Y : C), P Y →
        ∃ (E : C) (f : E ⟶ Y),
          Good E ∧
          P (kernel (Abelian.factorThruImage f)) ∧
          P (cokernel (Abelian.image.ι f)) ∧
          (IsZero (kernel (Abelian.factorThruImage f)) ∨
            r (rank (kernel (Abelian.factorThruImage f))) (rank Y)) ∧
          (IsZero (cokernel (Abelian.image.ι f)) ∨
            r (rank (cokernel (Abelian.image.ι f))) (rank Y)))
    (hgood : ∀ E, Good E → RationalExtFinite X E) :
    ∀ (Y : C), P Y → RationalExtFinite X Y := by
  let rel : C → C → Prop := fun A B => r (rank A) (rank B)
  haveI : IsWellFounded C rel :=
    inferInstanceAs (IsWellFounded C (InvImage r rank))
  intro Y hY
  induction Y using IsWellFounded.induction rel with
  | ind Y ih =>
      obtain
        ⟨E, f, hE, hPK, hPQ, hKsmaller, hQsmaller⟩ :=
        hmodel Y hY
      let K := kernel (Abelian.factorThruImage f)
      let I := Abelian.image f
      let Q := cokernel (Abelian.image.ι f)
      have hK : RationalExtFinite X K := by
        rcases hKsmaller with hKzero | hKlt
        · exact RationalExtFinite.of_isZero X K hKzero
        · exact ih K hKlt hPK
      have hQ : RationalExtFinite X Q := by
        rcases hQsmaller with hQzero | hQlt
        · exact RationalExtFinite.of_isZero X Q hQzero
        · exact ih Q hQlt hPQ
      have hEfinite : RationalExtFinite X E :=
        hgood E hE
      let S₁ :=
        ShortComplex.kernelSequence
          (Abelian.factorThruImage f)
      haveI : Epi S₁.g := by
        dsimp [S₁, ShortComplex.kernelSequence]
        infer_instance
      have hS₁ : S₁.ShortExact :=
        { exact :=
            ShortComplex.kernelSequence_exact
              (Abelian.factorThruImage f) }
      have hI : RationalExtFinite X I := by
        exact RationalExtFinite.right hS₁ hK hEfinite
      let S₂ :=
        ShortComplex.cokernelSequence
          (Abelian.image.ι f)
      haveI : Mono S₂.f := by
        dsimp [S₂, ShortComplex.cokernelSequence]
        infer_instance
      have hS₂ : S₂.ShortExact :=
        { exact :=
            ShortComplex.cokernelSequence_exact
              (Abelian.image.ι f) }
      exact RationalExtFinite.middle hS₂ hI hQ

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
