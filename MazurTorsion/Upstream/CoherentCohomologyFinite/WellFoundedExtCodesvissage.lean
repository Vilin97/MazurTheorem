/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ModuleSupport
import MazurTorsion.Upstream.CoherentCohomologyFinite.WellFoundedExtDevissage

/-!
# Ext codévissage along a well-founded support measure

This is the dual orientation of `rationalExtFinite_of_wellFounded_models`.
Here an object maps *into* a good model.  Factoring a comparison
`Y ⟶ E` through its image gives short exact sequences

`0 ⟶ ker ⟶ Y ⟶ image ⟶ 0`

and

`0 ⟶ image ⟶ E ⟶ coker ⟶ 0`.

If the kernel and cokernel vanish or have strictly smaller support, the
Ext long exact sequence and well-founded induction prove finiteness for
`Y`.  This is the orientation naturally supplied by the pullback--pushforward
unit of a modification.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe u v w t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X : C}

/--
Well-founded kernel--image--cokernel codévissage.

The relation `r` is typically strict inclusion of closed supports.  A
comparison points from the object under study to a good model.  Residual
objects are allowed to be zero, which avoids demanding a strict decrease
below a minimal support.
-/
theorem rationalExtFinite_of_wellFounded_comodels
    {α : Type t} (r : α → α → Prop) [IsWellFounded α r]
    (rank : C → α) (P Good : C → Prop)
    (hcomodel :
      ∀ (Y : C), P Y →
        ∃ (E : C) (f : Y ⟶ E),
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
        hcomodel Y hY
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
      have hI : RationalExtFinite X I := by
        exact RationalExtFinite.left hS₂ hEfinite hQ
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
      exact RationalExtFinite.middle hS₁ hK hI

/--
The closed-stalk-support specialization of well-founded codévissage on a
Noetherian scheme.
-/
theorem rationalExtFinite_of_closedStalkSupport_comodels
    {S : Scheme.{u}} [NoetherianSpace S]
    [HasExt.{w} S.Modules]
    (A : S.Modules) (P Good : S.Modules → Prop)
    (hcomodel :
      ∀ (M : S.Modules), P M →
        ∃ (E : S.Modules) (f : M ⟶ E),
          Good E ∧
          P (kernel (Abelian.factorThruImage f)) ∧
          P (cokernel (Abelian.image.ι f)) ∧
          (IsZero (kernel (Abelian.factorThruImage f)) ∨
            Scheme.Modules.closedStalkSupport
                (kernel (Abelian.factorThruImage f)) <
              Scheme.Modules.closedStalkSupport M) ∧
          (IsZero (cokernel (Abelian.image.ι f)) ∨
            Scheme.Modules.closedStalkSupport
                (cokernel (Abelian.image.ι f)) <
              Scheme.Modules.closedStalkSupport M))
    (hgood : ∀ E, Good E → RationalExtFinite A E) :
    ∀ (M : S.Modules), P M → RationalExtFinite A M :=
  rationalExtFinite_of_wellFounded_comodels
    (fun Z W : Closeds S => Z < W)
    Scheme.Modules.closedStalkSupport P Good hcomodel hgood

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
