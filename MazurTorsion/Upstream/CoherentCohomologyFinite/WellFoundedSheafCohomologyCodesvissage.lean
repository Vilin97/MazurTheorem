/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.WellFoundedExtCodesvissage

/-!
# Sheaf-cohomology codévissage by closed support

The abstract Ext codévissage cannot be applied directly in the category of
scheme modules: `Ext` there is not sheaf cohomology.  This file maps the
kernel--image--cokernel sequences to the exact underlying-ab\-elian-sheaf
functor and applies the Ext long exact sequence in the sheaf category.

The resulting theorem is the support-induction engine needed for a
comparison `M ⟶ π_* N` supplied by a modification.
-/


open CategoryTheory Limits AlgebraicGeometry TensorProduct
open TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

noncomputable local instance wellFoundedCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- All cohomology groups of a scheme module are finite-dimensional after
rationalization. -/
def RationalSheafHFinite
    {X : Scheme.{0}} (M : X.Modules) : Prop :=
  ∀ n : ℕ, Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n)

namespace RationalSheafHFinite

variable {X : Scheme.{0}}

/-- A zero scheme module has finite rationalized sheaf cohomology. -/
theorem of_isZero (M : X.Modules) (hM : IsZero M) :
    RationalSheafHFinite M := by
  let constantZ :=
    (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift ℤ))
  have hsheaf : IsZero M.sheaf :=
    (Scheme.Modules.toUnderlyingSheaf X).map_isZero hM
  change
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
      constantZ M.sheaf
  exact
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite.of_isZero
      constantZ M.sheaf hsheaf

/-- Rationalized sheaf-cohomology finiteness is closed under extensions. -/
theorem middle
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : RationalSheafHFinite S.X₁)
    (h₃ : RationalSheafHFinite S.X₃) :
    RationalSheafHFinite S.X₂ := by
  let U := Scheme.Modules.toUnderlyingSheaf X
  let T := S.map U
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS U
  let constantZ :=
    (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift ℤ))
  have h₁' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₁ := by
    dsimp only [constantZ, T, U]
    change RationalSheafHFinite S.X₁
    exact h₁
  have h₃' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₃ := by
    dsimp only [constantZ, T, U]
    change RationalSheafHFinite S.X₃
    exact h₃
  have h₂' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₂ :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite.middle
      hT h₁' h₃'
  dsimp only [constantZ, T, U] at h₂'
  exact h₂'

/-- Rationalized sheaf-cohomology finiteness descends to a submodule in
a short exact sequence. -/
theorem left
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₂ : RationalSheafHFinite S.X₂)
    (h₃ : RationalSheafHFinite S.X₃) :
    RationalSheafHFinite S.X₁ := by
  let U := Scheme.Modules.toUnderlyingSheaf X
  let T := S.map U
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS U
  let constantZ :=
    (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift ℤ))
  have h₂' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₂ := by
    dsimp only [constantZ, T, U]
    change RationalSheafHFinite S.X₂
    exact h₂
  have h₃' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₃ := by
    dsimp only [constantZ, T, U]
    change RationalSheafHFinite S.X₃
    exact h₃
  have h₁' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₁ :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite.left
      hT h₂' h₃'
  dsimp only [constantZ, T, U] at h₁'
  exact h₁'

/-- Rationalized sheaf-cohomology finiteness descends to a quotient in a
short exact sequence. -/
theorem right
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : RationalSheafHFinite S.X₁)
    (h₂ : RationalSheafHFinite S.X₂) :
    RationalSheafHFinite S.X₃ := by
  let U := Scheme.Modules.toUnderlyingSheaf X
  let T := S.map U
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS U
  let constantZ :=
    (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift ℤ))
  have h₁' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₁ := by
    dsimp only [constantZ, T, U]
    change RationalSheafHFinite S.X₁
    exact h₁
  have h₂' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₂ := by
    dsimp only [constantZ, T, U]
    change RationalSheafHFinite S.X₂
    exact h₂
  have h₃' :
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite
        constantZ T.X₃ :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.RationalExtFinite.right
      hT h₁' h₂'
  dsimp only [constantZ, T, U] at h₃'
  exact h₃'

end RationalSheafHFinite

/--
Well-founded sheaf-cohomology codévissage for comparisons `M ⟶ E`.
-/
theorem rationalSheafHFinite_of_wellFounded_comodels
    {α : Type*} (r : α → α → Prop) [IsWellFounded α r]
    {X : Scheme.{0}}
    (rank : X.Modules → α)
    (P Good : X.Modules → Prop)
    (hcomodel :
      ∀ (M : X.Modules), P M →
        ∃ (E : X.Modules) (f : M ⟶ E),
          Good E ∧
          P (kernel (Abelian.factorThruImage f)) ∧
          P (cokernel (Abelian.image.ι f)) ∧
          (IsZero (kernel (Abelian.factorThruImage f)) ∨
            r (rank (kernel (Abelian.factorThruImage f))) (rank M)) ∧
          (IsZero (cokernel (Abelian.image.ι f)) ∨
            r (rank (cokernel (Abelian.image.ι f))) (rank M)))
    (hgood : ∀ E, Good E → RationalSheafHFinite E) :
    ∀ (M : X.Modules), P M → RationalSheafHFinite M := by
  let rel : X.Modules → X.Modules → Prop :=
    fun A B => r (rank A) (rank B)
  haveI : IsWellFounded X.Modules rel :=
    inferInstanceAs
      (IsWellFounded X.Modules (InvImage r rank))
  intro M hM
  induction M using IsWellFounded.induction rel with
  | ind M ih =>
      obtain
        ⟨E, f, hE, hPK, hPQ, hKsmaller, hQsmaller⟩ :=
        hcomodel M hM
      let K := kernel (Abelian.factorThruImage f)
      let I := Abelian.image f
      let Q := cokernel (Abelian.image.ι f)
      have hK : RationalSheafHFinite K := by
        rcases hKsmaller with hKzero | hKlt
        · exact RationalSheafHFinite.of_isZero K hKzero
        · exact ih K hKlt hPK
      have hQ : RationalSheafHFinite Q := by
        rcases hQsmaller with hQzero | hQlt
        · exact RationalSheafHFinite.of_isZero Q hQzero
        · exact ih Q hQlt hPQ
      have hEfinite : RationalSheafHFinite E :=
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
      have hI : RationalSheafHFinite I := by
        change RationalSheafHFinite S₂.X₁
        apply RationalSheafHFinite.left hS₂
        · change RationalSheafHFinite E
          exact hEfinite
        · change RationalSheafHFinite Q
          exact hQ
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
      change RationalSheafHFinite S₁.X₂
      apply RationalSheafHFinite.middle hS₁
      · change RationalSheafHFinite K
        exact hK
      · change RationalSheafHFinite I
        exact hI

/--
The Noetherian closed-stalk-support specialization.
-/
theorem rationalSheafHFinite_of_closedStalkSupport_comodels
    {X : Scheme.{0}} [NoetherianSpace X]
    (P Good : X.Modules → Prop)
    (hcomodel :
      ∀ (M : X.Modules), P M →
        ∃ (E : X.Modules) (f : M ⟶ E),
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
    (hgood : ∀ E, Good E → RationalSheafHFinite E) :
    ∀ (M : X.Modules), P M → RationalSheafHFinite M :=
  rationalSheafHFinite_of_wellFounded_comodels
    (fun Z W : Closeds X => Z < W)
    Scheme.Modules.closedStalkSupport P Good hcomodel hgood

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
