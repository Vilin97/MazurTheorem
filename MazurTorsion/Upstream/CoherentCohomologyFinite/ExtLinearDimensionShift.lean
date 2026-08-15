/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAcyclicCoresolutionLES
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Linear source-side Ext dimension shifting

The long-exact-sequence construction in
`ExtAcyclicCoresolutionLES` is additive.  In a category linear over a
commutative ring, all its connecting maps are linear.  This file records
the corresponding linear equivalences, independently of any particular
resolution.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe w v u

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{v} C]

/-- The source-variable Ext connecting equivalence, with its coefficient
module structure retained. -/
noncomputable def extConnectingLinearEquivOfAcyclicMiddle
    {S : ShortComplex C} (hS : S.ShortExact) (B : C) (n : ℕ)
    (h₀ : Subsingleton (Abelian.Ext.{v} S.X₂ B n))
    (h₁ : Subsingleton (Abelian.Ext.{v} S.X₂ B (n + 1))) :
    Abelian.Ext.{v} S.X₁ B n ≃ₗ[R]
      Abelian.Ext.{v} S.X₃ B (n + 1) :=
  LinearEquiv.ofBijective
    (hS.extClass.precompOfLinear R B
      (by omega : 1 + n = n + 1))
    (extConnectingAddEquivOfAcyclicMiddle
      hS B n h₀ h₁).bijective

section SourceSyzygies

variable [CategoryWithHomology C]

/-- Iterated source-variable dimension shifting as a linear
equivalence. -/
noncomputable def sourceExtStaircaseLinearEquiv
    (K : ChainComplex C ℕ) (B : C)
    (hexact : ∀ q, K.ExactAt (q + 1))
    (hacyclic :
      ∀ q m, Subsingleton (Abelian.Ext.{v} (K.X q) B (m + 1)))
    (m s : ℕ) :
    Abelian.Ext.{v} (sourceSyzygyShortComplex K s).X₃ B (m + 1) ≃ₗ[R]
      Abelian.Ext.{v}
        (sourceSyzygyShortComplex K (s + m)).X₃ B 1 := by
  induction m generalizing s with
  | zero =>
      exact LinearEquiv.refl R _
  | succ m ih =>
      let hS : (sourceSyzygyShortComplex K s).ShortExact :=
        sourceSyzygyShortExact K s (hexact s)
      let shift :=
        (extConnectingLinearEquivOfAcyclicMiddle (R := R)
          hS B (m + 1)
          (hacyclic s m) (hacyclic s (m + 1))).symm
      let e := shift.trans (ih (s + 1))
      rw [show s + 1 + m = s + (m + 1) by omega] at e
      exact e

/-- Transport Ext contravariantly across an isomorphism, retaining
linearity over the coefficient ring. -/
noncomputable def sourceAugmentationExtLinearEquiv
    (K : ChainComplex C ℕ) {A : C}
    (e : K.opcycles 0 ≅ A) (B : C) (n : ℕ) :
    Abelian.Ext.{v} A B n ≃ₗ[R]
      Abelian.Ext.{v} (sourceSyzygyShortComplex K 0).X₃ B n where
  __ := sourceAugmentationExtAddEquiv K e B n
  map_smul' r x := by
    change
      (Abelian.Ext.mk₀ (sourceSyzygyZeroIso K e).hom).comp
          (r • x) (zero_add n) =
        r •
          (Abelian.Ext.mk₀ (sourceSyzygyZeroIso K e).hom).comp
            x (zero_add n)
    exact Abelian.Ext.comp_smul _ _ _ _

/-- The first connecting map out of a source syzygy, as a linear map. -/
noncomputable def sourceSyzygyHomToExtOneLinear
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1)) :
    ((sourceSyzygyShortComplex K q).X₁ ⟶ B) →ₗ[R]
      Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1 := by
  let S := sourceSyzygyShortComplex K q
  let hS : S.ShortExact := sourceSyzygyShortExact K q h
  exact
    (hS.extClass.precompOfLinear R B rfl).comp
      Abelian.Ext.linearEquiv₀.symm.toLinearMap

@[simp]
lemma sourceSyzygyHomToExtOneLinear_apply
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (x : (sourceSyzygyShortComplex K q).X₁ ⟶ B) :
    sourceSyzygyHomToExtOneLinear (R := R) K B q h x =
      sourceSyzygyHomToExtOne K B q h x.op :=
  rfl

lemma sourceSyzygyHomToExtOneLinear_surjective
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (hacyclic :
      Subsingleton (Abelian.Ext.{v} (K.X q) B 1)) :
    Function.Surjective
      (sourceSyzygyHomToExtOneLinear (R := R) K B q h) := by
  let S := sourceSyzygyShortComplex K q
  let hS : S.ShortExact := sourceSyzygyShortExact K q h
  letI : Subsingleton (Abelian.Ext.{v} S.X₂ B 1) := by
    change Subsingleton (Abelian.Ext.{v} (K.X q) B 1)
    exact hacyclic
  intro y
  have hy :
      (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x, hx⟩ :=
    Abelian.Ext.contravariant_sequence_exact₃
      hS B y hy (by omega : 1 + 0 = 1)
  refine ⟨Abelian.Ext.linearEquiv₀ (R := R) x, ?_⟩
  change
    hS.extClass.comp
      (Abelian.Ext.mk₀
        (Abelian.Ext.linearEquiv₀ (R := R) x))
      (by omega : 1 + 0 = 1) = y
  simpa using hx

end SourceSyzygies

end CategoryTheory
