/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAcyclicCoresolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Source-side Ext dimension shifting without projectives

The right-derived-functor proof in `ExtAcyclicCoresolution` is convenient
when the ambient category has enough projectives.  Categories of sheaves
generally do not.  This file starts the projective-free comparison directly
from the contravariant long exact sequence for `Ext`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

/-- Across a short exact sequence with Ext-acyclic middle term, the
connecting morphism is the usual source-variable dimension-shift
equivalence. -/
noncomputable def extConnectingAddEquivOfAcyclicMiddle
    {S : ShortComplex C} (hS : S.ShortExact) (B : C) (n : ℕ)
    (h₀ : Subsingleton (Abelian.Ext.{v} S.X₂ B n))
    (h₁ : Subsingleton (Abelian.Ext.{v} S.X₂ B (n + 1))) :
    Abelian.Ext.{v} S.X₁ B n ≃+
      Abelian.Ext.{v} S.X₃ B (n + 1) := by
  letI : Subsingleton (Abelian.Ext.{v} S.X₂ B n) := h₀
  letI : Subsingleton (Abelian.Ext.{v} S.X₂ B (n + 1)) := h₁
  let δ := hS.extClass.precomp B (by omega : 1 + n = n + 1)
  exact AddEquiv.ofBijective δ ⟨by
    intro x y hxy
    apply sub_eq_zero.mp
    have hδ :
        hS.extClass.comp (x - y) (by omega : 1 + n = n + 1) = 0 := by
      change δ (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ :=
      Abelian.Ext.contravariant_sequence_exact₁
        hS B (x - y) (by omega : 1 + n = n + 1) hδ
    rw [← hz, Subsingleton.elim z 0]
    simp
  , by
    intro y
    have hy :
        (Abelian.Ext.mk₀ S.g).comp y (zero_add (n + 1)) = 0 :=
      Subsingleton.elim _ _
    obtain ⟨x, hx⟩ :=
      Abelian.Ext.contravariant_sequence_exact₃
        hS B y hy (by omega : 1 + n = n + 1)
    exact ⟨x, hx⟩⟩

section SourceSyzygies

variable [CategoryWithHomology C]

/-- The source syzygy sequence cut out of a chain complex.  It is obtained
by forming the cosyzygy sequence of the opposite cochain complex and
unoppositing it:
`Z_{q+1} ⟶ K_q ⟶ Z_q`. -/
noncomputable abbrev sourceSyzygyShortComplex
    (K : ChainComplex C ℕ) (q : ℕ) : ShortComplex C :=
  (Functor.cosyzygyShortComplex K.opCocomplex q).unop

/-- Exactness in degree `q+1` makes the source syzygy sequence short
exact. -/
theorem sourceSyzygyShortExact
    (K : ChainComplex C ℕ) (q : ℕ)
    (h : K.ExactAt (q + 1)) :
    (sourceSyzygyShortComplex K q).ShortExact :=
  (Functor.cosyzygyShortExact K.opCocomplex q
    (K.opCocomplex_exactAt_succ q h)).unop

/-- The connecting map from a contravariant-Hom cocycle at the next
syzygy to `Ext¹` of the current syzygy. -/
noncomputable def sourceSyzygyHomToExtOne
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1)) :
    (contravariantHomFunctor B).obj
        (K.opCocomplex.cycles (q + 1)) →+
      Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1 := by
  let S := sourceSyzygyShortComplex K q
  let hS : S.ShortExact := sourceSyzygyShortExact K q h
  change
    (Opposite.op B ⟶ Opposite.op S.X₁) →+
      Abelian.Ext.{v} S.X₃ B 1
  exact
    (hS.extClass.precomp B rfl).comp
      (Abelian.Ext.addEquiv₀.symm.toAddMonoidHom.comp
        (oppositeHomAddEquiv S.X₁ B).toAddMonoidHom)

lemma sourceSyzygyHomToExtOne_surjective
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (hacyclic :
      Subsingleton (Abelian.Ext.{v} (K.X q) B 1)) :
    Function.Surjective (sourceSyzygyHomToExtOne K B q h) := by
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
  refine ⟨(Abelian.Ext.addEquiv₀ x).op, ?_⟩
  change
    hS.extClass.comp
      (Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x))
      (by omega : 1 + 0 = 1) = y
  simpa using hx

/-- The boundaries in the contravariant Hom complex are exactly the
zeroth-Ext classes killed by the source connecting morphism. -/
lemma sourceSyzygyHomBoundaryRange_eq_ker
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1)) :
    AddMonoidHom.range
        ((contravariantHomFunctor B).map
          (K.opCocomplex.toCycles q (q + 1))).hom =
      AddMonoidHom.ker (sourceSyzygyHomToExtOne K B q h) := by
  let S := sourceSyzygyShortComplex K q
  let hS : S.ShortExact := sourceSyzygyShortExact K q h
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let yu : S.X₂ ⟶ B :=
      oppositeHomAddEquiv S.X₂ B y
    rw [AddMonoidHom.mem_ker]
    change
      hS.extClass.comp
        (Abelian.Ext.mk₀ (S.f ≫ yu))
        (by omega : 1 + 0 = 1) = 0
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Abelian.Ext.mk₀ yu)
  · intro hx
    let xu : S.X₁ ⟶ B :=
      oppositeHomAddEquiv S.X₁ B x
    rw [AddMonoidHom.mem_ker] at hx
    have hδ :
        hS.extClass.comp
          (Abelian.Ext.mk₀ xu)
          (by omega : 1 + 0 = 1) = 0 := by
      exact hx
    obtain ⟨z, hz⟩ :=
      Abelian.Ext.contravariant_sequence_exact₁
        hS B (Abelian.Ext.mk₀ x.unop)
          (by omega : 1 + 0 = 1) hδ
    refine ⟨(Abelian.Ext.addEquiv₀ z).op, ?_⟩
    apply Quiver.Hom.unop_inj
    change S.f ≫ Abelian.Ext.addEquiv₀ z = xu
    apply (Abelian.Ext.mk₀_bijective _ _).injective
    calc
      Abelian.Ext.mk₀ (S.f ≫ Abelian.Ext.addEquiv₀ z) =
          (Abelian.Ext.mk₀ S.f).comp
            (Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ z))
            (zero_add 0) :=
        (Abelian.Ext.mk₀_comp_mk₀ _ _).symm
      _ = (Abelian.Ext.mk₀ S.f).comp z (zero_add 0) := by
        rw [Abelian.Ext.mk₀_addEquiv₀_apply]
      _ = Abelian.Ext.mk₀ xu := hz

/-- The lowest source-variable dimension shift identifies the cokernel of
`Hom(K_q,B) → Hom(Z_{q+1},B)` with `Ext¹(Z_q,B)`. -/
noncomputable def sourceSyzygyCokernelIsoExtOne
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (hacyclic :
      Subsingleton (Abelian.Ext.{v} (K.X q) B 1)) :
    cokernel
        ((contravariantHomFunctor B).map
          (K.opCocomplex.toCycles q (q + 1))) ≅
      AddCommGrpCat.of
        (Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1) :=
  AddCommGrpCat.cokernelIsoQuotient
      ((contravariantHomFunctor B).map
        (K.opCocomplex.toCycles q (q + 1))) ≪≫
    ((QuotientAddGroup.quotientAddEquivOfEq
        (sourceSyzygyHomBoundaryRange_eq_ker K B q h)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (sourceSyzygyHomToExtOne K B q h)
        (sourceSyzygyHomToExtOne_surjective
          K B q h hacyclic))).toAddCommGrpIso

/-- Positive-degree Hom cohomology at the end of the source staircase is
the first Ext group of the corresponding syzygy. -/
noncomputable def contravariantHomHomologyIsoSyzygyExtOne
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (hacyclic :
      Subsingleton (Abelian.Ext.{v} (K.X q) B 1)) :
    (K.contravariantHomCocomplex B).homology (q + 1) ≅
      AddCommGrpCat.of
        (Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1) :=
  (contravariantHomFunctor B).cohomologyAppliedResolutionIso
      K.opCocomplex q ≪≫
    sourceSyzygyCokernelIsoExtOne K B q h hacyclic

/-- Iterated source-variable dimension shifting along the syzygy short
exact sequences of `K`. -/
noncomputable def sourceExtStaircaseAddEquiv
    (K : ChainComplex C ℕ) (B : C)
    (hexact : ∀ q, K.ExactAt (q + 1))
    (hacyclic :
      ∀ q m, Subsingleton (Abelian.Ext.{v} (K.X q) B (m + 1)))
    (m s : ℕ) :
    Abelian.Ext.{v} (sourceSyzygyShortComplex K s).X₃ B (m + 1) ≃+
      Abelian.Ext.{v}
        (sourceSyzygyShortComplex K (s + m)).X₃ B 1 := by
  induction m generalizing s with
  | zero =>
      exact AddEquiv.refl _
  | succ m ih =>
      let hS : (sourceSyzygyShortComplex K s).ShortExact :=
        sourceSyzygyShortExact K s (hexact s)
      let shift :=
        (extConnectingAddEquivOfAcyclicMiddle hS B (m + 1)
          (hacyclic s m) (hacyclic s (m + 1))).symm
      let e := shift.trans (ih (s + 1))
      rw [show s + 1 + m = s + (m + 1) by omega] at e
      exact e

/-- The zeroth source syzygy is the object resolved by the augmentation. -/
noncomputable def sourceSyzygyZeroIso
    (K : ChainComplex C ℕ) {A : C}
    (e : K.opcycles 0 ≅ A) :
    (sourceSyzygyShortComplex K 0).X₃ ≅ A :=
  (K.opIsoCyclesZero e).unop

/-- Transport Ext contravariantly across the augmentation isomorphism. -/
noncomputable def sourceAugmentationExtAddEquiv
    (K : ChainComplex C ℕ) {A : C}
    (e : K.opcycles 0 ≅ A) (B : C) (n : ℕ) :
    Abelian.Ext.{v} A B n ≃+
      Abelian.Ext.{v} (sourceSyzygyShortComplex K 0).X₃ B n :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction.precompIsoAddEquiv
    (sourceSyzygyZeroIso K e) n

/-- Actual morphisms out of the `q`-th source syzygy are the value of
contravariant Hom on the `q`-th cycles object of the opposite complex. -/
noncomputable def sourceSyzygyHomIsoContravariantHomCycles
    (K : ChainComplex C ℕ) (B : C) (q : ℕ) :
    AddCommGrpCat.of ((sourceSyzygyShortComplex K q).X₃ ⟶ B) ≅
      (contravariantHomFunctor B).obj (K.opCocomplex.cycles q) := by
  change
    AddCommGrpCat.of ((sourceSyzygyShortComplex K q).X₃ ⟶ B) ≅
      AddCommGrpCat.of
        (Opposite.op B ⟶
          Opposite.op (sourceSyzygyShortComplex K q).X₃)
  exact
    (oppositeHomAddEquiv
      (sourceSyzygyShortComplex K q).X₃ B).symm.toAddCommGrpIso

/-- **Projective-free source acyclic resolution theorem.**

Unlike `extIsoHomologyOfAcyclicCoresolution`, this version uses the
contravariant long exact sequence of Ext directly.  It therefore applies
to sheaf categories, which have enough injectives but need not have enough
projectives. -/
noncomputable def extIsoHomologyOfAcyclicCoresolutionLES
    (K : ChainComplex C ℕ) {A B : C}
    (e : K.opcycles 0 ≅ A)
    (hexact : ∀ q, K.ExactAt (q + 1))
    (hacyclic :
      ∀ q m, Subsingleton (Abelian.Ext.{v} (K.X q) B (m + 1)))
    (n : ℕ) :
    AddCommGrpCat.of (Abelian.Ext.{v} A B n) ≅
      (K.contravariantHomCocomplex B).homology n := by
  cases n with
  | zero =>
      let eExtZero :
          AddCommGrpCat.of
              (Abelian.Ext.{v}
                (sourceSyzygyShortComplex K 0).X₃ B 0) ≅
            AddCommGrpCat.of
              ((sourceSyzygyShortComplex K 0).X₃ ⟶ B) :=
        (Abelian.Ext.addEquiv₀
          (X := (sourceSyzygyShortComplex K 0).X₃)
          (Y := B)).toAddCommGrpIso
      exact
        (sourceAugmentationExtAddEquiv K e B 0).toAddCommGrpIso ≪≫
          eExtZero ≪≫
          sourceSyzygyHomIsoContravariantHomCycles K B 0 ≪≫
          (contravariantHomFunctor B).gHomologyZeroIso
            K.opCocomplex
  | succ m =>
      let stair :=
        sourceExtStaircaseAddEquiv K B hexact hacyclic m 0
      rw [Nat.zero_add] at stair
      let stairIso :
          AddCommGrpCat.of
              (Abelian.Ext.{v}
                (sourceSyzygyShortComplex K 0).X₃ B (m + 1)) ≅
            AddCommGrpCat.of
              (Abelian.Ext.{v}
                (sourceSyzygyShortComplex K m).X₃ B 1) :=
        stair.toAddCommGrpIso
      exact
        (sourceAugmentationExtAddEquiv K e B (m + 1)).toAddCommGrpIso ≪≫
          stairIso ≪≫
          (contravariantHomHomologyIsoSyzygyExtOne
            K B m (hexact m) (hacyclic m 0)).symm

end SourceSyzygies

end CategoryTheory
