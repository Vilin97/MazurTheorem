/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AcyclicResolution
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Ext from acyclic resolutions

This file connects Mathlib's two descriptions of derived functors:

* `Functor.rightDerived`, computed by applying a functor to an injective resolution;
* `Ext`, presented by `InjectiveResolution.extMk` as cycles modulo boundaries.

For a fixed object `A`, applying `preadditiveCoyoneda.obj (op A)` to an injective
resolution of `B` gives the usual cochain complex `Hom(A, I •)`.  We identify its
homology with `Ext A B n`.  Composing this identification with
`Functor.rightDerivedIsoOfAcyclicResolution` then lets any acyclic resolution
compute Ext.
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  {A B : C} (I : InjectiveResolution B)

/-- The pointwise Hom complex attached to an injective resolution. -/
noncomputable abbrev coyonedaCocomplex :
  CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (Opposite.op A)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    I.cocomplex

/-- A cycle in the pointwise Hom complex, represented as a morphism into the
corresponding term of the injective resolution. -/
noncomputable abbrev CoyonedaCycle (n : ℕ) :=
  AddMonoidHom.ker ((I.coyonedaCocomplex (A := A)).d n (n + 1)).hom

@[simp]
lemma coyonedaCocomplex_X (n : ℕ) :
    (I.coyonedaCocomplex (A := A)).X n = AddCommGrpCat.of (A ⟶ I.cocomplex.X n) :=
  rfl

@[simp]
lemma coyonedaCocomplex_d_apply {n m : ℕ} (f : A ⟶ I.cocomplex.X n) :
    (I.coyonedaCocomplex (A := A)).d n m f = f ≫ I.cocomplex.d n m :=
  rfl

/-- Send a cocycle in `Hom(A, I •)` to the Ext class represented by it. -/
noncomputable def coyonedaCycleToExt (n : ℕ) :
    I.CoyonedaCycle (A := A) n →+ Abelian.Ext.{v} A B n where
  toFun x :=
    I.extMk x.1 (n + 1) rfl (by
      change
        (I.coyonedaCocomplex (A := A)).d n (n + 1) x.1 = 0
      exact x.2)
  map_zero' := by
    apply I.extMk_zero
  map_add' x y := by
    symm
    apply I.add_extMk

@[simp]
lemma coyonedaCycleToExt_apply (n : ℕ) (x : I.CoyonedaCycle (A := A) n) :
    I.coyonedaCycleToExt n x =
      I.extMk x.1 (n + 1) rfl (by
        change
          (I.coyonedaCocomplex (A := A)).d n (n + 1) x.1 = 0
        exact x.2) :=
  rfl

/-- The three-term window of `Hom(A, I •)` centered in positive degree `n + 1`. -/
noncomputable abbrev coyonedaShortComplex (n : ℕ) : ShortComplex AddCommGrpCat.{v} :=
  (I.coyonedaCocomplex (A := A)).sc' n (n + 1) (n + 2)

/-- The Ext-class map on the literal cycle group used by the short-complex API. -/
noncomputable def coyonedaShortComplexCycleToExt (n : ℕ) :
    AddMonoidHom.ker (I.coyonedaShortComplex (A := A) n).g.hom →+
      Abelian.Ext.{v} A B (n + 1) where
  toFun x :=
    I.extMk x.1 (n + 2) (by omega) (by
      change
        (I.coyonedaCocomplex (A := A)).d (n + 1) (n + 2) x.1 = 0
      exact x.2)
  map_zero' := by
    apply I.extMk_zero
  map_add' x y := by
    symm
    apply I.add_extMk

lemma coyonedaShortComplexCycleToExt_surjective (n : ℕ) :
    Function.Surjective (I.coyonedaShortComplexCycleToExt (A := A) n) := by
  intro α
  obtain ⟨f, hf, hα⟩ := I.extMk_surjective α (n + 2) (by omega)
  let x : AddMonoidHom.ker (I.coyonedaShortComplex (A := A) n).g.hom :=
    ⟨f, by
      change
        (I.coyonedaCocomplex (A := A)).d (n + 1) (n + 2) f = 0
      rw [I.coyonedaCocomplex_d_apply (A := A)]
      exact hf⟩
  exact ⟨x, hα⟩

lemma coyonedaCycleToExt_surjective (n : ℕ) :
    Function.Surjective (I.coyonedaCycleToExt (A := A) (n + 1)) := by
  intro α
  obtain ⟨f, hf, hα⟩ := I.extMk_surjective α (n + 2) (by omega)
  let x : I.CoyonedaCycle (A := A) (n + 1) :=
    ⟨f, by
      change
        (I.coyonedaCocomplex (A := A)).d (n + 1) (n + 2) f = 0
      rw [I.coyonedaCocomplex_d_apply (A := A)]
      exact hf⟩
  exact ⟨x, hα⟩

/-- Boundaries in the positive-degree pointwise Hom complex are exactly the
cocycles representing the zero Ext class. -/
lemma coyonedaBoundaryRange_eq_ker_cycleToExt (n : ℕ) :
    AddMonoidHom.range (I.coyonedaShortComplex (A := A) n).abToCycles =
      AddMonoidHom.ker (I.coyonedaShortComplexCycleToExt (A := A) n) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change
      I.extMk (y ≫ I.cocomplex.d n (n + 1)) (n + 2) (by omega) (by
        exact ConcreteCategory.congr_hom
          ((I.coyonedaCocomplex (A := A)).d_comp_d
            n (n + 1) (n + 2)) y) = 0
    apply (I.extMk_eq_zero_iff
      (y ≫ I.cocomplex.d n (n + 1)) (n + 2) (by omega) (by
        exact ConcreteCategory.congr_hom
          ((I.coyonedaCocomplex (A := A)).d_comp_d
            n (n + 1) (n + 2)) y) n (by omega)).2
    exact ⟨y, rfl⟩
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    change I.extMk x.1 (n + 2) (by omega) (by
      change
        (I.coyonedaCocomplex (A := A)).d (n + 1) (n + 2) x.1 = 0
      exact x.2) = 0 at hx
    obtain ⟨y, hy⟩ :=
      (I.extMk_eq_zero_iff x.1 (n + 2) (by omega) (by
        change
          (I.coyonedaCocomplex (A := A)).d (n + 1) (n + 2) x.1 = 0
        exact x.2) n (by omega)).mp hx
    refine ⟨y, Subtype.ext ?_⟩
    exact hy

/-- The concrete quotient description of positive-degree homology is Ext. -/
noncomputable def coyonedaHomologyQuotientAddEquivExt (n : ℕ) :
    (AddMonoidHom.ker (I.coyonedaShortComplex (A := A) n).g.hom ⧸
      AddMonoidHom.range (I.coyonedaShortComplex (A := A) n).abToCycles) ≃+
      Abelian.Ext.{v} A B (n + 1) :=
    (QuotientAddGroup.quotientAddEquivOfEq
      (I.coyonedaBoundaryRange_eq_ker_cycleToExt (A := A) n)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (I.coyonedaShortComplexCycleToExt (A := A) n)
      (I.coyonedaShortComplexCycleToExt_surjective (A := A) n))

/-- The short-complex homology of `Hom(A, I •)` in positive degree is Ext. -/
noncomputable def coyonedaShortComplexHomologyIsoExt (n : ℕ) :
    (I.coyonedaShortComplex (A := A) n).homology ≅
      AddCommGrpCat.of (Abelian.Ext.{v} A B (n + 1)) :=
  (I.coyonedaShortComplex (A := A) n).abHomologyIso ≪≫
    (I.coyonedaHomologyQuotientAddEquivExt (A := A) n).toAddCommGrpIso

/-- Positive-degree homology of the whole pointwise Hom complex is Ext. -/
noncomputable def coyonedaCocomplexHomologyIsoExt (n : ℕ) :
    (I.coyonedaCocomplex (A := A)).homology (n + 1) ≅
      AddCommGrpCat.of (Abelian.Ext.{v} A B (n + 1)) :=
  (I.coyonedaCocomplex (A := A)).homologyIsoSc'
      n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    I.coyonedaShortComplexHomologyIsoExt (A := A) n

/-- The positive right-derived functors of `Hom(A, -)` are Ext. -/
noncomputable def rightDerivedCoyonedaIsoExtPositive [HasInjectiveResolutions C] (n : ℕ) :
    ((preadditiveCoyoneda.obj (Opposite.op A)).rightDerived (n + 1)).obj B ≅
      AddCommGrpCat.of (Abelian.Ext.{v} A B (n + 1)) :=
  I.isoRightDerivedObj (preadditiveCoyoneda.obj (Opposite.op A)) (n + 1) ≪≫
    I.coyonedaCocomplexHomologyIsoExt (A := A) n

end CategoryTheory.InjectiveResolution

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  [HasInjectiveResolutions C] {A B : C}

/-- In every degree, the right-derived functor of `Hom(A, -)` is Ext.
Degree zero uses `Ext.addEquiv₀`; positive degrees use an injective resolution. -/
noncomputable def rightDerivedCoyonedaIsoExt (n : ℕ) :
    ((preadditiveCoyoneda.obj (Opposite.op A)).rightDerived n).obj B ≅
      AddCommGrpCat.of (Abelian.Ext.{v} A B n) := by
  cases n with
  | zero =>
      exact
        (preadditiveCoyoneda.obj (Opposite.op A)).rightDerivedZeroIsoSelf.app B ≪≫
          Abelian.Ext.addEquiv₀.symm.toAddCommGrpIso
  | succ n =>
      exact
        (injectiveResolution B).rightDerivedCoyonedaIsoExtPositive (A := A) n

/-- Every Ext group can be computed by any resolution whose terms are acyclic
for `Hom(A, -)`.

This is the Ext-facing form of `Functor.rightDerivedIsoOfAcyclicResolution`.
The degree-zero branch is supplied by the ordinary Hom identification above. -/
noncomputable def extIsoHomologyOfAcyclicResolution
    (K : CochainComplex C ℕ) (e : B ≅ K.cycles 0)
    (hexact : ∀ q, K.ExactAt (q + 1))
    [∀ q, (preadditiveCoyoneda.obj (Opposite.op A)).IsRightAcyclic (K.X q)]
    (n : ℕ) :
    AddCommGrpCat.of (Abelian.Ext.{v} A B n) ≅
      (((preadditiveCoyoneda.obj (Opposite.op A)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology n :=
  (rightDerivedCoyonedaIsoExt (A := A) (B := B) n).symm ≪≫
    (preadditiveCoyoneda.obj (Opposite.op A)).rightDerivedIsoOfAcyclicResolution
      K B e hexact n

end CategoryTheory
