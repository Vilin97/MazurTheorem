/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAcyclicResolution
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Ext from source-side acyclic resolutions

This file is the source-variable dual of `ExtAcyclicResolution`.  A chain
resolution of the source is turned into a cochain resolution in the
opposite abelian category.  Applying the covariant Hom functor there is
the usual contravariant Hom cochain complex in the original category.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace ChainComplex

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Reverse an `ℕ`-indexed chain complex and pass to the opposite
category, obtaining an `ℕ`-indexed cochain complex. -/
@[simps]
noncomputable def opCocomplex (K : ChainComplex C ℕ) :
    CochainComplex Cᵒᵖ ℕ where
  X n := Opposite.op (K.X n)
  d i j := (K.d j i).op
  shape i j hij := by
    rw [K.shape j i hij, op_zero]
  d_comp_d' i j k hij hjk := by
    rw [← op_comp, K.d_comp_d k j i, op_zero]

section Abelian

variable [Abelian C] [CategoryWithHomology C]

omit [Abelian C] [CategoryWithHomology C] in
/-- Exactness in a positive chain degree is preserved by the explicit
opposite cochain construction. -/
lemma opCocomplex_exactAt_succ
    (K : ChainComplex C ℕ) (n : ℕ)
    (h : K.ExactAt (n + 1)) :
    K.opCocomplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    K.opCocomplex n (n + 1) (n + 2) (by simp) (by simp)]
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
      (by exact (Category.id_comp _).trans (Category.comp_id _).symm))
  rw [HomologicalComplex.exactAt_iff'
    K (n + 2) (n + 1) n (by simp) (by simp)] at h
  exact h.op

/-- An identification of the zeroth opcycles of a chain complex with
`A` becomes the augmentation of its opposite cochain complex. -/
noncomputable def opIsoCyclesZero
    (K : ChainComplex C ℕ) {A : C}
    (e : K.opcycles 0 ≅ A) :
    Opposite.op A ≅ K.opCocomplex.cycles 0 := by
  let hker :
      IsLimit
        (KernelFork.ofι (K.pOpcycles 0).op
          (show
            (K.pOpcycles 0).op ≫ K.opCocomplex.d 0 1 = 0 by
            change
              (K.pOpcycles 0).op ≫ (K.d 1 0).op = 0
            rw [← op_comp, K.d_pOpcycles 1 0, op_zero])) := by
    change
      IsLimit
        (KernelFork.ofι (K.pOpcycles 0).op
          (show
            (K.pOpcycles 0).op ≫ (K.d 1 0).op = 0 by
            rw [← op_comp, K.d_pOpcycles 1 0, op_zero]))
    exact
      CokernelCofork.IsColimit.ofπOp
        (K.pOpcycles 0) (K.d_pOpcycles 1 0)
        (K.opcyclesIsCokernel 1 0 (by simp))
  exact
    e.op ≪≫
      IsLimit.conePointUniqueUpToIso hker
        (K.opCocomplex.cyclesIsKernel 0 1 (by simp))

end Abelian

end ChainComplex

namespace CategoryTheory.ProjectiveResolution

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A : C} (P : ProjectiveResolution A)

/-- Positive-degree exactness is preserved by the source-resolution
opposite cochain construction. -/
lemma opCocomplex_exactAt_succ (n : ℕ) :
    P.complex.opCocomplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    P.complex.opCocomplex n (n + 1) (n + 2) (by simp) (by simp)]
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
      (by exact (Category.id_comp _).trans (Category.comp_id _).symm))
  exact (P.exact_succ n).op

/-- The zeroth cocycles of the opposite cochain complex identify with the
opposite of the object resolved by `P`. -/
noncomputable def opIsoCyclesZero :
    Opposite.op A ≅ P.complex.opCocomplex.cycles 0 := by
  let hker :
      IsLimit
        (KernelFork.ofι (P.π.f 0).op
          (show (P.π.f 0).op ≫ P.complex.opCocomplex.d 0 1 = 0 by
            change (P.π.f 0).op ≫ (P.complex.d 1 0).op = 0
            rw [← op_comp, P.complex_d_comp_π_f_zero, op_zero])) :=
    by
      change
        IsLimit
          (KernelFork.ofι (P.π.f 0).op
            (show (P.π.f 0).op ≫ (P.complex.d 1 0).op = 0 by
              rw [← op_comp, P.complex_d_comp_π_f_zero, op_zero]))
      exact
        CokernelCofork.IsColimit.ofπOp
          (P.π.f 0) P.complex_d_comp_π_f_zero
          P.isColimitCokernelCofork
  exact
    IsLimit.conePointUniqueUpToIso hker
      (P.complex.opCocomplex.cyclesIsKernel 0 1 (by simp))

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The additive equivalence between a morphism in the opposite category
and the corresponding reversed morphism in the original category. -/
def oppositeHomAddEquiv (X Y : C) :
    (Opposite.op Y ⟶ Opposite.op X) ≃+ (X ⟶ Y) where
  toFun f := f.unop
  invFun f := f.op
  left_inv f := Quiver.Hom.op_unop f
  right_inv f := Quiver.Hom.unop_op f
  map_add' f g := by simp

/-- The covariant Hom functor on the opposite category which is
contravariant Hom into `B` on the original category. -/
noncomputable abbrev contravariantHomFunctor (B : C) :
    Cᵒᵖ ⥤ AddCommGrpCat.{v} :=
  preadditiveCoyoneda.obj (Opposite.op (Opposite.op B))

end CategoryTheory

namespace ChainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Apply contravariant Hom into `B` degreewise to a chain complex.
The result is a cochain complex of additive commutative groups. -/
noncomputable abbrev contravariantHomCocomplex
    (K : ChainComplex C ℕ) (B : C) :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  ((CategoryTheory.contravariantHomFunctor B).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    K.opCocomplex

end ChainComplex

namespace CategoryTheory.ProjectiveResolution

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  {A B : C} (P : ProjectiveResolution A)

/-- The contravariant pointwise Hom cochain complex associated to a chain
complex resolving the source of Ext. -/
noncomputable abbrev contravariantHomCocomplex :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj
      (Opposite.op (Opposite.op B))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    P.complex.opCocomplex

/-- A cycle in the source-resolution Hom cochain complex. -/
noncomputable abbrev ContravariantHomCycle (n : ℕ) :=
  AddMonoidHom.ker
    ((P.contravariantHomCocomplex (B := B)).d n (n + 1)).hom

omit [HasExt C] in
@[simp]
lemma contravariantHomCocomplex_X (n : ℕ) :
    (P.contravariantHomCocomplex (B := B)).X n =
      AddCommGrpCat.of
        (Opposite.op B ⟶ Opposite.op (P.complex.X n)) :=
  rfl

omit [HasExt C] in
@[simp]
lemma contravariantHomCocomplex_d_apply
    {n m : ℕ}
    (f : Opposite.op B ⟶ Opposite.op (P.complex.X n)) :
    (P.contravariantHomCocomplex (B := B)).d n m f =
      f ≫ (P.complex.d m n).op :=
  rfl

/-- Send a cocycle in the contravariant Hom complex to the Ext class
represented by its unopposite morphism. -/
noncomputable def contravariantHomCycleToExt (n : ℕ) :
    P.ContravariantHomCycle (B := B) n →+
      Abelian.Ext.{v} A B n where
  toFun x :=
    P.extMk x.1.unop (n + 1) rfl (by
      apply Quiver.Hom.op_inj
      erw [op_zero, op_comp]
      change
        (P.contravariantHomCocomplex (B := B)).d n (n + 1) x.1 = 0
      exact x.2)
  map_zero' := by
    apply P.extMk_zero
  map_add' x y := by
    symm
    apply P.add_extMk

/-- The three-term window of the source-resolution Hom cochain complex
centered in positive degree `n + 1`. -/
noncomputable abbrev contravariantHomShortComplex (n : ℕ) :
    ShortComplex AddCommGrpCat.{v} :=
  (P.contravariantHomCocomplex (B := B)).sc' n (n + 1) (n + 2)

/-- The Ext-class map on the literal cycle group of the positive-degree
short-complex window. -/
noncomputable def contravariantHomShortComplexCycleToExt (n : ℕ) :
    AddMonoidHom.ker
        (P.contravariantHomShortComplex (B := B) n).g.hom →+
      Abelian.Ext.{v} A B (n + 1) where
  toFun x :=
    P.extMk x.1.unop (n + 2) (by omega) (by
      apply Quiver.Hom.op_inj
      erw [op_zero, op_comp]
      change
        (P.contravariantHomCocomplex (B := B)).d
          (n + 1) (n + 2) x.1 = 0
      exact x.2)
  map_zero' := by
    apply P.extMk_zero
  map_add' x y := by
    symm
    apply P.add_extMk

lemma contravariantHomShortComplexCycleToExt_surjective (n : ℕ) :
    Function.Surjective
      (P.contravariantHomShortComplexCycleToExt (B := B) n) := by
  intro α
  obtain ⟨f, hf, hα⟩ :=
    P.extMk_surjective α (n + 2) (by omega)
  let x :
      AddMonoidHom.ker
        (P.contravariantHomShortComplex (B := B) n).g.hom :=
    ⟨f.op, by
      change
        (P.contravariantHomCocomplex (B := B)).d
          (n + 1) (n + 2) f.op = 0
      rw [P.contravariantHomCocomplex_d_apply (B := B)]
      rw [← op_comp, hf, op_zero]
      rfl⟩
  exact ⟨x, hα⟩

/-- Boundaries in the positive-degree contravariant Hom complex are
exactly the cocycles representing zero in Ext. -/
lemma contravariantHomBoundaryRange_eq_ker_cycleToExt (n : ℕ) :
    AddMonoidHom.range
        (P.contravariantHomShortComplex (B := B) n).abToCycles =
      AddMonoidHom.ker
        (P.contravariantHomShortComplexCycleToExt
          (B := B) n) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    let fy : P.complex.X n ⟶ B := y.unop
    change
      P.extMk
          (P.complex.d (n + 1) n ≫ fy)
          (n + 2) (by omega)
          (by
            exact (Category.assoc _ _ _).symm.trans
              ((CategoryTheory.eq_whisker
                (P.complex.d_comp_d (n + 2) (n + 1) n) fy).trans
                  zero_comp)) = 0
    rw [P.extMk_eq_zero_iff (Y := B) (n := n + 1) _ _ _ _ n rfl]
    exact ⟨fy, rfl⟩
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    let fx : P.complex.X (n + 1) ⟶ B := x.1.unop
    change
      P.extMk fx (n + 2) (by omega) (by
        apply Quiver.Hom.op_inj
        erw [op_zero, op_comp]
        change
          (P.contravariantHomCocomplex (B := B)).d
            (n + 1) (n + 2) x.1 = 0
        exact x.2) = 0 at hx
    rw [P.extMk_eq_zero_iff (Y := B) (n := n + 1) _ _ _ _ n rfl] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨y.op, Subtype.ext ?_⟩
    apply Quiver.Hom.unop_inj
    exact hy

/-- The quotient description of positive-degree homology of the
contravariant Hom complex is Ext. -/
noncomputable def
    contravariantHomHomologyQuotientAddEquivExt (n : ℕ) :
    (AddMonoidHom.ker
          (P.contravariantHomShortComplex (B := B) n).g.hom ⧸
        AddMonoidHom.range
          (P.contravariantHomShortComplex (B := B) n).abToCycles) ≃+
      Abelian.Ext.{v} A B (n + 1) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (P.contravariantHomBoundaryRange_eq_ker_cycleToExt
        (B := B) n)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (P.contravariantHomShortComplexCycleToExt (B := B) n)
      (P.contravariantHomShortComplexCycleToExt_surjective
        (B := B) n))

/-- Positive-degree homology of the source-resolution Hom complex is
Ext. -/
noncomputable def contravariantHomShortComplexHomologyIsoExt
    (n : ℕ) :
    (P.contravariantHomShortComplex (B := B) n).homology ≅
      AddCommGrpCat.of (Abelian.Ext.{v} A B (n + 1)) :=
  (P.contravariantHomShortComplex (B := B) n).abHomologyIso ≪≫
    (P.contravariantHomHomologyQuotientAddEquivExt
      (B := B) n).toAddCommGrpIso

/-- Positive-degree homology of the whole source-resolution Hom complex
is Ext. -/
noncomputable def contravariantHomCocomplexHomologyIsoExt
    (n : ℕ) :
    (P.contravariantHomCocomplex (B := B)).homology (n + 1) ≅
      AddCommGrpCat.of (Abelian.Ext.{v} A B (n + 1)) :=
  (P.contravariantHomCocomplex (B := B)).homologyIsoSc'
      n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    P.contravariantHomShortComplexHomologyIsoExt (B := B) n

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  [HasProjectiveResolutions C] [HasInjectiveResolutions Cᵒᵖ]
  {A B : C}

/-- The right-derived functors of contravariant Hom, regarded as a
covariant functor on the opposite category, are the ordinary Ext groups
in the original category. -/
noncomputable def rightDerivedContravariantHomIsoExt (n : ℕ) :
    ((contravariantHomFunctor B).rightDerived n).obj (Opposite.op A) ≅
      AddCommGrpCat.of (Abelian.Ext.{v} A B n) := by
  cases n with
  | zero =>
      let eHom :
          (contravariantHomFunctor B).obj (Opposite.op A) ≅
            AddCommGrpCat.of (A ⟶ B) :=
        (oppositeHomAddEquiv A B).toAddCommGrpIso
      let eExt :
          AddCommGrpCat.of (A ⟶ B) ≅
            AddCommGrpCat.of (Abelian.Ext.{v} A B 0) :=
        (Abelian.Ext.addEquiv₀
          (X := A) (Y := B)).symm.toAddCommGrpIso
      exact
        (contravariantHomFunctor B).rightDerivedZeroIsoSelf.app
            (Opposite.op A) ≪≫
          eHom ≪≫ eExt
  | succ n =>
      let P := projectiveResolution A
      letI (q : ℕ) :
          Injective (P.complex.opCocomplex.X q) := by
        change Injective (Opposite.op (P.complex.X q))
        infer_instance
      exact
        (contravariantHomFunctor B).rightDerivedIsoOfAcyclicResolution
            P.complex.opCocomplex (Opposite.op A)
            P.opIsoCyclesZero P.opCocomplex_exactAt_succ (n + 1) ≪≫
          P.contravariantHomCocomplexHomologyIsoExt (B := B) n

/-- Ext-acyclicity in the source variable gives right acyclicity of the
corresponding opposite object for contravariant Hom. -/
theorem contravariantHom_isRightAcyclic_of_ext_subsingleton
    (X B : C)
    (h : ∀ n : ℕ, Subsingleton (Abelian.Ext.{v} X B (n + 1))) :
    (contravariantHomFunctor B).IsRightAcyclic (Opposite.op X) where
  vanish n := by
    letI : Subsingleton (Abelian.Ext.{v} X B (n + 1)) := h n
    exact
      IsZero.of_iso
        (AddCommGrpCat.isZero_of_subsingleton
          (AddCommGrpCat.of (Abelian.Ext.{v} X B (n + 1))))
        (rightDerivedContravariantHomIsoExt
          (A := X) (B := B) (n + 1))

/-- A source-side resolution whose terms are Ext-acyclic against `B`
computes `Ext A B`.  Equivalently, `Ext A B n` is the `n`-th homology
of the cochain complex obtained by applying contravariant Hom into `B`
to the chain resolution. -/
noncomputable def extIsoHomologyOfAcyclicCoresolution
    [CategoryWithHomology C]
    (K : ChainComplex C ℕ)
    (e : K.opcycles 0 ≅ A)
    (hexact : ∀ q, K.ExactAt (q + 1))
    (hacyclic :
      ∀ q m, Subsingleton (Abelian.Ext.{v} (K.X q) B (m + 1)))
    (n : ℕ) :
    AddCommGrpCat.of (Abelian.Ext.{v} A B n) ≅
      (K.contravariantHomCocomplex B).homology n := by
  letI (q : ℕ) :
      (contravariantHomFunctor B).IsRightAcyclic
        (K.opCocomplex.X q) := by
    change
      (contravariantHomFunctor B).IsRightAcyclic
        (Opposite.op (K.X q))
    exact
      contravariantHom_isRightAcyclic_of_ext_subsingleton
        (K.X q) B (hacyclic q)
  exact
    (rightDerivedContravariantHomIsoExt
      (A := A) (B := B) n).symm ≪≫
      (contravariantHomFunctor B).rightDerivedIsoOfAcyclicResolution
        K.opCocomplex (Opposite.op A)
        (K.opIsoCyclesZero e)
        (fun q => K.opCocomplex_exactAt_succ q (hexact q))
        n

end CategoryTheory
