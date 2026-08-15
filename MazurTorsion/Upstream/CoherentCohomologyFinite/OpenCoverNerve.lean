/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The augmented nerve of an open cover

For a family `U : ι → Opens T`, the value of its nerve on an open `V`
in simplicial degree `n` is the type of `(n + 1)`-tuples of members of
the family which contain `V`.  The augmentation remembers only that at
least one such member exists.

After applying the free-abelian-group functor, the augmentation is an
objectwise homotopy equivalence.  This is the presheaf-level exactness
input for the Čech resolution of the constant sheaf.
-/


open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverNerve

variable {T : TopCat.{u}} {ι : Type u}

section FunctorialAlternatingComplex

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- Taking the alternating face-map complex commutes with an additive
functor.  The comparison is the identity in every degree. -/
noncomputable def alternatingFaceMapComplexMapIso
    (F : C ⥤ D) [F.Additive]
    (X : SimplicialObject C) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj X) ≅
      AlgebraicTopology.AlternatingFaceMapComplex.obj
        (((SimplicialObject.whiskering C D).obj F).obj X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => Iso.refl _) (by
      rintro i j (rfl : j + 1 = i)
      simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d,
        AlgebraicTopology.AlternatingFaceMapComplex.obj,
        ChainComplex.of_d,
        AlgebraicTopology.AlternatingFaceMapComplex.objD,
        Functor.map_sum, Functor.map_zsmul]
      erw [Category.id_comp, Category.comp_id]
      rfl)

/-- The augmentation of the alternating face-map complex is compatible
with applying an additive functor. -/
noncomputable def arrowMkAugmentationMapIso
    [HasZeroObject C] [HasZeroObject D]
    (F : C ⥤ D) [F.Additive]
    (X : SimplicialObject.Augmented C) :
    Arrow.mk
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (AlgebraicTopology.AlternatingFaceMapComplex.ε.app X)) ≅
      Arrow.mk
        (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
          (((SimplicialObject.Augmented.whiskering C D).obj F).obj X)) :=
  Arrow.isoMk
    (alternatingFaceMapComplexMapIso F X.left)
    ((HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).app X.right) (by
        ext n
        cases n with
        | zero =>
            simp [alternatingFaceMapComplexMapIso,
              AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero,
              HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
            change _ =
              F.map
                  ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app X).f 0) ≫
                ((HomologicalComplex.singleMapHomologicalComplex F
                    (ComplexShape.down ℕ) 0).hom.app X.right).f 0
            rw [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
            erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self
              F (ComplexShape.down ℕ) 0 X.right]
            erw [Category.id_comp, Category.comp_id]
            simp [SimplicialObject.Augmented.whiskering,
              SimplicialObject.Augmented.whiskeringObj]
            exact Category.comp_id _
        | succ n =>
            simp [alternatingFaceMapComplexMapIso,
              AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_succ,
              HomologicalComplex.singleMapHomologicalComplex_hom_app_ne]
            change (0 : _) =
              F.map
                  ((AlgebraicTopology.AlternatingFaceMapComplex.ε.app X).f
                    (n + 1)) ≫
                ((HomologicalComplex.singleMapHomologicalComplex F
                    (ComplexShape.down ℕ) 0).hom.app X.right).f (n + 1)
            rw [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_succ,
              Functor.map_zero]
            exact zero_comp.symm)

end FunctorialAlternatingComplex

/-- The cover members which contain an open `V`. -/
def CoverIndex (U : ι → Opens T) (V : Opens T) :=
  {i : ι // V ≤ U i}

/-- Restrict a cover index along an inclusion of opens. -/
def CoverIndex.map {U : ι → Opens T} {V W : Opens T}
    (h : W ≤ V) : CoverIndex U V → CoverIndex U W :=
  fun i => ⟨i.1, h.trans i.2⟩

@[simp]
lemma CoverIndex.map_val {U : ι → Opens T} {V W : Opens T}
    (h : W ≤ V) (i : CoverIndex U V) :
    (CoverIndex.map h i).1 = i.1 :=
  rfl

/-- In simplicial degree `n`, tuples of cover members containing the
test open form a presheaf of types. -/
def simplexPresheaf (U : ι → Opens T)
    (n : SimplexCategoryᵒᵖ) :
    (Opens T)ᵒᵖ ⥤ Type u where
  obj V := ToType n.unop → CoverIndex U V.unop
  map {V W} f := ↾fun a k =>
    CoverIndex.map (U := U) (leOfHom f.unop) (a k)

/-- The simplicial presheaf underlying the nerve of an open family. -/
def nerve (U : ι → Opens T) :
    SimplicialObject ((Opens T)ᵒᵖ ⥤ Type u) where
  obj n := simplexPresheaf U n
  map f :=
    { app := fun _ => ↾fun a k => a (f.unop.toOrderHom k) }

/-- The support presheaf of an open family: it is a singleton on opens
contained in a cover member and empty otherwise. -/
def supportPresheaf (U : ι → Opens T) :
    (Opens T)ᵒᵖ ⥤ Type u where
  obj V :=
    {x : ULift.{u} PUnit // Nonempty (CoverIndex U V.unop)}
  map {V W} f := ↾fun x =>
    ⟨x.1, x.2.map
      (CoverIndex.map (U := U) (leOfHom f.unop))⟩

/-- The nerve augmented to the support presheaf. -/
def augmentedNerve (U : ι → Opens T) :
    SimplicialObject.Augmented ((Opens T)ᵒᵖ ⥤ Type u) where
  left := nerve U
  right := supportPresheaf U
  hom :=
    { app := fun _ =>
        { app := fun _ => ↾fun a =>
            ⟨ULift.up PUnit.unit, ⟨a 0⟩⟩ } }

/-- The explicit value of the augmented nerve at an open. -/
def evaluatedAugmentedNerve (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    SimplicialObject.Augmented (Type u) where
  left :=
    { obj := fun n => ToType n.unop → CoverIndex U V.unop
      map := fun f => ↾fun a k => a (f.unop.toOrderHom k) }
  right :=
    {x : ULift.{u} PUnit // Nonempty (CoverIndex U V.unop)}
  hom :=
    { app := fun _ => ↾fun a =>
        ⟨ULift.up PUnit.unit, ⟨a 0⟩⟩ }

/-- The explicit value agrees with categorical evaluation of the
presheaf-valued augmented nerve. -/
def evaluatedAugmentedNerveIso
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      ((evaluation (Opens T)ᵒᵖ (Type u)).obj V)).obj
        (augmentedNerve U) ≅
      evaluatedAugmentedNerve U V :=
  Iso.refl _

/-- If the test open lies in a cover member, prepending one fixed member
gives an extra degeneracy of the evaluated nerve. -/
def evaluatedExtraDegeneracyOfNonempty
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ)
    (h : Nonempty (CoverIndex U V.unop)) :
    (evaluatedAugmentedNerve U V).ExtraDegeneracy := by
  let i₀ : CoverIndex U V.unop := Classical.choice h
  change
    (SimplicialObject.Augmented.ExtraDegeneracy
      (evaluatedAugmentedNerve U V))
  refine
    { s' := ↾fun _ _ => i₀
      s := fun _ => ↾fun a k => Fin.cases i₀ a k
      s'_comp_ε := ?_
      s₀_comp_δ₁ := ?_
      s_comp_δ₀ := ?_
      s_comp_δ := ?_
      s_comp_σ := ?_ }
  · rfl
  · dsimp [evaluatedAugmentedNerve, augmentedNerve, nerve,
      simplexPresheaf, SimplicialObject.δ, SimplexCategory.δ]
    ext a k
    fin_cases k
    rfl
  · intro n
    dsimp [evaluatedAugmentedNerve, augmentedNerve, nerve,
      simplexPresheaf, SimplicialObject.δ, SimplexCategory.δ]
    ext a k
    rfl
  · intro n i
    dsimp [evaluatedAugmentedNerve, augmentedNerve, nerve,
      simplexPresheaf, SimplicialObject.δ, SimplexCategory.δ]
    ext a k
    cases k using Fin.cases <;> simp
  · intro n i
    dsimp [evaluatedAugmentedNerve, augmentedNerve, nerve,
      simplexPresheaf, SimplicialObject.σ, SimplexCategory.σ]
    ext a k
    cases k using Fin.cases <;> simp

/-- If the support at a test open is empty, every simplex type is empty,
so the evaluated nerve still has an extra degeneracy. -/
def evaluatedExtraDegeneracyOfIsEmpty
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ)
    (h : IsEmpty (CoverIndex U V.unop)) :
    (evaluatedAugmentedNerve U V).ExtraDegeneracy := by
  let emptySimplex (n : ℕ) :
      IsEmpty
        ((evaluatedAugmentedNerve U V).left.obj
          (Opposite.op (SimplexCategory.mk n))) :=
    ⟨fun a => h.false (a 0)⟩
  refine
    { s' := ↾fun x => False.elim (h.false (Classical.choice x.2))
      s := fun n => ↾fun a =>
        False.elim ((emptySimplex n).false a)
      s'_comp_ε := ?_
      s₀_comp_δ₁ := ?_
      s_comp_δ₀ := ?_
      s_comp_δ := ?_
      s_comp_σ := ?_ }
  · ext x
    exact False.elim (h.false (Classical.choice x.2))
  · ext a
    exact False.elim ((emptySimplex 0).false a)
  · intro n
    ext a
    exact False.elim ((emptySimplex n).false a)
  · intro n i
    ext a
    exact False.elim ((emptySimplex (n + 1)).false a)
  · intro n i
    ext a
    exact False.elim ((emptySimplex n).false a)

/-- Evaluation at every open has an extra degeneracy. -/
noncomputable def evaluatedExtraDegeneracy
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    (evaluatedAugmentedNerve U V).ExtraDegeneracy := by
  classical
  exact if h : Nonempty (CoverIndex U V.unop) then
    evaluatedExtraDegeneracyOfNonempty U V h
  else
    evaluatedExtraDegeneracyOfIsEmpty U V
      ⟨fun i => h ⟨i⟩⟩

/-- Apply the free-abelian-group functor objectwise to a presheaf of
types. -/
noncomputable def pointwiseFreeAbelianFunctor :
    ((Opens T)ᵒᵖ ⥤ Type u) ⥤
      ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringRight
    (Opens T)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free

/-- The augmented open-cover nerve after taking free abelian groups
objectwise. -/
noncomputable def freeAbelianAugmentedNerve
    (U : ι → Opens T) :
    SimplicialObject.Augmented
      ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ((SimplicialObject.Augmented.whiskering
    ((Opens T)ᵒᵖ ⥤ Type u)
    ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
      pointwiseFreeAbelianFunctor).obj
        (augmentedNerve U)

/-- The free-abelian augmented nerve evaluated at one open, written
without functor-category transports. -/
noncomputable def evaluatedFreeAbelianAugmentedNerve
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    SimplicialObject.Augmented AddCommGrpCat.{u} :=
  ((SimplicialObject.Augmented.whiskering
    (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free).obj
        (evaluatedAugmentedNerve U V)

/-- Categorical evaluation of the presheaf-valued free nerve is the
explicit evaluated free nerve. -/
noncomputable def evaluatedFreeAbelianAugmentedNerveIso
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      ((evaluation (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj V)).obj
        (freeAbelianAugmentedNerve U) ≅
      evaluatedFreeAbelianAugmentedNerve U V :=
  Iso.refl _

/-- The evaluated free-abelian nerve inherits the explicit extra
degeneracy. -/
noncomputable def evaluatedFreeAbelianExtraDegeneracy
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    (evaluatedFreeAbelianAugmentedNerve U V).ExtraDegeneracy :=
  (evaluatedExtraDegeneracy U V).map AddCommGrpCat.free

/-- The augmentation map of the free-abelian alternating Čech complex. -/
noncomputable def freeAbelianAugmentation
    (U : ι → Opens T) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj
        (freeAbelianAugmentedNerve U).left ⟶
      (ChainComplex.single₀
        ((Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
          (freeAbelianAugmentedNerve U).right :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (freeAbelianAugmentedNerve U)

/-- The free-abelian open-cover nerve is objectwise contractible onto its
support augmentation. -/
theorem freeAbelianAugmentation_quasiIso
    (U : ι → Opens T) :
    QuasiIso (freeAbelianAugmentation U) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro V
  let F :=
    (evaluation (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj V
  exact
    (quasiIso_iff_of_arrow_mk_iso
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (freeAbelianAugmentation U))
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (evaluatedFreeAbelianAugmentedNerve U V))
      (arrowMkAugmentationMapIso F
        (freeAbelianAugmentedNerve U))).2
      (evaluatedFreeAbelianExtraDegeneracy U V).homotopyEquiv.quasiIso_hom

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverNerve
