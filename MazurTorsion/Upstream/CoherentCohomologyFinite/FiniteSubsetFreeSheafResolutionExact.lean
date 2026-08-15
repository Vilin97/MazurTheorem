/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafResolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverNerve
import Mathlib.Algebra.Homology.Functor
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Exactness of the normalized finite-subset free-sheaf resolution

We model the normalized finite-subset presheaf complex as the normalized
chain complex of the nerve of the finite linear order of cover members
containing a test open.  A nonempty finite linear order has the nerve of a
standard simplex, so its augmented normalized chain complex is contractible.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

abbrev CoverIndex (U : ι → Opens T) (V : Opens T) :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverNerve.CoverIndex U V

local instance coverIndexLinearOrder (U : ι → Opens T) (V : Opens T) :
    LinearOrder (CoverIndex U V) :=
  LinearOrder.lift' (fun i => i.1) (fun _ _ h => Subtype.ext h)

local instance coverIndexCategory (U : ι → Opens T) (V : Opens T) :
    SmallCategory (CoverIndex U V) :=
  Preorder.smallCategory _

noncomputable local instance coverIndexFintype
    (U : ι → Opens T) (V : Opens T) :
    Fintype (CoverIndex U V) :=
  Fintype.ofInjective (fun i : CoverIndex U V => i.1)
    (fun _ _ h => Subtype.ext h)

/-- Restriction of the finite ordered set of available cover members. -/
def coverIndexRestriction (U : ι → Opens T)
    {V W : (Opens T)ᵒᵖ} (f : V ⟶ W) :
    CoverIndex U V.unop ⥤ CoverIndex U W.unop where
  obj i :=
    ⟨i.1, (leOfHom f.unop).trans i.2⟩
  map g := homOfLE (by
    exact leOfHom g)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma coverIndexRestriction_obj_val (U : ι → Opens T)
    {V W : (Opens T)ᵒᵖ} (f : V ⟶ W)
    (i : CoverIndex U V.unop) :
    ((coverIndexRestriction U f).obj i).1 = i.1 :=
  rfl

/-- The nerve of the ordered set of cover members containing the test
open, functorial under restriction of the test open. -/
def orderedCoverNerveFunctor (U : ι → Opens T) :
    (Opens T)ᵒᵖ ⥤ SSet.{u} where
  obj V := CategoryTheory.nerve (CoverIndex U V.unop)
  map f := CategoryTheory.nerveMap (coverIndexRestriction U f)
  map_id V := by
    ext n x j
    rfl
  map_comp f g := by
    ext n x j
    rfl

/-- The pointwise normalized chain complex of the ordered cover nerve. -/
noncomputable def orderedCoverNormalizedChainFunctor
    (U : ι → Opens T) :
    (Opens T)ᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  orderedCoverNerveFunctor U ⋙
    SSet.normalizedChainComplexFunctorObj (ModuleCat.of R R)

/-- The inclusion of normalized chains is natural.  Mathlib packages
the reverse projection as a natural transformation; this is the
corresponding statement for the split inclusion. -/
lemma normalizedChainComplexMap_fromNormalizedChainComplex
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.normalizedChainComplexMap f (ModuleCat.of R R) ≫
        Y.fromNormalizedChainComplex (ModuleCat.of R R) =
      X.fromNormalizedChainComplex (ModuleCat.of R R) ≫
        SSet.chainComplexMap f (ModuleCat.of R R) := by
  have hcomm :
      SSet.chainComplexMap f (ModuleCat.of R R) ≫
          Y.toNormalizedChainComplex (ModuleCat.of R R) ≫
          Y.fromNormalizedChainComplex (ModuleCat.of R R) =
        X.toNormalizedChainComplex (ModuleCat.of R R) ≫
          X.fromNormalizedChainComplex (ModuleCat.of R R) ≫
          SSet.chainComplexMap f (ModuleCat.of R R) := by
    rw [SSet.toNormalizedChainComplex_fromNormalizedChainComplex
      Y (ModuleCat.of R R)]
    rw [SSet.toNormalizedChainComplex_fromNormalizedChainComplex_assoc
      X (ModuleCat.of R R)]
    exact SSet.chainComplexMap_PInfty
      (X := X) (Y := Y) f (ModuleCat.of R R)
  rw [SSet.normalizedChainComplexMap]
  simp only [Category.assoc]
  rw [hcomm]
  simp only [← Category.assoc,
    SSet.fromNormalizedChainComplex_toNormalizedChainComplex,
    Category.id_comp]

/-- Natural inclusion of normalized chains into the unnormalized
simplicial chain complex. -/
noncomputable def fromNormalizedChainComplexNatTrans :
    SSet.normalizedChainComplexFunctorObj (ModuleCat.of R R) ⟶
      (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R) where
  app X := X.fromNormalizedChainComplex (ModuleCat.of R R)
  naturality _ _ f :=
    normalizedChainComplexMap_fromNormalizedChainComplex
      (R := R) f

universe vD uD vC uC

/-- Turn a functor to chain complexes into a chain complex in the
functor category. -/
def chainComplexInFunctorCategory
    {D : Type uD} {C : Type uC}
    [Category.{vD} D] [Category.{vC} C]
    [HasZeroMorphisms C]
    (K : D ⥤ ChainComplex C ℕ) :
    ChainComplex (D ⥤ C) ℕ where
  X q :=
    { obj := fun d => (K.obj d).X q
      map := fun f => (K.map f).f q
      map_id := fun d => by
        rw [K.map_id]
        rfl
      map_comp := fun f g => by
        rw [K.map_comp]
        rfl }
  d i j :=
    { app := fun d => (K.obj d).d i j
      naturality := fun d e f => by
        exact (K.map f).comm i j }
  shape i j hij := by
    ext d
    exact (K.obj d).shape i j hij
  d_comp_d' i j k hij hjk := by
    ext d
    exact (K.obj d).d_comp_d i j k

/-- Turn a natural transformation of complex-valued functors into a
morphism of complexes in the functor category. -/
def chainMapInFunctorCategory
    {D : Type uD} {C : Type uC}
    [Category.{vD} D] [Category.{vC} C]
    [HasZeroMorphisms C]
    {K L : D ⥤ ChainComplex C ℕ} (φ : K ⟶ L) :
    chainComplexInFunctorCategory K ⟶
      chainComplexInFunctorCategory L where
  f q :=
    { app := fun d => (φ.app d).f q
      naturality := fun d e f => by
        exact HomologicalComplex.congr_hom
          (φ.naturality f) q }
  comm' i j _ := by
    ext d
    exact (φ.app d).comm i j

/-- The normalized ordered-cover complex as a complex of module
presheaves. -/
noncomputable def orderedCoverNormalizedPresheafComplex
    (U : ι → Opens T) :
    ChainComplex ((Opens T)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  chainComplexInFunctorCategory
    (orderedCoverNormalizedChainFunctor (R := R) U)

/-- The ordered cover nerve at one open, augmented to the support of
the cover at that open. -/
def evaluatedOrderedAugmentedNerve
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    SimplicialObject.Augmented (Type u) where
  left := CategoryTheory.nerve (CoverIndex U V.unop)
  right :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverNerve.supportPresheaf U |>.obj V
  hom :=
    { app := fun _ => ↾fun x =>
        ⟨ULift.up PUnit.unit, ⟨x.obj 0⟩⟩
      naturality := fun _ _ _ => by
        ext x
        subsingleton }

/-- The augmented ordered nerves form a functor of the test open. -/
def orderedCoverAugmentedNerveFunctor
    (U : ι → Opens T) :
    (Opens T)ᵒᵖ ⥤ SimplicialObject.Augmented (Type u) where
  obj V := evaluatedOrderedAugmentedNerve U V
  map {V W} f :=
    { left := CategoryTheory.nerveMap (coverIndexRestriction U f)
      right :=
        (MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverNerve.supportPresheaf U).map f
      w := by
        ext n x
        subsingleton }
  map_id V := by
    apply SimplicialObject.Augmented.hom_ext
    · ext n x j
      rfl
    · ext x
      rfl
  map_comp f g := by
    apply SimplicialObject.Augmented.hom_ext
    · ext n x j
      rfl
    · ext x
      rfl

/-- Apply the module coproduct functor to the augmented ordered nerve,
functorially in the test open. -/
noncomputable def orderedCoverModuleAugmentedNerveFunctor
    (U : ι → Opens T) :
    (Opens T)ᵒᵖ ⥤
      SimplicialObject.Augmented (ModuleCat.{u} R) :=
  orderedCoverAugmentedNerveFunctor U ⋙
    (SimplicialObject.Augmented.whiskering
      (Type u) (ModuleCat.{u} R)).obj
        (sigmaConst.obj (ModuleCat.of R R))

/-- The target of the ordered-cover augmentation, as a functor to
chain complexes. -/
noncomputable def orderedCoverSupportSingleFunctor
    (U : ι → Opens T) :
    (Opens T)ᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  orderedCoverModuleAugmentedNerveFunctor (R := R) U ⋙
    SimplicialObject.Augmented.point ⋙
      ChainComplex.single₀ (ModuleCat.{u} R)

/-- The pointwise normalized augmentations assemble naturally over all
test opens. -/
noncomputable def orderedCoverNormalizedAugmentationNatTrans
    (U : ι → Opens T) :
    orderedCoverNormalizedChainFunctor (R := R) U ⟶
      orderedCoverSupportSingleFunctor (R := R) U :=
  Functor.whiskerLeft (orderedCoverNerveFunctor U)
      (fromNormalizedChainComplexNatTrans (R := R)) ≫
    Functor.whiskerLeft
      (orderedCoverModuleAugmentedNerveFunctor (R := R) U)
      AlgebraicTopology.AlternatingFaceMapComplex.ε

/-- The support module presheaf of the cover. -/
noncomputable def orderedCoverSupportModulePresheaf
    (U : ι → Opens T) :
    (Opens T)ᵒᵖ ⥤ ModuleCat.{u} R :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverNerve.supportPresheaf U ⋙
    sigmaConst.obj (ModuleCat.of R R)

/-- The support presheaf, concentrated in chain degree zero. -/
noncomputable def orderedCoverSupportSingleComplex
    (U : ι → Opens T) :
    ChainComplex ((Opens T)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  chainComplexInFunctorCategory
    (orderedCoverSupportSingleFunctor (R := R) U)

/-- Currying pointwise degree-zero complexes agrees with the ordinary
degree-zero complex of the support presheaf. -/
noncomputable def orderedCoverSupportSingleComplexIso
    (U : ι → Opens T) :
    orderedCoverSupportSingleComplex (R := R) U ≅
      (ChainComplex.single₀
        ((Opens T)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
          (orderedCoverSupportModulePresheaf (R := R) U) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q => ?_) ?_
  · cases q with
    | zero =>
        exact NatIso.ofComponents (fun _ => Iso.refl _)
          (fun _ => by rfl)
    | succ q =>
        exact NatIso.ofComponents
          (fun V =>
            (HomologicalComplex.isZero_single_obj_X
              (ComplexShape.down ℕ) 0
              ((orderedCoverSupportModulePresheaf
                (R := R) U).obj V)
              (q + 1) (Nat.succ_ne_zero q)).iso
            ((HomologicalComplex.isZero_single_obj_X
              (ComplexShape.down ℕ) 0
              (orderedCoverSupportModulePresheaf (R := R) U)
              (q + 1) (Nat.succ_ne_zero q)).obj V))
          (fun {V W} f => by
            exact
              (HomologicalComplex.isZero_single_obj_X
                (ComplexShape.down ℕ) 0
                ((orderedCoverSupportModulePresheaf
                  (R := R) U).obj V)
                (q + 1) (Nat.succ_ne_zero q)).eq_of_src _ _)
  · intro i j hij
    change j + 1 = i at hij
    subst i
    apply NatTrans.ext
    funext V
    exact
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0
        ((orderedCoverSupportModulePresheaf (R := R) U).obj V)
        (j + 1) (Nat.succ_ne_zero j)).eq_of_src _ _

/-- The natural normalized augmentation as a morphism of complexes of
module presheaves. -/
noncomputable def orderedCoverNormalizedPresheafAugmentation
    (U : ι → Opens T) :
    orderedCoverNormalizedPresheafComplex (R := R) U ⟶
      orderedCoverSupportSingleComplex (R := R) U :=
  chainMapInFunctorCategory
    (orderedCoverNormalizedAugmentationNatTrans (R := R) U)

/-- When the support is nonempty, the evaluated ordered nerve is an
augmented standard simplex. -/
noncomputable def evaluatedOrderedAugmentedNerveIsoOfNonempty
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ)
    (h : Nonempty (CoverIndex U V.unop)) :
    SSet.Augmented.stdSimplex.obj
        (SimplexCategory.mk
          (Fintype.card (CoverIndex U V.unop) - 1)) ≅
      evaluatedOrderedAugmentedNerve U V := by
  let α := CoverIndex U V.unop
  have hcard : Fintype.card α =
      (Fintype.card α - 1) + 1 := by
    have : 0 < Fintype.card α := Fintype.card_pos_iff.mpr h
    omega
  let e : α ≃o Fin ((Fintype.card α - 1) + 1) :=
    (monoEquivOfFin α hcard).symm
  let leftIso :
      (SSet.Augmented.stdSimplex.obj
          (SimplexCategory.mk (Fintype.card α - 1))).left ≅
        (evaluatedOrderedAugmentedNerve U V).left :=
    SSet.stdSimplex.isoOfRepresentableBy
      (CategoryTheory.nerve.representableBy α e)
  let supportIso :
      (PUnit : Type u) ≅
        (MazurTorsion.AlgebraicGeometry.CoherentCohomology.OpenCoverNerve.supportPresheaf U).obj V :=
    Iso.mk
      (↾fun _ => ⟨ULift.up PUnit.unit, h⟩)
      (↾fun _ => PUnit.unit)
      (by ext x)
      (by
        ext x
        apply Subtype.ext
        cases x.1
        rfl)
  let rightIso :
      (SSet.Augmented.stdSimplex.obj
          (SimplexCategory.mk (Fintype.card α - 1))).right ≅
        (evaluatedOrderedAugmentedNerve U V).right :=
    Types.terminalIso.trans supportIso
  exact CategoryTheory.Comma.isoMk leftIso rightIso (by
    ext n x
    subsingleton)

/-- A nonempty evaluated ordered nerve inherits the standard simplex's
extra degeneracy. -/
noncomputable def evaluatedOrderedExtraDegeneracyOfNonempty
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ)
    (h : Nonempty (CoverIndex U V.unop)) :
    (evaluatedOrderedAugmentedNerve U V).ExtraDegeneracy :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso
    (evaluatedOrderedAugmentedNerveIsoOfNonempty U V h)
    (SSet.Augmented.StandardSimplex.extraDegeneracy
      (SimplexCategory.mk
        (Fintype.card (CoverIndex U V.unop) - 1)))

/-- If no cover member contains the test open, both the support and all
simplices of the ordered nerve are empty. -/
def evaluatedOrderedExtraDegeneracyOfIsEmpty
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ)
    (h : IsEmpty (CoverIndex U V.unop)) :
    (evaluatedOrderedAugmentedNerve U V).ExtraDegeneracy := by
  let emptySimplex (n : ℕ) :
      IsEmpty
        ((evaluatedOrderedAugmentedNerve U V).left.obj
          (Opposite.op (SimplexCategory.mk n))) :=
    ⟨fun x => h.false (x.obj 0)⟩
  refine
    { s' := ↾fun x => False.elim (h.false (Classical.choice x.2))
      s := fun n => ↾fun x => False.elim ((emptySimplex n).false x)
      s'_comp_ε := ?_
      s₀_comp_δ₁ := ?_
      s_comp_δ₀ := ?_
      s_comp_δ := ?_
      s_comp_σ := ?_ }
  · ext x
    exact False.elim (h.false (Classical.choice x.2))
  · ext x
    exact False.elim ((emptySimplex 0).false x)
  · intro n
    ext x
    exact False.elim ((emptySimplex n).false x)
  · intro n i
    ext x
    exact False.elim ((emptySimplex (n + 1)).false x)
  · intro n i
    ext x
    exact False.elim ((emptySimplex n).false x)

/-- Every evaluated ordered cover nerve has an extra degeneracy. -/
noncomputable def evaluatedOrderedExtraDegeneracy
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    (evaluatedOrderedAugmentedNerve U V).ExtraDegeneracy := by
  classical
  exact if h : Nonempty (CoverIndex U V.unop) then
    evaluatedOrderedExtraDegeneracyOfNonempty U V h
  else
    evaluatedOrderedExtraDegeneracyOfIsEmpty U V
      ⟨fun i => h ⟨i⟩⟩

/-- Apply the coproduct-of-copies functor to the evaluated augmented
ordered nerve. -/
noncomputable def evaluatedOrderedModuleAugmentedNerve
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    SimplicialObject.Augmented (ModuleCat.{u} R) :=
  ((SimplicialObject.Augmented.whiskering
    (Type u) (ModuleCat.{u} R)).obj
      (sigmaConst.obj (ModuleCat.of R R))).obj
        (evaluatedOrderedAugmentedNerve U V)

/-- The module-valued ordered nerve retains the pointwise contraction. -/
noncomputable def evaluatedOrderedModuleExtraDegeneracy
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    (evaluatedOrderedModuleAugmentedNerve (R := R) U V).ExtraDegeneracy :=
  (evaluatedOrderedExtraDegeneracy U V).map
    (sigmaConst.obj (ModuleCat.of R R))

/-- The normalized augmentation of the ordered cover nerve at one test
open. -/
noncomputable def evaluatedOrderedNormalizedAugmentation
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    (CategoryTheory.nerve (CoverIndex U V.unop)).normalizedChainComplex
        (ModuleCat.of R R) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} R)).obj
        (evaluatedOrderedModuleAugmentedNerve (R := R) U V).right :=
  (CategoryTheory.nerve
      (CoverIndex U V.unop)).fromNormalizedChainComplex
        (ModuleCat.of R R) ≫
    AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (evaluatedOrderedModuleAugmentedNerve (R := R) U V)

/-- The normalized augmentation is a quasi-isomorphism at every test
open. -/
theorem evaluatedOrderedNormalizedAugmentation_quasiIso
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) :
    QuasiIso
      (evaluatedOrderedNormalizedAugmentation (R := R) U V) := by
  let hε : QuasiIso
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (evaluatedOrderedModuleAugmentedNerve (R := R) U V)) :=
    (evaluatedOrderedModuleExtraDegeneracy
      (R := R) U V).homotopyEquiv.quasiIso_hom
  dsimp [evaluatedOrderedNormalizedAugmentation]
  exact quasiIso_comp _ _ (hφ' := hε)

/-- The normalized ordered-cover augmentation is already a
quasi-isomorphism before sheafification. -/
theorem orderedCoverNormalizedPresheafAugmentation_quasiIso
    (U : ι → Opens T) :
    QuasiIso
      (orderedCoverNormalizedPresheafAugmentation (R := R) U) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro V
  change QuasiIso
    ((orderedCoverNormalizedAugmentationNatTrans
      (R := R) U).app V)
  exact evaluatedOrderedNormalizedAugmentation_quasiIso
    (R := R) U V

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
