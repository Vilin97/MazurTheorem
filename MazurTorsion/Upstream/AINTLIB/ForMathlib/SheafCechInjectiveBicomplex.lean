/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechFlasqueHOne
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechZero

/-!
# The Cech bicomplex of an injective resolution

Apply mathlib's native Cech complex degreewise to an injective resolution. The resulting
bicomplex has exact augmented rows in degree zero and exact rows in degree one. These are
the horizontal inputs for the degree-one total-complex comparison.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

private theorem piMap_zero {β : Type u} (F G : β → AddCommGrpCat.{u}) :
    Limits.Pi.map (fun i ↦ (0 : F i ⟶ G i)) = 0 := by
  refine Pi.hom_ext _ _ fun i ↦ ?_
  rw [Pi.map_π, comp_zero, zero_comp]

/-- The native Cech-complex functor preserves zero morphisms. -/
noncomputable instance cechComplexFunctor_preservesZeroMorphisms :
    (cechComplexFunctor (A := AddCommGrpCat.{u}) U).PreservesZeroMorphisms := by
  constructor
  intro F G
  apply HomologicalComplex.Hom.ext
  funext p
  change Limits.Pi.map (fun _ ↦ 0) = 0
  apply piMap_zero

/-- The native Cech-complex functor restricted from presheaves to sheaves. -/
noncomputable def cechSheafComplexFunctor :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CochainComplex AddCommGrpCat.{u} ℕ :=
  CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    cechComplexFunctor U

noncomputable instance cechSheafComplexFunctor_preservesZeroMorphisms :
    (cechSheafComplexFunctor U).PreservesZeroMorphisms := by
  letI : (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    Functor.FullyFaithful.preservesZeroMorphisms _
      (CategoryTheory.fullyFaithfulSheafToPresheaf _ _)
  change (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    cechComplexFunctor U).PreservesZeroMorphisms
  infer_instance

/-- Applying the native Cech complex degreewise to a cochain complex of sheaves gives
a Cech bicomplex. Its outer index is the original cochain degree and its inner index is
the Cech degree. -/
noncomputable def cechBicomplex
    (K : CochainComplex
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  ((cechSheafComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K

/-- The Cech bicomplex associated to the chosen injective resolution of a sheaf. -/
noncomputable def cechInjectiveResolutionBicomplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  cechBicomplex U (injectiveResolution (toSiteSheaf F)).cocomplex

@[simp]
theorem cechInjectiveResolutionBicomplex_X
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    (cechInjectiveResolutionBicomplex U F).X q =
      (cechComplexFunctor U).obj
        ((injectiveResolution (toSiteSheaf F)).cocomplex.X q).obj :=
  rfl

@[simp]
theorem cechInjectiveResolutionBicomplex_d_f
    (F : Sheaf AddCommGrpCat.{u} X) (q q' p : ℕ) :
    ((cechInjectiveResolutionBicomplex U F).d q q').f p =
      ((cechComplexFunctor U).map
        ((injectiveResolution (toSiteSheaf F)).cocomplex.d q q').hom).f p :=
  rfl

/-- The augmented degree-zero row of the injective-resolution Cech bicomplex. -/
noncomputable def cechInjectiveResolutionRowZeroShortComplex
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    ShortComplex AddCommGrpCat.{u} :=
  cechZeroShortComplex
    ((injectiveResolution (toSiteSheaf F)).cocomplex.X q) U

/-- Every augmented row is exact at Cech degree zero by the sheaf condition. -/
theorem cechInjectiveResolutionBicomplex_row_zero_exact
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    (cechInjectiveResolutionRowZeroShortComplex (U := U) F q).Exact :=
  cechZeroShortComplex_exact _ _

/-- Every row of the injective-resolution Cech bicomplex is exact in degree one for
an actual open cover. -/
theorem cechInjectiveResolutionBicomplex_row_exactAt_one
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) (q : ℕ) :
    ((cechInjectiveResolutionBicomplex U F).X q).ExactAt 1 := by
  let I := injectiveResolution (toSiteSheaf F)
  letI : IsFlasque (I.cocomplex.X q) :=
    @IsFlasque.of_injective X (I.cocomplex.X q) (I.injective q)
  change ((cechComplexFunctor U).obj (I.cocomplex.X q).obj).ExactAt 1
  exact cechComplex_exactAt_one_of_isFlasque (I.cocomplex.X q) U hU

end
end TopCat.Sheaf
