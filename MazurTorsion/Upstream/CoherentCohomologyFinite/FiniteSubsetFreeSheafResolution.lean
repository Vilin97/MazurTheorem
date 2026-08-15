/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafBoundary
import Mathlib.Topology.Sheaves.Abelian

/-!
# The normalized finite-subset free-sheaf resolution

For a finite ordered open family, this file constructs the canonical
augmentation from the normalized alternating complex of free module
sheaves on the intersections to the constant rank-one module sheaf.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- The constant presheaf with value the rank-one `R`-module. -/
abbrev constantRankOnePresheaf (T : TopCat.{u}) :
    (Opens T)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of R R)

/-- The constant rank-one sheaf. -/
abbrev constantRankOneSheaf (T : TopCat.{u}) :
    ModuleSheaf (R := R) T :=
  (constantSheaf (Opens.grothendieckTopology T)
    (ModuleCat.{u} R)).obj (ModuleCat.of R R)

/-- The free module presheaf represented by an open maps to the
constant rank-one presheaf by sending every represented generator to
`1`. -/
noncomputable def freeModulePresheafAugmentation (V : Opens T) :
    (yoneda.obj V ⋙ ModuleCat.free R) ⟶
      constantRankOnePresheaf (R := R) T :=
  (((ModuleCat.adj R).whiskerRight (Opens T)ᵒᵖ).homEquiv
      (yoneda.obj V)
      (constantRankOnePresheaf (R := R) T)).symm
    (yonedaEquiv.symm (1 : R))

lemma freeModulePresheafAugmentation_naturality
    {V W : Opens T} (i : V ⟶ W) :
    Functor.whiskerRight (yoneda.map i) (ModuleCat.free R) ≫
        freeModulePresheafAugmentation (R := R) W =
      freeModulePresheafAugmentation (R := R) V := by
  apply (((ModuleCat.adj R).whiskerRight
    (Opens T)ᵒᵖ).homEquiv
      (yoneda.obj V)
      (constantRankOnePresheaf (R := R) T)).injective
  unfold freeModulePresheafAugmentation
  rw [← Functor.whiskeringRight_obj_map]
  erw [Adjunction.homEquiv_naturality_left]
  simp only [Equiv.apply_symm_apply]
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality]
  rfl

/-- Sheafification of the canonical augmentation of a represented free
module presheaf. -/
noncomputable def freeModuleSheafAugmentation (V : Opens T) :
    freeModuleSheaf (R := R) V ⟶ constantRankOneSheaf (R := R) T :=
  (presheafToSheaf
    (Opens.grothendieckTopology T) (ModuleCat.{u} R)).map
      (freeModulePresheafAugmentation (R := R) V)

@[reassoc]
lemma freeModuleSheafAugmentation_naturality
    {V W : Opens T} (i : V ⟶ W) :
    freeModuleSheafMap (R := R) i ≫
        freeModuleSheafAugmentation (R := R) W =
      freeModuleSheafAugmentation (R := R) V := by
  let G := presheafToSheaf
    (Opens.grothendieckTopology T) (ModuleCat.{u} R)
  exact
    (G.map_comp
      (Functor.whiskerRight (yoneda.map i) (ModuleCat.free R))
      (freeModulePresheafAugmentation (R := R) W)).symm.trans
      (congrArg G.map
        (freeModulePresheafAugmentation_naturality
          (R := R) i))

omit [Fintype ι] in
/-- The two oriented vertices of a one-simplex have opposite signs. -/
lemma sum_insertionSign_erase_of_card_two
    (J : Finset ι) (hJ : J.card = 2) :
    ∑ j : ↥J,
        insertionSign (R := ℤ) (J.erase j.1) j.1 = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hJ
  let f : ι → ℤ := fun j =>
    insertionSign (R := ℤ) (({a, b} : Finset ι).erase j) j
  change (∑ j : ↥({a, b} : Finset ι), f j.1) = 0
  rw [Finset.univ_eq_attach, Finset.sum_attach,
    Finset.sum_pair hab]
  dsimp only [f]
  have hEraseA : ({a, b} : Finset ι).erase a = {b} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, hx | hx⟩
      · exact False.elim (by contradiction)
      · exact hx
    · intro hx
      subst x
      exact ⟨hab.symm, Or.inr rfl⟩
  have hEraseB : ({a, b} : Finset ι).erase b = {a} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, hx | hx⟩
      · exact hx
      · exact False.elim (by contradiction)
    · intro hx
      subst x
      exact ⟨hab, Or.inl rfl⟩
  rw [hEraseA, hEraseB]
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · rw [insertionSign, insertionSign,
      insertionPosition, insertionPosition,
      Finset.filter_singleton, Finset.filter_singleton,
      if_neg (not_lt_of_ge hab'.le), if_pos hab']
    norm_num
  · rw [insertionSign, insertionSign,
      insertionPosition, insertionPosition,
      Finset.filter_singleton, Finset.filter_singleton,
      if_pos hba', if_neg (not_lt_of_ge hba'.le)]
    norm_num

/-- The degree-zero augmentation of the normalized finite-subset
free-sheaf complex. -/
noncomputable def augmentation (U : ι → Opens T) :
    term (R := R) U 0 ⟶ constantRankOneSheaf (R := R) T :=
  Limits.Sigma.desc fun I : Simplex (ι := ι) 0 =>
    freeModuleSheafAugmentation (R := R) (intersection U I.1)

lemma simplexBoundary_comp_augmentation
    (U : ι → Opens T) (J : Simplex (ι := ι) 1) :
    simplexBoundary (R := R) U 0 J ≫ augmentation (R := R) U = 0 := by
  rw [simplexBoundary, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc,
    augmentation, Limits.Sigma.ι_desc]
  calc
    (∑ j : ↥J.1,
        insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
          (faceMap (R := R) U J j ≫
            freeModuleSheafAugmentation (R := R)
              (intersection U (J.erase j.1 j.2).1))) =
        ∑ j : ↥J.1,
          insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
            freeModuleSheafAugmentation (R := R)
              (intersection U J.1) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact freeModuleSheafAugmentation_naturality
        (R := R)
        (homOfLE
          (intersection_anti U
            (Finset.erase_subset j.1 J.1)))
    _ = (∑ j : ↥J.1,
          insertionSign (R := ℤ) (J.1.erase j.1) j.1) •
            freeModuleSheafAugmentation (R := R)
              (intersection U J.1) := by
      rw [Finset.sum_smul]
    _ = 0 := by
      rw [sum_insertionSign_erase_of_card_two J.1 J.2]
      simp

lemma boundary_zero_comp_augmentation (U : ι → Opens T) :
    boundary (R := R) U 0 ≫ augmentation (R := R) U = 0 := by
  apply Limits.Sigma.hom_ext
  intro J
  simp only [comp_zero]
  rw [← Category.assoc, boundary, Limits.Sigma.ι_desc]
  exact simplexBoundary_comp_augmentation U J

/-- The augmentation as a chain map to the constant rank-one sheaf
concentrated in degree zero. -/
noncomputable def augmentedComplexMap (U : ι → Opens T) :
    complex (R := R) U ⟶
      (ChainComplex.single₀ (ModuleSheaf (R := R) T)).obj
        (constantRankOneSheaf (R := R) T) :=
  (ChainComplex.toSingle₀Equiv
    (complex (R := R) U)
    (constantRankOneSheaf (R := R) T)).symm
      ⟨augmentation (R := R) U,
        boundary_zero_comp_augmentation (R := R) U⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
