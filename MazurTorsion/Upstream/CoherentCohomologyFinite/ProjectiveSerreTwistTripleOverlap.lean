/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistTransition

/-!
# Triple-overlap geometry for the Serre twist

The three ratios occurring in the cocycle are compared by factoring all
three overlap maps through `D₊(XᵢXⱼXₖ)`.  This file contains only that
geometric factorization and the elementary fraction identity.
-/

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MvPolynomial
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

variable (k : Type) [CommRing k] (d : ℕ)

private lemma comp_nested {A B C D E : Scheme}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (q : D ⟶ E) :
    (f ≫ (g ≫ h)) ≫ q = f ≫ (g ≫ h ≫ q) := by
  simp only [Category.assoc]

private lemma factor_through_mono {A B C D E : Scheme}
    (outer : A ⟶ B) (overlap : B ⟶ C) (inclusion : C ⟶ D)
    [Mono inclusion] (common : A ⟶ E) (restrict : E ⟶ C)
    (middle : B ⟶ D) (tripleInclusion : E ⟶ D) (target : A ⟶ D)
    (hoverlap : overlap ≫ inclusion = middle)
    (houter : outer ≫ middle = target)
    (hcommon : common ≫ tripleInclusion = target)
    (hrestrict : restrict ≫ inclusion = tripleInclusion) :
    outer ≫ overlap = common ≫ restrict := by
  rw [← cancel_mono inclusion]
  simp only [Category.assoc, hoverlap, houter, hrestrict, hcommon]

/-- The three localized coordinate ratios satisfy
`(Xᵢ/Xⱼ)(Xⱼ/Xₖ) = Xᵢ/Xₖ`. -/
lemma awayMap_awayFraction_cocycle
    (i j l : Fin (d + 1)) :
    awayMap (homogeneousGrading k d)
        (coordinate_mem_degreeOne k l)
        (show
          coordinate k i * coordinate k j * coordinate k l =
            (coordinate k i * coordinate k j) * coordinate k l
          from rfl)
        (awayFraction k d i j) *
      awayMap (homogeneousGrading k d)
        (coordinate_mem_degreeOne k i)
        (show
          coordinate k i * coordinate k j * coordinate k l =
            (coordinate k j * coordinate k l) * coordinate k i by
          rw [mul_assoc, mul_comm])
        (awayFraction k d j l) =
      awayMap (homogeneousGrading k d)
        (coordinate_mem_degreeOne k j)
        (show
          coordinate k i * coordinate k j * coordinate k l =
            (coordinate k i * coordinate k l) * coordinate k j by
          rw [mul_assoc, mul_comm (coordinate k j) (coordinate k l),
            ← mul_assoc])
        (awayFraction k d i l) := by
  rw [awayFraction, awayFraction, awayFraction,
    awayMap_mk, awayMap_mk, awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

lemma glueData_f (i j : Fin (d + 1)) :
    (glueData k d).f i j =
      pullback.fst ((cover k d).f i) ((cover k d).f j) := by
  exact Scheme.Cover.gluedCover_f (cover k d) i j

lemma glueData_t (i j : Fin (d + 1)) :
    (glueData k d).t i j =
      (pullbackSymmetry ((cover k d).f i)
        ((cover k d).f j)).hom := by
  exact Scheme.Cover.gluedCover_t (cover k d) i j

lemma cover_glue_condition (i j : Fin (d + 1)) :
    (glueData k d).t i j ≫ (glueData k d).f j i ≫
        (cover k d).f j =
      (glueData k d).f i j ≫ (cover k d).f i := by
  rw [glueData_t, glueData_f, glueData_f]
  calc
    _ = ((pullbackSymmetry ((cover k d).f i) ((cover k d).f j)).hom ≫
          pullback.fst ((cover k d).f j) ((cover k d).f i)) ≫
        (cover k d).f j := (Category.assoc _ _ _).symm
    _ = pullback.snd ((cover k d).f i) ((cover k d).f j) ≫
        (cover k d).f j := congrArg (fun q => q ≫ (cover k d).f j)
      (pullbackSymmetry_hom_comp_fst
        ((cover k d).f i) ((cover k d).f j))
    _ = _ := pullback.condition.symm

lemma chart_overlap_swap (i j : Fin (d + 1)) :
    (glueData k d).f i j ≫ (cover k d).f i =
      pullback.snd ((cover k d).f i) ((cover k d).f j) ≫
        (cover k d).f j := by
  rw [glueData_f]
  exact pullback.condition

lemma triple_range_le (i j l : Fin (d + 1)) :
    Set.range
        (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
          (glueData k d).f i j ≫ (cover k d).f i).base ⊆
      Set.range
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j * coordinate k l)).ι).base := by
  have hi :
      pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          (glueData k d).f i j ≫ (cover k d).f i =
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          (glueData k d).f i j) ≫ (cover k d).f i := by
    exact (Category.assoc _ _ _).symm
  have hj :
      pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          (glueData k d).f i j ≫ (cover k d).f i =
        (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
          pullback.snd ((cover k d).f i)
            ((cover k d).f j)) ≫ (cover k d).f j := by
    calc
      _ = pullback.fst ((glueData k d).f i j) ((glueData k d).f i l) ≫
          ((glueData k d).f i j ≫ (cover k d).f i) := rfl
      _ = pullback.fst ((glueData k d).f i j) ((glueData k d).f i l) ≫
          (pullback.snd ((cover k d).f i) ((cover k d).f j) ≫
            (cover k d).f j) := congrArg
        (fun q => pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ q) (chart_overlap_swap k d i j)
      _ = _ := (Category.assoc _ _ _).symm
  have hl :
      pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          (glueData k d).f i j ≫ (cover k d).f i =
        (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l) ≫
          pullback.snd ((cover k d).f i)
            ((cover k d).f l)) ≫ (cover k d).f l := by
    calc
      _ = (pullback.fst ((glueData k d).f i j) ((glueData k d).f i l) ≫
          (glueData k d).f i j) ≫ (cover k d).f i := hi
      _ = (pullback.snd ((glueData k d).f i j) ((glueData k d).f i l) ≫
          (glueData k d).f i l) ≫ (cover k d).f i := congrArg
        (fun q => q ≫ (cover k d).f i) pullback.condition
      _ = pullback.snd ((glueData k d).f i j) ((glueData k d).f i l) ≫
          ((glueData k d).f i l ≫ (cover k d).f i) := Category.assoc _ _ _
      _ = pullback.snd ((glueData k d).f i j) ((glueData k d).f i l) ≫
          (pullback.snd ((cover k d).f i) ((cover k d).f l) ≫
            (cover k d).f l) := congrArg
        (fun q => pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ q) (chart_overlap_swap k d i l)
      _ = _ := (Category.assoc _ _ _).symm
  have range_comp_subset {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
      Set.range (f ≫ g).base ⊆ Set.range g.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f.base x, rfl⟩
  rw [Scheme.Opens.range_ι, Proj.basicOpen_mul,
    Proj.basicOpen_mul, TopologicalSpace.Opens.coe_inf,
    TopologicalSpace.Opens.coe_inf]
  refine Set.subset_inter (Set.subset_inter ?_ ?_) ?_
  · rw [← Scheme.Opens.range_ι
      (Proj.basicOpen (homogeneousGrading k d) (coordinate k i)), hi]
    exact range_comp_subset _ _
  · rw [← Scheme.Opens.range_ι
      (Proj.basicOpen (homogeneousGrading k d) (coordinate k j)), hj]
    exact range_comp_subset _ _
  · rw [← Scheme.Opens.range_ι
      (Proj.basicOpen (homogeneousGrading k d) (coordinate k l)), hl]
    exact range_comp_subset _ _

/-- The common map from the triple overlap to
`D₊(XᵢXⱼXₖ)`. -/
def commonHom (i j l : Fin (d + 1)) :
    pullback ((glueData k d).f i j)
        ((glueData k d).f i l) ⟶
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j * coordinate k l)).toScheme :=
  IsOpenImmersion.lift
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j * coordinate k l)).ι
    (pullback.fst ((glueData k d).f i j)
        ((glueData k d).f i l) ≫
      (glueData k d).f i j ≫ (cover k d).f i)
    (triple_range_le k d i j l)

lemma commonHom_comp_ι (i j l : Fin (d + 1)) :
    commonHom k d i j l ≫
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j * coordinate k l)).ι =
      pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        (glueData k d).f i j ≫ (cover k d).f i :=
  IsOpenImmersion.lift_fac _ _ _

lemma overlapHom_comp_ι (i j : Fin (d + 1)) :
    overlapHom k d i j ≫
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).ι =
      (glueData k d).f i j ≫ (cover k d).f i := by
  rw [glueData_f]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The bridge from the `i`-based triple overlap to the `j,k` overlap. -/
noncomputable def jkBridge (i j l : Fin (d + 1)) :
    pullback ((glueData k d).f i j) ((glueData k d).f i l) ⟶
      pullback ((cover k d).f j) ((cover k d).f l) :=
  (glueData k d).t' i j l ≫
    pullback.fst ((glueData k d).f j l) ((glueData k d).f j i)

lemma jkBridge_comp_f (i j l : Fin (d + 1)) :
    jkBridge k d i j l ≫ (glueData k d).f j l =
      ((glueData k d).t' i j l ≫
        pullback.fst ((glueData k d).f j l)
          ((glueData k d).f j i)) ≫ (glueData k d).f j l :=
  rfl

lemma bridgeMiddle_jkBridge (i j l : Fin (d + 1)) :
    pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        ((glueData k d).t i j ≫ (glueData k d).f j i) =
      jkBridge k d i j l ≫ (glueData k d).f j l :=
  (bridgeMiddle (glueData k d) i j l).trans
    (jkBridge_comp_f k d i j l).symm

lemma jkBridge_comp_target (i j l : Fin (d + 1)) :
    jkBridge k d i j l ≫
        ((glueData k d).t j l ≫ (glueData k d).f l j) =
      ((glueData k d).t' i j l ≫
        pullback.fst ((glueData k d).f j l)
          ((glueData k d).f j i)) ≫
        ((glueData k d).t j l ≫ (glueData k d).f l j) :=
  rfl

lemma bridgeTarget_jkBridge (i j l : Fin (d + 1)) :
    jkBridge k d i j l ≫
        ((glueData k d).t j l ≫ (glueData k d).f l j) =
      pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        ((glueData k d).t i l ≫ (glueData k d).f l i) :=
  (jkBridge_comp_target k d i j l).trans
    (bridgeTarget (glueData k d) i j l)

lemma jk_inclusion (i j l : Fin (d + 1)) :
    jkBridge k d i j l ≫
        ((glueData k d).f j l ≫ (cover k d).f j) =
      pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        ((glueData k d).f i j ≫ (cover k d).f i) := by
  have hmiddle := bridgeMiddle_jkBridge k d i j l
  have hcover := cover_glue_condition k d i j
  calc
    jkBridge k d i j l ≫
          ((glueData k d).f j l ≫ (cover k d).f j) =
        (jkBridge k d i j l ≫ (glueData k d).f j l) ≫
          (cover k d).f j := (Category.assoc _ _ _).symm
    _ = (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          ((glueData k d).t i j ≫
            (glueData k d).f j i)) ≫ (cover k d).f j :=
      congrArg (fun q => q ≫ (cover k d).f j) hmiddle.symm
    _ = pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
          ((glueData k d).t i j ≫
          (glueData k d).f j i ≫ (cover k d).f j) := by
      exact comp_nested _ _ _ _
    _ = pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        (glueData k d).f i j ≫ (cover k d).f i :=
      congrArg
        (fun q => pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ q) hcover

lemma factor_ij (i j l : Fin (d + 1))
    (h :
      Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j * coordinate k l) ≤
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)) :
    pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ overlapHom k d i j =
      commonHom k d i j l ≫ (scheme k d).homOfLE h := by
  rw [← cancel_mono
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)).ι]
  calc
    _ = pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        (overlapHom k d i j ≫
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j)).ι) := Category.assoc _ _ _
    _ = pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        ((glueData k d).f i j ≫ (cover k d).f i) := congrArg
      (fun q => pullback.fst ((glueData k d).f i j)
        ((glueData k d).f i l) ≫ q) (overlapHom_comp_ι k d i j)
    _ = commonHom k d i j l ≫
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j * coordinate k l)).ι :=
      (commonHom_comp_ι k d i j l).symm
    _ = commonHom k d i j l ≫
        ((scheme k d).homOfLE h ≫
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j)).ι) := congrArg
      (fun q => commonHom k d i j l ≫ q)
      (Scheme.homOfLE_ι (X := scheme k d) h).symm
    _ = _ := (Category.assoc _ _ _).symm

lemma factor_ik (i j l : Fin (d + 1))
    (h :
      Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j * coordinate k l) ≤
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k l)) :
    pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ overlapHom k d i l =
      commonHom k d i j l ≫ (scheme k d).homOfLE h := by
  rw [← cancel_mono
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k l)).ι]
  calc
    _ = pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        (overlapHom k d i l ≫
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k l)).ι) := Category.assoc _ _ _
    _ = pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        ((glueData k d).f i l ≫ (cover k d).f i) := congrArg
      (fun q => pullback.snd ((glueData k d).f i j)
        ((glueData k d).f i l) ≫ q) (overlapHom_comp_ι k d i l)
    _ = (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ (glueData k d).f i l) ≫
        (cover k d).f i := (Category.assoc _ _ _).symm
    _ = (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ (glueData k d).f i j) ≫
        (cover k d).f i := congrArg
      (fun q => q ≫ (cover k d).f i) pullback.condition.symm
    _ = pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫
        ((glueData k d).f i j ≫ (cover k d).f i) := Category.assoc _ _ _
    _ = commonHom k d i j l ≫
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j * coordinate k l)).ι :=
      (commonHom_comp_ι k d i j l).symm
    _ = commonHom k d i j l ≫
        ((scheme k d).homOfLE h ≫
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k l)).ι) := congrArg
      (fun q => commonHom k d i j l ≫ q)
      (Scheme.homOfLE_ι (X := scheme k d) h).symm
    _ = _ := (Category.assoc _ _ _).symm

lemma factor_jk (i j l : Fin (d + 1))
    (h :
      Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j * coordinate k l) ≤
        Proj.basicOpen (homogeneousGrading k d)
          (coordinate k j * coordinate k l)) :
    jkBridge k d i j l ≫ overlapHom k d j l =
      commonHom k d i j l ≫ (scheme k d).homOfLE h := by
  exact factor_through_mono
    (jkBridge k d i j l)
    (overlapHom k d j l)
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k j * coordinate k l)).ι
    (commonHom k d i j l) ((scheme k d).homOfLE h)
    ((glueData k d).f j l ≫ (cover k d).f j)
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j * coordinate k l)).ι
    (pullback.fst ((glueData k d).f i j)
      ((glueData k d).f i l) ≫
      ((glueData k d).f i j ≫ (cover k d).f i))
    (overlapHom_comp_ι k d j l) (jk_inclusion k d i j l)
    (commonHom_comp_ι k d i j l)
    (Scheme.homOfLE_ι (X := scheme k d) h)

lemma topIso_inv_homOfLE_appTop
    {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) :
    V.topIso.inv ≫ (X.homOfLE h).appTop =
      X.presheaf.map (homOfLE h).op ≫ U.topIso.inv := by
  exact ((@Scheme.restrictFunctorΓ X).inv.naturality (homOfLE h).op).symm

/-- Restriction of an away section along
`D₊(xf*xg) ≤ D₊(xf)` is the homogeneous-localization away map. -/
lemma section_restrict {q : ℕ}
    (xf xg : MvPolynomial (Fin (d + 1)) k)
    (hg : xg ∈ homogeneousGrading k d q)
    (xt : MvPolynomial (Fin (d + 1)) k)
    (hxt : xt = xf * xg)
    (hopen :
      Proj.basicOpen (homogeneousGrading k d) xt ≤
        Proj.basicOpen (homogeneousGrading k d) xf)
    (a : Away (homogeneousGrading k d) xf) :
    ((scheme k d).homOfLE hopen).appTop
        ((Proj.basicOpen (homogeneousGrading k d) xf).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d) xf a)) =
      (Proj.basicOpen (homogeneousGrading k d) xt).topIso.inv
        (Proj.awayToSection (homogeneousGrading k d) xt
          (awayMap (homogeneousGrading k d) hg hxt a)) := by
  have hnat := congrArg
    (fun (φ : _ ⟶ _) =>
      (CommRingCat.Hom.hom φ)
        (Proj.awayToSection (homogeneousGrading k d) xf a))
    (topIso_inv_homOfLE_appTop
      (X := scheme k d) hopen)
  simp only [CommRingCat.comp_apply] at hnat
  rw [hnat]
  congr 1
  exact
    (congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f) a)
      (Proj.awayMap_awayToSection
        (𝒜 := homogeneousGrading k d) hg hxt)).symm

lemma overlapUnit_val_eq (i j : Fin (d + 1)) :
    (overlapUnit k d i j).val =
      (overlapHom k d i j).appTop
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i * coordinate k j)
            (awayFraction k d i j))) :=
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
