/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceStandardCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafScalarPullback

/-!
# Transition functions for the Serre twist

On the standard chart `D₊(Xᵢ)` of projective space, `𝒪(m)` is free on the
local generator `Xᵢ^m`.  On an overlap the change of generator is
`(Xᵢ / Xⱼ)^m`.  This file constructs that unit in the degree-zero
homogeneous localization and the corresponding transition isomorphism of
unit module sheaves.
-/

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MvPolynomial
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- The standard coordinate charts, represented by their open subschemes. -/
noncomputable def cover : (scheme k d).OpenCover :=
  (scheme k d).openCoverOfIsOpenCover
    (standardChart k) (iSup_standardChart k d)

/-- The scheme glue datum associated to the standard coordinate cover. -/
abbrev glueData : Scheme.GlueData :=
  (cover k d).gluedCover

/-- A product of two homogeneous coordinates has degree two. -/
lemma coordinate_mul_mem_degreeTwo
    (i j : Fin (d + 1)) :
    coordinate k i * coordinate k j ∈
      homogeneousGrading k d 2 :=
  SetLike.mul_mem_graded
    (coordinate_mem_degreeOne k i)
    (coordinate_mem_degreeOne k j)

/-- The degree-zero fraction `Xᵢ / Xⱼ`, represented over the product
denominator `XᵢXⱼ`. -/
def awayFraction (i j : Fin (d + 1)) :
    Away (homogeneousGrading k d)
      (coordinate k i * coordinate k j) :=
  Away.mk _ (coordinate_mul_mem_degreeTwo k d i j) 1
    (coordinate k i * coordinate k i)
    (by simpa using coordinate_mul_mem_degreeTwo k d i i)

/-- The inverse fraction `Xⱼ / Xᵢ` in the same localization. -/
def awayFractionInv (i j : Fin (d + 1)) :
    Away (homogeneousGrading k d)
      (coordinate k i * coordinate k j) :=
  Away.mk _ (coordinate_mul_mem_degreeTwo k d i j) 1
    (coordinate k j * coordinate k j)
    (by simpa using coordinate_mul_mem_degreeTwo k d j j)

lemma awayFraction_mul_inv (i j : Fin (d + 1)) :
    awayFraction k d i j * awayFractionInv k d i j = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    awayFraction, awayFractionInv, Away.val_mk, Away.val_mk,
    Localization.mk_mul]
  have hnum :
      (coordinate k i * coordinate k i) *
          (coordinate k j * coordinate k j) =
        ((coordinate k i * coordinate k j) ^ 1 *
          (coordinate k i * coordinate k j) ^ 1 :
            MvPolynomial (Fin (d + 1)) k) := by
    ring
  rw [hnum]
  exact Localization.mk_self
    ((⟨(coordinate k i * coordinate k j) ^ 1, 1, rfl⟩ :
        Submonoid.powers
          (coordinate k i * coordinate k j :
            MvPolynomial (Fin (d + 1)) k)) *
      (⟨(coordinate k i * coordinate k j) ^ 1, 1, rfl⟩ :
        Submonoid.powers
          (coordinate k i * coordinate k j :
            MvPolynomial (Fin (d + 1)) k)))

/-- The overlap ratio `Xᵢ / Xⱼ` as a unit. -/
def awayUnit (i j : Fin (d + 1)) :
    (Away (homogeneousGrading k d)
      (coordinate k i * coordinate k j))ˣ where
  val := awayFraction k d i j
  inv := awayFractionInv k d i j
  val_inv := awayFraction_mul_inv k d i j
  inv_val := (mul_comm _ _).trans
    (awayFraction_mul_inv k d i j)

/-- The scheme-theoretic overlap maps into the product basic open
`D₊(XᵢXⱼ)`. -/
lemma range_overlap_le (i j : Fin (d + 1)) :
    Set.range
        (pullback.fst ((cover k d).f i) ((cover k d).f j) ≫
          (cover k d).f i).base ⊆
      Set.range
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).ι).base := by
  rw [Scheme.Opens.range_ι, Proj.basicOpen_mul]
  rintro _ ⟨v, rfl⟩
  refine ⟨?_, ?_⟩
  · have hx :
        ((pullback.fst ((cover k d).f i) ((cover k d).f j) ≫
          (cover k d).f i) v : scheme k d) ∈
          Set.range
            ((Proj.basicOpen (homogeneousGrading k d)
              (coordinate k i)).ι) := by
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (Scheme.Opens.range_ι _) ▸ hx
  · have h := congrArg
      (fun (φ : pullback ((cover k d).f i) ((cover k d).f j) ⟶
          scheme k d) => φ.base v)
      pullback.condition
    simp only at h
    rw [h]
    have hx :
        ((pullback.snd ((cover k d).f i) ((cover k d).f j) ≫
          (cover k d).f j) v : scheme k d) ∈
          Set.range
            ((Proj.basicOpen (homogeneousGrading k d)
              (coordinate k j)).ι) := by
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (Scheme.Opens.range_ι _) ▸ hx

/-- The canonical map from the scheme-theoretic overlap to the product
basic open. -/
def overlapHom (i j : Fin (d + 1)) :
    pullback ((cover k d).f i) ((cover k d).f j) ⟶
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)).toScheme :=
  IsOpenImmersion.lift
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)).ι
    (pullback.fst ((cover k d).f i) ((cover k d).f j) ≫
      (cover k d).f i)
    (range_overlap_le k d i j)

/-- Degree-zero homogeneous fractions as functions on the overlap. -/
def overlapRingHom (i j : Fin (d + 1)) :
    Away (homogeneousGrading k d)
        (coordinate k i * coordinate k j) →+*
      Γ(pullback ((cover k d).f i) ((cover k d).f j), ⊤) :=
  ((overlapHom k d i j).appTop.hom.comp
    ((Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)).topIso.inv.hom)).comp
    (Proj.awayToSection (homogeneousGrading k d)
      (coordinate k i * coordinate k j)).hom

/-- The transition ratio as a unit of functions on the scheme-theoretic
overlap. -/
def overlapUnit (i j : Fin (d + 1)) :
    Γ(pullback ((cover k d).f i) ((cover k d).f j), ⊤)ˣ :=
  Units.map (overlapRingHom k d i j).toMonoidHom
    (awayUnit k d i j)

lemma awayFraction_self (i : Fin (d + 1)) :
    awayFraction k d i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one, awayFraction, Away.val_mk]
  have hden :
      (⟨(coordinate k i * coordinate k i) ^ 1, 1, rfl⟩ :
          Submonoid.powers
            (coordinate k i * coordinate k i :
              MvPolynomial (Fin (d + 1)) k)) =
        ⟨coordinate k i * coordinate k i, 1, pow_one _⟩ :=
    Subtype.ext (pow_one _)
  rw [hden]
  exact Localization.mk_self_mk _ _

lemma awayUnit_self (i : Fin (d + 1)) :
    awayUnit k d i i = 1 :=
  Units.ext (awayFraction_self k d i)

lemma overlapUnit_self (i : Fin (d + 1)) :
    overlapUnit k d i i = 1 := by
  rw [overlapUnit, awayUnit_self, map_one]

/-- The rank-one transition from the `i`-chart generator to the `j`-chart
generator of `𝒪(m)`. -/
def transition (m : ℕ) (i j : Fin (d + 1)) :
    (Scheme.Modules.pullback ((glueData k d).f i j)).obj
        (SheafOfModules.unit ((glueData k d).U i).ringCatSheaf) ≅
      (Scheme.Modules.pullback
        ((glueData k d).t i j ≫ (glueData k d).f j i)).obj
        (SheafOfModules.unit ((glueData k d).U j).ringCatSheaf) :=
  pullbackUnitIso ((glueData k d).f i j) ≪≫
    unitIso ((overlapUnit k d i j) ^ m) ≪≫
    (pullbackUnitIso
      ((glueData k d).t i j ≫ (glueData k d).f j i)).symm

/-- The diagonal transition is the canonical equality transport. -/
lemma transition_self (m : ℕ) (i : Fin (d + 1)) :
    transition k d m i i =
      eqToIso (congrArg
        (fun f => (Scheme.Modules.pullback f).obj
          (SheafOfModules.unit ((glueData k d).U i).ringCatSheaf))
        (show
          (glueData k d).f i i =
            (glueData k d).t i i ≫ (glueData k d).f i i by
          rw [(glueData k d).t_id i, Category.id_comp])) := by
  have hmiddle :
      unitIso ((overlapUnit k d i i) ^ m) =
        Iso.refl (SheafOfModules.unit
          (pullback ((cover k d).f i)
            ((cover k d).f i)).ringCatSheaf) := by
    rw [overlapUnit_self, one_pow, unitIso_one]
  calc
    transition k d m i i =
        pullbackUnitIso ((glueData k d).f i i) ≪≫
          unitIso ((overlapUnit k d i i) ^ m) ≪≫
          (pullbackUnitIso
            ((glueData k d).t i i ≫
              (glueData k d).f i i)).symm := rfl
    _ = pullbackUnitIso ((glueData k d).f i i) ≪≫
          (pullbackUnitIso
            ((glueData k d).t i i ≫
              (glueData k d).f i i)).symm := by
      refine (congrArg
        (fun e =>
          pullbackUnitIso ((glueData k d).f i i) ≪≫ e ≪≫
            (pullbackUnitIso
              ((glueData k d).t i i ≫
                (glueData k d).f i i)).symm)
        hmiddle).trans ?_
      exact congrArg
        (fun e => pullbackUnitIso ((glueData k d).f i i) ≪≫ e)
        (Iso.refl_trans _)
    _ = eqToIso (congrArg
          (fun f => (Scheme.Modules.pullback f).obj
            (SheafOfModules.unit
              ((glueData k d).U i).ringCatSheaf))
          (show
            (glueData k d).f i i =
              (glueData k d).t i i ≫ (glueData k d).f i i by
            rw [(glueData k d).t_id i, Category.id_comp])) := by
      exact pullbackUnitIso_trans_symm_eqToIso
        (show
          (glueData k d).f i i =
            (glueData k d).t i i ≫ (glueData k d).f i i by
          rw [(glueData k d).t_id i, Category.id_comp])

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
