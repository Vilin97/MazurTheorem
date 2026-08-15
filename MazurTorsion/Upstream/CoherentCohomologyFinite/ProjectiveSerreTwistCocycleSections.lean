/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistTripleOverlap

/-!
# Restricting Serre transition functions to a triple overlap

The former monolithic cocycle calculation is split here into one
factorization lemma and one section calculation for each of the three legs.
Every declaration therefore checks at the default heartbeat limit.
-/

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/-- The product coordinate defining the common triple overlap. -/
abbrev tripleCoordinate
    (i j l : Fin (d + 1)) :
    MvPolynomial (Fin (d + 1)) k :=
  coordinate k i * coordinate k j * coordinate k l

/-- The common projective basic open on a triple overlap. -/
abbrev tripleOpen (i j l : Fin (d + 1)) :
    (scheme k d).Opens :=
  Proj.basicOpen (homogeneousGrading k d)
    (tripleCoordinate k d i j l)

lemma tripleOpen_le_ij (i j l : Fin (d + 1)) :
    tripleOpen k d i j l ≤
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j) := by
  change
    Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j * coordinate k l) ≤
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
  rw [Proj.basicOpen_mul]
  exact inf_le_left

lemma tripleOpen_le_jk (i j l : Fin (d + 1)) :
    tripleOpen k d i j l ≤
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k j * coordinate k l) := by
  change
    Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j * coordinate k l) ≤
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k j * coordinate k l)
  rw [show
    coordinate k i * coordinate k j * coordinate k l =
      (coordinate k j * coordinate k l) * coordinate k i by ring,
    Proj.basicOpen_mul]
  exact inf_le_left

lemma tripleOpen_le_ik (i j l : Fin (d + 1)) :
    tripleOpen k d i j l ≤
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k l) := by
  change
    Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j * coordinate k l) ≤
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k l)
  rw [show
    coordinate k i * coordinate k j * coordinate k l =
      (coordinate k i * coordinate k l) * coordinate k j by ring,
    Proj.basicOpen_mul]
  exact inf_le_left

/-- `Xᵢ/Xⱼ` after localization at `XᵢXⱼXₖ`. -/
def tripleAwayIJ (i j l : Fin (d + 1)) :
    Away (homogeneousGrading k d) (tripleCoordinate k d i j l) :=
  awayMap (homogeneousGrading k d)
    (coordinate_mem_degreeOne k l)
    (show
      tripleCoordinate k d i j l =
        (coordinate k i * coordinate k j) * coordinate k l
      from rfl)
    (awayFraction k d i j)

/-- `Xⱼ/Xₖ` after localization at `XᵢXⱼXₖ`. -/
def tripleAwayJK (i j l : Fin (d + 1)) :
    Away (homogeneousGrading k d) (tripleCoordinate k d i j l) :=
  awayMap (homogeneousGrading k d)
    (coordinate_mem_degreeOne k i)
    (show
      tripleCoordinate k d i j l =
        (coordinate k j * coordinate k l) * coordinate k i by
      ring)
    (awayFraction k d j l)

/-- `Xᵢ/Xₖ` after localization at `XᵢXⱼXₖ`. -/
def tripleAwayIK (i j l : Fin (d + 1)) :
    Away (homogeneousGrading k d) (tripleCoordinate k d i j l) :=
  awayMap (homogeneousGrading k d)
    (coordinate_mem_degreeOne k j)
    (show
      tripleCoordinate k d i j l =
        (coordinate k i * coordinate k l) * coordinate k j by
      ring)
    (awayFraction k d i l)

lemma tripleAway_mul (i j l : Fin (d + 1)) :
    tripleAwayIJ k d i j l * tripleAwayJK k d i j l =
      tripleAwayIK k d i j l :=
  awayMap_awayFraction_cocycle k d i j l

/-- The localized `ij` ratio as a structure-sheaf section on the common
triple basic open. -/
def tripleSectionIJ (i j l : Fin (d + 1)) :
    Γ((tripleOpen k d i j l).toScheme, ⊤) :=
  (tripleOpen k d i j l).topIso.inv
    (Proj.awayToSection (homogeneousGrading k d)
      (tripleCoordinate k d i j l)
      (tripleAwayIJ k d i j l))

/-- The localized `jk` ratio on the common triple basic open. -/
def tripleSectionJK (i j l : Fin (d + 1)) :
    Γ((tripleOpen k d i j l).toScheme, ⊤) :=
  (tripleOpen k d i j l).topIso.inv
    (Proj.awayToSection (homogeneousGrading k d)
      (tripleCoordinate k d i j l)
      (tripleAwayJK k d i j l))

/-- The localized `ik` ratio on the common triple basic open. -/
def tripleSectionIK (i j l : Fin (d + 1)) :
    Γ((tripleOpen k d i j l).toScheme, ⊤) :=
  (tripleOpen k d i j l).topIso.inv
    (Proj.awayToSection (homogeneousGrading k d)
      (tripleCoordinate k d i j l)
      (tripleAwayIK k d i j l))

lemma appTop_factor_ij (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop (overlapHom k d i j) ≫
        Scheme.Hom.appTop
          (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l)) =
      Scheme.Hom.appTop
          ((scheme k d).homOfLE (tripleOpen_le_ij k d i j l)) ≫
        Scheme.Hom.appTop (commonHom k d i j l) := by
  calc
    _ = Scheme.Hom.appTop
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ overlapHom k d i j) :=
      (Scheme.Hom.comp_appTop _ _).symm
    _ = Scheme.Hom.appTop
        (commonHom k d i j l ≫
          (scheme k d).homOfLE (tripleOpen_le_ij k d i j l)) := congrArg
      Scheme.Hom.appTop
      (factor_ij k d i j l (tripleOpen_le_ij k d i j l))
    _ = _ := Scheme.Hom.comp_appTop _ _

lemma appTop_factor_jk (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop (overlapHom k d j l) ≫
        Scheme.Hom.appTop (jkBridge k d i j l) =
      Scheme.Hom.appTop
          ((scheme k d).homOfLE (tripleOpen_le_jk k d i j l)) ≫
        Scheme.Hom.appTop (commonHom k d i j l) := by
  calc
    _ = Scheme.Hom.appTop
        (jkBridge k d i j l ≫ overlapHom k d j l) :=
      (Scheme.Hom.comp_appTop _ _).symm
    _ = Scheme.Hom.appTop
        (commonHom k d i j l ≫
          (scheme k d).homOfLE (tripleOpen_le_jk k d i j l)) := congrArg
      Scheme.Hom.appTop
      (factor_jk k d i j l (tripleOpen_le_jk k d i j l))
    _ = _ := Scheme.Hom.comp_appTop _ _

lemma appTop_factor_ik (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop (overlapHom k d i l) ≫
        Scheme.Hom.appTop
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l)) =
      Scheme.Hom.appTop
          ((scheme k d).homOfLE (tripleOpen_le_ik k d i j l)) ≫
        Scheme.Hom.appTop (commonHom k d i j l) := by
  calc
    _ = Scheme.Hom.appTop
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l) ≫ overlapHom k d i l) :=
      (Scheme.Hom.comp_appTop _ _).symm
    _ = Scheme.Hom.appTop
        (commonHom k d i j l ≫
          (scheme k d).homOfLE (tripleOpen_le_ik k d i j l)) := congrArg
      Scheme.Hom.appTop
      (factor_ik k d i j l (tripleOpen_le_ik k d i j l))
    _ = _ := Scheme.Hom.comp_appTop _ _

/-- The `ij` overlap function restricts to the expected common fraction. -/
lemma transported_overlapUnit_ij (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        (overlapUnit k d i j).val =
      Scheme.Hom.appTop (commonHom k d i j l)
        (tripleSectionIJ k d i j l) := by
  rw [overlapUnit_val_eq]
  refine (congrArg
    (fun (f : _ ⟶ _) =>
      (ConcreteCategory.hom f)
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i * coordinate k j)
            (awayFraction k d i j))))
    (appTop_factor_ij k d i j l)).trans ?_
  simp only [ConcreteCategory.comp_apply]
  exact congrArg
    (fun z =>
      (ConcreteCategory.hom
        (Scheme.Hom.appTop (commonHom k d i j l))) z)
    (section_restrict k d
      (coordinate k i * coordinate k j) (coordinate k l)
      (coordinate_mem_degreeOne k l)
      (tripleCoordinate k d i j l) rfl
      (tripleOpen_le_ij k d i j l)
      (awayFraction k d i j))

/-- The `jk` overlap function restricts to the expected common fraction. -/
lemma transported_overlapUnit_jk (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop (jkBridge k d i j l)
        (overlapUnit k d j l).val =
      Scheme.Hom.appTop (commonHom k d i j l)
        (tripleSectionJK k d i j l) := by
  rw [overlapUnit_val_eq]
  refine (congrArg
    (fun (f : _ ⟶ _) =>
      (ConcreteCategory.hom f)
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k j * coordinate k l)).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k j * coordinate k l)
            (awayFraction k d j l))))
    (appTop_factor_jk k d i j l)).trans ?_
  simp only [ConcreteCategory.comp_apply]
  exact congrArg
    (fun z =>
      (ConcreteCategory.hom
        (Scheme.Hom.appTop (commonHom k d i j l))) z)
    (section_restrict k d
      (coordinate k j * coordinate k l) (coordinate k i)
      (coordinate_mem_degreeOne k i)
      (tripleCoordinate k d i j l)
      (by ring)
      (tripleOpen_le_jk k d i j l)
      (awayFraction k d j l))

/-- The `ik` overlap function restricts to the expected common fraction. -/
lemma transported_overlapUnit_ik (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l))
        (overlapUnit k d i l).val =
      Scheme.Hom.appTop (commonHom k d i j l)
        (tripleSectionIK k d i j l) := by
  rw [overlapUnit_val_eq]
  refine (congrArg
    (fun (f : _ ⟶ _) =>
      (ConcreteCategory.hom f)
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k l)).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i * coordinate k l)
            (awayFraction k d i l))))
    (appTop_factor_ik k d i j l)).trans ?_
  simp only [ConcreteCategory.comp_apply]
  exact congrArg
    (fun z =>
      (ConcreteCategory.hom
        (Scheme.Hom.appTop (commonHom k d i j l))) z)
    (section_restrict k d
      (coordinate k i * coordinate k l) (coordinate k j)
      (coordinate_mem_degreeOne k j)
      (tripleCoordinate k d i j l)
      (by ring)
      (tripleOpen_le_ik k d i j l)
      (awayFraction k d i l))

lemma tripleSection_mul (i j l : Fin (d + 1)) :
    tripleSectionIJ k d i j l * tripleSectionJK k d i j l =
      tripleSectionIK k d i j l := by
  rw [tripleSectionIJ, tripleSectionJK, tripleSectionIK,
    ← map_mul, ← map_mul, tripleAway_mul]

/-- The transition units satisfy the cocycle after transport to the common
triple overlap. -/
lemma overlapUnit_cocycle_transport (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        (overlapUnit k d i j).val *
      Scheme.Hom.appTop
        (jkBridge k d i j l)
        (overlapUnit k d j l).val =
      Scheme.Hom.appTop
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l))
        (overlapUnit k d i l).val := by
  rw [transported_overlapUnit_ij, transported_overlapUnit_jk,
    transported_overlapUnit_ik, ← map_mul, tripleSection_mul]

lemma overlapUnit_cocycle_transport_pow
    (m : ℕ) (i j l : Fin (d + 1)) :
    Scheme.Hom.appTop
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((overlapUnit k d i j ^ m).val) *
      Scheme.Hom.appTop
        (jkBridge k d i j l)
        ((overlapUnit k d j l ^ m).val) =
      Scheme.Hom.appTop
        (pullback.snd ((glueData k d).f i j)
          ((glueData k d).f i l))
        ((overlapUnit k d i l ^ m).val) := by
  simp only [Units.val_pow_eq_pow_val]
  calc
    _ = (Scheme.Hom.appTop
          (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l))
          (overlapUnit k d i j).val) ^ m *
        (Scheme.Hom.appTop (jkBridge k d i j l)
          (overlapUnit k d j l).val) ^ m := congrArg₂ (· * ·)
      (map_pow (Scheme.Hom.appTop
        (pullback.fst ((glueData k d).f i j)
          ((glueData k d).f i l))).hom _ m)
      (map_pow (Scheme.Hom.appTop (jkBridge k d i j l)).hom _ m)
    _ = (Scheme.Hom.appTop
          (pullback.fst ((glueData k d).f i j)
            ((glueData k d).f i l))
          (overlapUnit k d i j).val *
        Scheme.Hom.appTop (jkBridge k d i j l)
          (overlapUnit k d j l).val) ^ m := (mul_pow _ _ _).symm
    _ = (Scheme.Hom.appTop
          (pullback.snd ((glueData k d).f i j)
            ((glueData k d).f i l))
          (overlapUnit k d i l).val) ^ m := congrArg (· ^ m)
      (overlapUnit_cocycle_transport k d i j l)
    _ = _ := (map_pow (Scheme.Hom.appTop
      (pullback.snd ((glueData k d).f i j)
        ((glueData k d).f i l))).hom _ m).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
