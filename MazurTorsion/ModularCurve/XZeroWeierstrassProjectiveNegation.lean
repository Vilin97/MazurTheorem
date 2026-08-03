/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveCubic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Negation on the reduced projective Weierstrass cubic

This file realizes the homogeneous coordinate substitution
`[X : Y : Z] ↦ [X : -Y - a₁X - a₃Z : Z]` as an involutive automorphism of the
projective plane.  The substitution fixes the homogeneous Weierstrass equation, so it restricts
to an involutive automorphism of the concrete reduced projective cubic.

The construction is checked over the ground field.  On the affine cover transported by the
graded substitution, the degree-zero localization maps commute with coefficient constants; this
proves that ambient negation commutes with the projective-plane structure morphism.  Consequently
the restricted involution is packaged as an automorphism of the cubic in the slice over `Spec K`.
This is scheme-level group geometry, but no addition law or group-object structure is claimed.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped WeierstrassCurve.Projective

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The homogeneous coordinate expressions defining Weierstrass negation. -/
noncomputable def negationCoordinates (W : WeierstrassCurve K) :
    Fin 3 → MvPolynomial (Fin 3) K :=
  (W.map (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)).toProjective.neg
    (fun i ↦ MvPolynomial.X i)

/-- The coordinate-ring substitution defining Weierstrass negation. -/
noncomputable def negationRingHom (W : WeierstrassCurve K) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
  (MvPolynomial.aeval (negationCoordinates W)).toRingHom

@[simp]
theorem negationRingHom_X (W : WeierstrassCurve K) (i : Fin 3) :
    negationRingHom W (MvPolynomial.X i) = negationCoordinates W i := by
  simp [negationRingHom]

@[simp]
theorem negationRingHom_C (W : WeierstrassCurve K) (a : K) :
    negationRingHom W (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [negationRingHom]

theorem negationCoordinates_isHomogeneous (W : WeierstrassCurve K) (i : Fin 3) :
    (negationCoordinates W i).IsHomogeneous 1 := by
  fin_cases i
  · simpa [negationCoordinates, WeierstrassCurve.Projective.neg] using
      MvPolynomial.isHomogeneous_X K 0
  · simpa [negationCoordinates, WeierstrassCurve.Projective.neg,
      WeierstrassCurve.Projective.negY] using
      (((MvPolynomial.isHomogeneous_X K 1).neg.sub
        ((MvPolynomial.isHomogeneous_X K 0).C_mul W.a₁)).sub
          ((MvPolynomial.isHomogeneous_X K 2).C_mul W.a₃))
  · simpa [negationCoordinates, WeierstrassCurve.Projective.neg] using
      MvPolynomial.isHomogeneous_X K 2

/-- Weierstrass negation as a degree-preserving endomorphism of the homogeneous coordinate
ring. -/
noncomputable def negationGraded (W : WeierstrassCurve K) :
    homogeneousPieces K →+*ᵍ homogeneousPieces K where
  __ := negationRingHom W
  map_mem := fun h ↦ by
    change ((MvPolynomial.aeval (negationCoordinates W)) _).IsHomogeneous _
    simpa only [one_mul] using
      h.aeval (negationCoordinates W) (negationCoordinates_isHomogeneous W)

theorem negationRingHom_involutive (W : WeierstrassCurve K)
    (q : MvPolynomial (Fin 3) K) :
    negationRingHom W (negationRingHom W q) = q := by
  have hhom : (negationRingHom W).comp (negationRingHom W) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i
      · simp [negationRingHom_X, WeierstrassCurve.Projective.neg,
          WeierstrassCurve.Projective.negY, negationCoordinates]
      · simp [negationRingHom_X, WeierstrassCurve.Projective.neg,
          WeierstrassCurve.Projective.negY, negationCoordinates]
        ring
      · simp [negationRingHom_X, WeierstrassCurve.Projective.neg,
          WeierstrassCurve.Projective.negY, negationCoordinates]
  exact DFunLike.congr_fun hhom q

theorem negationGraded_involutive (W : WeierstrassCurve K) :
    (negationGraded W).comp (negationGraded W) =
      GradedRingHom.id (homogeneousPieces K) := by
  apply GradedRingHom.ext
  intro q
  exact negationRingHom_involutive W q

/-- Negation satisfies the irrelevant-ideal hypothesis needed to define a map on `Proj`. -/
theorem negation_irrelevant_le (W : WeierstrassCurve K) :
    HomogeneousIdeal.irrelevant (homogeneousPieces K) ≤
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).map (negationGraded W) := by
  change (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal ≤
    Ideal.map (negationGraded W)
      (HomogeneousIdeal.irrelevant (homogeneousPieces K)).toIdeal
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  rw [← negationRingHom_involutive W p]
  exact Ideal.mem_map_of_mem (negationGraded W)
    (HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousPieces K) hi
      ((negationGraded W).map_mem hp))

/-- The projective-plane automorphism induced by homogeneous Weierstrass negation. -/
noncomputable def ambientNegation (W : WeierstrassCurve K) :
    projectivePlane K ⟶ projectivePlane K :=
  Proj.map (negationGraded W) (negation_irrelevant_le W)

@[simp]
theorem ambientNegation_involutive (W : WeierstrassCurve K) :
    ambientNegation W ≫ ambientNegation W = 𝟙 _ := by
  change Proj.map (negationGraded W) (negation_irrelevant_le W) ≫
    Proj.map (negationGraded W) (negation_irrelevant_le W) = 𝟙 _
  rw [← Proj.map_comp]
  simpa only [negationGraded_involutive] using
    (Proj.map_id (𝒜 := homogeneousPieces K))

noncomputable instance ambientNegation_isIso (W : WeierstrassCurve K) :
    IsIso (ambientNegation W) := by
  apply IsIso.mk
  exact ⟨ambientNegation W, ambientNegation_involutive W,
    ambientNegation_involutive W⟩

theorem negationGraded_degreeZero (W : WeierstrassCurve K)
    (a : homogeneousPieces K 0) : negationGraded W a = a := by
  obtain ⟨r, rfl⟩ := (degreeZeroRingEquiv K).surjective a
  change negationRingHom W (MvPolynomial.C r) = MvPolynomial.C r
  exact negationRingHom_C W r

/-- On every homogeneous affine chart, the ring map induced by negation commutes with the
inclusion of the degree-zero coefficient ring. -/
theorem negationAwayMap_comp_fromZeroRingHom (W : WeierstrassCurve K)
    {d : ℕ} (s : MvPolynomial (Fin 3) K) (hs : s ∈ homogeneousPieces K d) :
    (HomogeneousLocalization.Away.map (negationGraded W) s).comp
        (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
          (Submonoid.powers s)) =
      HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (negationGraded W s)) := by
  apply RingHom.ext
  intro a
  simp only [RingHom.coe_comp, Function.comp_apply]
  have hleft :
      HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
          (Submonoid.powers s) a =
        HomogeneousLocalization.Away.mk (homogeneousPieces K) hs 0 a
          (by simpa using a.property) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    change Localization.mk (a : MvPolynomial (Fin 3) K)
        ⟨1, Submonoid.one_mem _⟩ =
      Localization.mk (a : MvPolynomial (Fin 3) K) ⟨s ^ 0, by simp⟩
    simp
  have hright :
      HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
          (Submonoid.powers (negationGraded W s)) a =
        HomogeneousLocalization.Away.mk (homogeneousPieces K)
          ((negationGraded W).map_mem hs) 0 a (by simpa using a.property) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    change Localization.mk (a : MvPolynomial (Fin 3) K)
        ⟨1, Submonoid.one_mem _⟩ =
      Localization.mk (a : MvPolynomial (Fin 3) K)
        ⟨(negationGraded W s) ^ 0, by simp⟩
    simp
  rw [hleft, hright, HomogeneousLocalization.Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  simp only [negationGraded_degreeZero]
  congr 1

theorem ambientNegation_comp_toSpecZero (W : WeierstrassCurve K) :
    ambientNegation W ≫ Proj.toSpecZero (homogeneousPieces K) =
      Proj.toSpecZero (homogeneousPieces K) := by
  refine (Proj.mapAffineOpenCover (negationGraded W)
    (negation_irrelevant_le W)).openCover.hom_ext _ _ ?_
  rintro ⟨d, ⟨s, hs⟩⟩
  change Proj.awayι (homogeneousPieces K) (negationGraded W s)
        ((negationGraded W).map_mem hs) d.pos ≫ ambientNegation W ≫
          Proj.toSpecZero (homogeneousPieces K) =
    Proj.awayι (homogeneousPieces K) (negationGraded W s)
        ((negationGraded W).map_mem hs) d.pos ≫
          Proj.toSpecZero (homogeneousPieces K)
  simp only [ambientNegation]
  rw [Proj.awayι_comp_map_assoc (negationGraded W) (negation_irrelevant_le W)
    d.pos s hs]
  rw [Proj.awayι_toSpecZero]
  rw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    negationAwayMap_comp_fromZeroRingHom W (d := (d : ℕ)) s hs]

@[simp, reassoc]
theorem ambientNegation_comp_projectivePlaneStructureMap
    (W : WeierstrassCurve K) :
    ambientNegation W ≫ projectivePlaneStructureMap K =
      projectivePlaneStructureMap K := by
  rw [projectivePlaneStructureMap, ← Category.assoc,
    ambientNegation_comp_toSpecZero]

@[simp]
theorem negationRingHom_polynomial (W : WeierstrassCurve K) :
    negationRingHom W W.toProjective.polynomial = W.toProjective.polynomial := by
  simp [negationRingHom, negationCoordinates, WeierstrassCurve.Projective.neg,
    WeierstrassCurve.Projective.negY, WeierstrassCurve.Projective.polynomial,
    WeierstrassCurve.map]
  ring

theorem ambientNegation_mem_carrier (W : WeierstrassCurve K)
    (x : projectivePlane K) (hx : x ∈ carrier W) :
    ambientNegation W x ∈ carrier W := by
  have hx' : W.toProjective.polynomial ∈
      (x.asHomogeneousIdeal : Set (MvPolynomial (Fin 3) K)) :=
    (mem_zeroLocus_iff W _).mp hx
  apply (mem_zeroLocus_iff W (ambientNegation W x)).mpr
  change negationRingHom W W.toProjective.polynomial ∈
    (x.asHomogeneousIdeal : Set (MvPolynomial (Fin 3) K))
  rw [negationRingHom_polynomial]
  exact hx'

theorem ambientNegation_range_inclusion_subset (W : WeierstrassCurve K) :
    Set.range (inclusion W ≫ ambientNegation W) ⊆ carrier W := by
  rintro _ ⟨x, rfl⟩
  change ambientNegation W (inclusion W x) ∈ carrier W
  apply ambientNegation_mem_carrier W
  rw [← range_inclusion W]
  exact ⟨x, rfl⟩

/-- Weierstrass negation restricted to the concrete reduced projective cubic. -/
noncomputable def negation (W : WeierstrassCurve K) : scheme W ⟶ scheme W :=
  MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.lift
    (inclusion W ≫ ambientNegation W) (closedCarrier W)
      (ambientNegation_range_inclusion_subset W)

@[simp, reassoc]
theorem negation_comp_inclusion (W : WeierstrassCurve K) :
    negation W ≫ inclusion W = inclusion W ≫ ambientNegation W :=
  MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.lift_comp_subschemeι _ _ _

@[simp]
theorem negation_involutive (W : WeierstrassCurve K) :
    negation W ≫ negation W = 𝟙 _ := by
  apply (cancel_mono (inclusion W)).1
  rw [Category.assoc, negation_comp_inclusion, ← Category.assoc,
    negation_comp_inclusion, Category.assoc, ambientNegation_involutive,
    Category.comp_id, Category.id_comp]

noncomputable instance negation_isIso (W : WeierstrassCurve K) :
    IsIso (negation W) := by
  apply IsIso.mk
  exact ⟨negation W, negation_involutive W, negation_involutive W⟩

@[simp, reassoc]
theorem negation_comp_structureMap (W : WeierstrassCurve K) :
    negation W ≫ structureMap W = structureMap W := by
  rw [structureMap, ← Category.assoc, negation_comp_inclusion,
    Category.assoc, ambientNegation_comp_projectivePlaneStructureMap]

/-- The Weierstrass negation involution as an automorphism over the ground field. -/
noncomputable def negationOver (W : WeierstrassCurve K) : toOver W ⟶ toOver W :=
  Over.homMk (negation W) (negation_comp_structureMap W)

@[simp]
theorem negationOver_involutive (W : WeierstrassCurve K) :
    negationOver W ≫ negationOver W = 𝟙 _ := by
  ext
  exact negation_involutive W

noncomputable instance negationOver_isIso (W : WeierstrassCurve K) :
    IsIso (negationOver W) := by
  apply IsIso.mk
  exact ⟨negationOver W, negationOver_involutive W, negationOver_involutive W⟩

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
