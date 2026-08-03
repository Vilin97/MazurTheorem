/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlat
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ElementaryGlobalSections

/-!
# Global sections of Mazur's bad-level constant factor

The principal-open model `(Z/pZ)^flat` at level `N` retains the identity component over all of
`Spec ℤ` and its other components only over `D(N)`.  Algebraically, inverting the component
function forces every integral point to be evaluation at the identity whenever `N` is not a
unit.  We prove this first over any integral base ring, then identify geometric global sections
with affine points and package the resulting one-element group as honest
`FinitePGroup.CertifiedData`.

The coefficient parameter `p` and bad level `N` remain separate throughout.  No fppf `H¹`
calculation or exact-sequence representability claim is made here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open FiniteFlatCommGroupScheme

universe u

variable {R G : Type u} [CommRing R] [CommGroup G]

private abbrev flatIota (N : R) :
    ConstantCoordinates R G →ₐ[R] ConstantFlatCoordinates R G N :=
  Algebra.algHom R (ConstantCoordinates R G) (ConstantFlatCoordinates R G N)

private theorem constantFlatAlgHom_comp_iota_eq_evaluation_one
    [Finite G] [NoZeroDivisors R] [Nontrivial R] (N : R) (hN : ¬ IsUnit N)
    (f : ConstantFlatCoordinates R G N →ₐ[R] R) :
    f.comp (flatIota (G := G) N) =
      ConstantCoordinates.evaluation (R := R) (1 : G) := by
  letI : Fintype G := Fintype.ofFinite G
  let φ : (G → R) →ₐ[R] R :=
    (f.comp (flatIota (G := G) N)).comp ULift.algEquiv.symm.toAlgHom
  obtain ⟨g, hg⟩ := AlgHom.eq_piEvalAlgHom φ
  have heunit : IsUnit
      (f (algebraMap (ConstantCoordinates R G)
        (ConstantFlatCoordinates R G N) (constantFlatElement (G := G) N))) :=
    (IsLocalization.Away.algebraMap_isUnit
      (constantFlatElement (G := G) N)).map f.toRingHom
  have hge := DFunLike.congr_fun hg (constantFlatElement (G := G) N).down
  have he_up : (ULift.algEquiv (R := R)).symm
      (constantFlatElement (G := G) N).down =
        constantFlatElement (G := G) N := by
    apply ULift.ext
    rfl
  change f (algebraMap (ConstantCoordinates R G)
      (ConstantFlatCoordinates R G N)
        ((ULift.algEquiv (R := R)).symm
          (constantFlatElement (G := G) N).down)) =
    (constantFlatElement (G := G) N).down g at hge
  rw [he_up] at hge
  have hg1 : g = 1 := by
    by_contra hgne
    apply hN
    rw [hge,
      constantFlatElement_down_apply, if_neg hgne] at heunit
    exact heunit
  apply AlgHom.ext
  intro a
  have ha := DFunLike.congr_fun hg a.down
  have ha_up : (ULift.algEquiv (R := R)).symm a.down = a := by
    apply ULift.ext
    rfl
  change f (algebraMap (ConstantCoordinates R G)
      (ConstantFlatCoordinates R G N) ((ULift.algEquiv (R := R)).symm a.down)) =
    a.down g at ha
  rw [ha_up, hg1] at ha
  change f (algebraMap (ConstantCoordinates R G)
      (ConstantFlatCoordinates R G N) a) = a.down 1
  exact ha

/-- If the level is not a unit in an integral base ring, the bad-level constant group has only
its identity affine point over that base. -/
theorem constantFlatAffine_point_eq_one
    [Fintype G] [NoZeroDivisors R] [Nontrivial R] (N : R) (hN : ¬ IsUnit N)
    (x : (constantFlatAffine R G N).Point R) : x = 1 := by
  let e := constantFlatElement (G := G) N
  apply ((constantFlatAffine R G N).pointMulEquiv R).injective
  rw [AffineCommGroupScheme.pointMulEquiv_apply,
    AffineCommGroupScheme.pointMulEquiv_apply]
  apply WithConv.ofConv_injective
  apply IsLocalization.algHom_ext (Submonoid.powers e)
  apply AlgHom.ext
  intro a
  have hx := DFunLike.congr_fun
    (constantFlatAlgHom_comp_iota_eq_evaluation_one (G := G) N hN
      ((constantFlatAffine R G N).pointToAlgHom R x)) a
  have hone := DFunLike.congr_fun
    (constantFlatAlgHom_comp_iota_eq_evaluation_one (G := G) N hN
      ((constantFlatAffine R G N).pointToAlgHom R (1 : (constantFlatAffine R G N).Point R))) a
  exact hx.trans hone.symm

/-- Global points of the quasi-finite constant-flat model are its affine points over the base
ring. -/
noncomputable def constantFlatBasePointMulEquivAffinePoint
    (R : Type u) [CommRing R] (G : Type u) [CommGroup G] [Fintype G] (N : R) :
    CommGroupScheme.Point (constantFlat R G N).obj
        (baseObject (Spec (.of R))) ≃*
      (constantFlatAffine R G N).Point R where
  toFun x := (baseObjectIsoTestObject R).inv ≫ x
  invFun x := (baseObjectIsoTestObject R).hom ≫ x
  left_inv x := by
    change (baseObjectIsoTestObject R).hom ≫
      (baseObjectIsoTestObject R).inv ≫ x = x
    simp
  right_inv x := by
    change (baseObjectIsoTestObject R).inv ≫
      (baseObjectIsoTestObject R).hom ≫ x = x
    simp
  map_mul' x y := map_mul
    (((CommGroupScheme.commPointPresheaf (constantFlat R G N).obj).map
      (baseObjectIsoTestObject R).inv.op).hom) x y

/-- At a nonunit level, the global sections of the constant-flat model form the trivial group. -/
noncomputable def constantFlatBasePointMulEquivUnit
    (R : Type u) [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (G : Type u) [CommGroup G] [Fintype G] (N : R) (hN : ¬ IsUnit N) :
    CommGroupScheme.Point (constantFlat R G N).obj
        (baseObject (Spec (.of R))) ≃* Unit :=
  (constantFlatBasePointMulEquivAffinePoint R G N).trans
    { toFun := fun _ ↦ Unit.unit
      invFun := fun _ ↦ 1
      left_inv := fun x ↦ (constantFlatAffine_point_eq_one N hN x).symm
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-- At a nonunit level every global section of the constant-flat model is the identity. -/
theorem constantFlatBasePoint_eq_one
    (R : Type u) [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (G : Type u) [CommGroup G] [Fintype G] (N : R) (hN : ¬ IsUnit N)
    (x : CommGroupScheme.Point (constantFlat R G N).obj
      (baseObject (Spec (.of R)))) : x = 1 := by
  apply (constantFlatBasePointMulEquivUnit R G N hN).injective
  simp

/-- The bad-level constant factor has one integral global section, certified as `p^0`. -/
noncomputable def mazurConstantFlatBasePointCertifiedData
    (coeffPrime level : ℕ) [NeZero coeffPrime]
    (hlevel : ¬ IsUnit (level : ℤ)) :
    FinitePGroup.CertifiedData coeffPrime
      (CommGroupScheme.Point (mazurConstantFlat coeffPrime level).obj
        (baseObject (Spec (.of ℤ)))) where
  finite := Finite.of_equiv Unit
    (constantFlatBasePointMulEquivUnit ℤ
      (Multiplicative (ZMod coeffPrime)) (level : ℤ) hlevel).symm.toEquiv
  length := 0
  card_eq := by
    rw [Nat.card_congr
      (constantFlatBasePointMulEquivUnit ℤ
        (Multiplicative (ZMod coeffPrime)) (level : ℤ) hlevel).toEquiv]
    simp

/-- A prime level is a nonunit in `ℤ`, hence the constant-flat factor has certified trivial
global sections there. -/
noncomputable def mazurConstantFlatBasePointCertifiedDataOfPrimeLevel
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    FinitePGroup.CertifiedData coeffPrime
      (CommGroupScheme.Point (mazurConstantFlat coeffPrime level).obj
        (baseObject (Spec (.of ℤ)))) :=
  mazurConstantFlatBasePointCertifiedData coeffPrime level (by
    rw [Int.ofNat_isUnit]
    exact hlevel.not_isUnit)

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
