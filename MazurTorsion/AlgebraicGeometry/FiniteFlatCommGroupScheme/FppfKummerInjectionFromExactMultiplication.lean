/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlatBadFiberClosedFiberControl
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneShortExactInjective
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneUniverse
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfKummerRankZero
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteBadLevelEuler

/-!
# Global fppf H¹ injectivity from the constant-flat cokernel

The constant ambient point sheaf restricts surjectively from `Spec ℤ` to a prime closed
fibre.  Concrete closed-fibre control of the supported cokernel then upgrades its locally
surjective quotient map to a surjection on global sections.  The checked short-exact sheaf
theorem consequently makes the constant-flat inclusion injective on global fppf `H¹`.

The result concerns the actual represented coefficient sheaves and their actual supported
cokernel.  Despite the frozen historical filename, this module proves no exact-multiplication
or Mordell--Weil Kummer theorem.  It does not identify an arithmetic Mordell--Weil group with
represented base points, construct a Néron model, or assert a quotient-cohomology or torsion
theorem; those inputs remain explicit in the rank-zero consumers below.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open CommGroupScheme
open FiniteFlatCommGroupScheme

universe u

/-- Global sections of the represented ambient constant point sheaf, in the multiplicative
spelling used by the closed-fibre comparison. -/
abbrev MazurConstantFlatGlobalAmbientHZero
    (coeffPrime : ℕ) [NeZero coeffPrime] :=
  Multiplicative
    (((representedAddPointFppfSheaf
      (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj).obj).obj
        (Opposite.op (baseObject (Spec (.of ℤ)))))

/-- Restriction of represented ambient constant sections to the named closed-fibre test
object. -/
def mazurConstantFlatGlobalAmbientRestriction
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatGlobalAmbientHZero coeffPrime →*
      MazurConstantFlatClosedFiberAmbientHZero coeffPrime level :=
  AddMonoidHom.toMultiplicative <|
    (((representedAddPointFppfSheaf
      (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj).obj).map
        (zmodLevelFiberToBaseObject level).op).hom

/-- The represented ambient global-section carrier is canonically the indexing group. -/
def mazurConstantFlatGlobalAmbientHZeroMulEquiv
    (coeffPrime : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatGlobalAmbientHZero coeffPrime ≃*
      Multiplicative (ZMod coeffPrime) :=
  ((AddEquiv.ulift (α := Additive
    (FiniteFlatCommGroupScheme.BasePoint (constantScheme ℤ
      (Multiplicative (ZMod coeffPrime)))))).toMultiplicative).trans
      (constantBasePointMulEquiv_of_noZeroDivisors ℤ
        (Multiplicative (ZMod coeffPrime)))

/-- Reduction to a prime closed fibre detects integral sections of the represented constant
scheme.  The proof reads both restrictions on the constant coordinate ring; distinct component
evaluations remain distinct in the nonzero prime residue field. -/
theorem mazurConstantFlatGlobalAmbientRestriction_injective
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    Function.Injective
      (mazurConstantFlatGlobalAmbientRestriction coeffPrime level) := by
  letI : Fact level.Prime := ⟨hlevel⟩
  let G := Multiplicative (ZMod coeffPrime)
  let Egl := mazurConstantFlatGlobalAmbientHZeroMulEquiv coeffPrime
  let P := pointMulEquivOfTestIso (constantScheme ℤ G)
    (baseObjectIsoTestObject ℤ)
  let e := constantPointMulEquiv_of_noZeroDivisors ℤ G
  let f := Algebra.ofId ℤ (ZMod level)
  intro x y hxy
  let x₀ : FiniteFlatCommGroupScheme.BasePoint
      (constantScheme ℤ G) := x.toAdd.down.toMul
  let y₀ : FiniteFlatCommGroupScheme.BasePoint
      (constantScheme ℤ G) := y.toAdd.down.toMul
  let g := Egl x
  let h := Egl y
  have hpull := congrArg (fun z ↦ z.toAdd.down.toMul) hxy
  change zmodLevelFiberToBaseObject level ≫ x₀ =
    zmodLevelFiberToBaseObject level ≫ y₀ at hpull
  have hxP : P x₀ = constantPoint ℤ G g := by
    change P x₀ = e g
    rw [show g = e.symm (P x₀) by rfl, e.apply_symm_apply]
  have hyP : P y₀ = constantPoint ℤ G h := by
    change P y₀ = e h
    rw [show h = e.symm (P y₀) by rfl, e.apply_symm_apply]
  have htest : zmodLevelFiberToBaseObject level =
      AffineCommGroupScheme.testObjectMap f ≫ (baseObjectIsoTestObject ℤ).inv := by
    apply Over.OverMorphism.ext
    rfl
  have hrestricted :
      AffineCommGroupScheme.testObjectMap f ≫ constantPoint ℤ G g =
        AffineCommGroupScheme.testObjectMap f ≫ constantPoint ℤ G h := by
    rw [← hxP, ← hyP]
    change AffineCommGroupScheme.testObjectMap f ≫
        ((baseObjectIsoTestObject ℤ).inv ≫ x₀) =
      AffineCommGroupScheme.testObjectMap f ≫
        ((baseObjectIsoTestObject ℤ).inv ≫ y₀)
    rw [← Category.assoc, ← Category.assoc]
    rw [← htest]
    exact hpull
  have halg := congrArg
    (fun z ↦ (constant ℤ G).obj.pointToAlgHom (ZMod level) z) hrestricted
  rw [AffineCommGroupScheme.pointToAlgHom_testObjectMap,
    AffineCommGroupScheme.pointToAlgHom_testObjectMap,
    pointToAlgHom_constantPoint, pointToAlgHom_constantPoint] at halg
  have hgh : g = h := by
    by_contra hne
    let δ : ConstantCoordinates ℤ G :=
      ULift.up (fun z ↦ if z = g then 1 else 0)
    have hδ := DFunLike.congr_fun halg δ
    change algebraMap ℤ (ZMod level) (if g = g then 1 else 0) =
      algebraMap ℤ (ZMod level) (if h = g then 1 else 0) at hδ
    rw [if_pos rfl, if_neg (Ne.symm hne), map_one, map_zero] at hδ
    exact one_ne_zero hδ
  apply Egl.injective
  exact hgh

/-- Every represented ambient section on a prime closed fibre is the restriction of an
integral constant section. -/
theorem mazurConstantFlatGlobalAmbientRestriction_surjective
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    Function.Surjective
      (mazurConstantFlatGlobalAmbientRestriction coeffPrime level) := by
  let Ecl :=
    (mazurConstantFlatClosedFiberAmbientHZeroMulEquiv coeffPrime level).trans
      (mazurConstantClosedFiberHZeroMulEquiv coeffPrime level hlevel)
  let Egl := mazurConstantFlatGlobalAmbientHZeroMulEquiv coeffPrime
  letI : Finite (MazurConstantFlatClosedFiberAmbientHZero coeffPrime level) :=
    Finite.of_equiv (Multiplicative (ZMod coeffPrime)) Ecl.symm.toEquiv
  have hcard :
      Nat.card (MazurConstantFlatClosedFiberAmbientHZero coeffPrime level) ≤
        Nat.card (MazurConstantFlatGlobalAmbientHZero coeffPrime) := by
    rw [Nat.card_congr Ecl.toEquiv, Nat.card_congr Egl.toEquiv]
  exact ((mazurConstantFlatGlobalAmbientRestriction_injective
    coeffPrime level hlevel).bijective_of_nat_card_le hcard).2

/-- The actual represented ambient-to-cokernel projection evaluated at `Spec ℤ`. -/
def mazurConstantFlatGlobalCokernelProjection
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatGlobalAmbientHZero coeffPrime →*
      MazurConstantFlatBadFiberHZero coeffPrime level :=
  AddMonoidHom.toMultiplicative <|
    ((constantFlatRepresentedPointCokernelFppfProjection
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)).hom.app
        (Opposite.op (baseObject (Spec (.of ℤ))))).hom

/-- Evaluation of the represented quotient projection commutes with restriction to the named
closed-fibre test object. -/
theorem mazurConstantFlatGlobalCokernelProjection_restriction
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    (mazurConstantFlatBadFiberRestriction coeffPrime level).comp
        (mazurConstantFlatGlobalCokernelProjection coeffPrime level) =
      (mazurConstantFlatClosedFiberCokernelProjection coeffPrime level).comp
        (mazurConstantFlatGlobalAmbientRestriction coeffPrime level) := by
  apply MonoidHom.ext
  intro x
  exact (NatTrans.naturality_apply
    (constantFlatRepresentedPointCokernelFppfProjection
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)).hom
    (zmodLevelFiberToBaseObject level).op x.toAdd).symm

/-- Concrete closed-fibre control upgrades the locally-surjective represented quotient map to
surjectivity on integral global sections. -/
theorem mazurConstantFlatGlobalCokernelProjection_surjective
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    Function.Surjective
      (mazurConstantFlatGlobalCokernelProjection coeffPrime level) := by
  let C := mazurConstantFlatBadFiberClosedFiberControl coeffPrime level
  intro q
  obtain ⟨x, hx⟩ :=
    mazurConstantFlatGlobalAmbientRestriction_surjective coeffPrime level hlevel
      (C.comparison (mazurConstantFlatBadFiberRestriction coeffPrime level q))
  refine ⟨x, ?_⟩
  apply C.restriction_injective
  calc
    mazurConstantFlatBadFiberRestriction coeffPrime level
        (mazurConstantFlatGlobalCokernelProjection coeffPrime level x) =
      mazurConstantFlatClosedFiberCokernelProjection coeffPrime level
        (mazurConstantFlatGlobalAmbientRestriction coeffPrime level x) := by
          exact congrArg (fun f ↦ f x)
            (mazurConstantFlatGlobalCokernelProjection_restriction
              coeffPrime level)
    _ = mazurConstantFlatClosedFiberCokernelProjection coeffPrime level
        (C.comparison (mazurConstantFlatBadFiberRestriction coeffPrime level q)) := by
          rw [hx]
    _ = mazurConstantFlatBadFiberRestriction coeffPrime level q := by
          simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using
            congrArg
              (fun f ↦ f (mazurConstantFlatBadFiberRestriction
                coeffPrime level q)) C.projection_comp_comparison

/-! ### The represented short exact sequence -/

private noncomputable def representedAddPointFppfMap
    {S : Scheme.{u}} {G H : CommGroupScheme S} (f : G ⟶ H) :
    representedAddPointFppfSheaf G ⟶ representedAddPointFppfSheaf H :=
  ⟨Functor.whiskerRight (addPointPresheafMap f)
    AddCommGrpCat.uliftFunctor.{u + 1}⟩

private theorem representedAddPointFppfMap_comp_sheafificationIso
    {S : Scheme.{u}} {G H : CommGroupScheme S} (f : G ⟶ H) :
    representedAddPointFppfMap f ≫ (representedAddPointFppfSheafIso H).hom =
      (representedAddPointFppfSheafIso G).hom ≫ addPointFppfMap f := by
  exact (sheafificationNatIso (Scheme.fppfTopology.over S)
    AddCommGrpCat.{u + 1}).hom.naturality (representedAddPointFppfMap f)

private abbrev mazurConstantFlatRepresentedSubgroupSheaf
    (coeffPrime level : ℕ) [NeZero coeffPrime] :=
  representedAddPointFppfSheaf (mazurConstantFlat coeffPrime level).obj

private abbrev mazurConstantFlatRepresentedAmbientSheaf
    (coeffPrime : ℕ) [NeZero coeffPrime] :=
  representedAddPointFppfSheaf
    (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj

private abbrev mazurConstantFlatRepresentedSubgroupMap
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    mazurConstantFlatRepresentedSubgroupSheaf coeffPrime level ⟶
      mazurConstantFlatRepresentedAmbientSheaf coeffPrime :=
  representedAddPointFppfMap
    (constantFlatInclusion
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ))

private abbrev mazurConstantFlatRepresentedCokernelProjection
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    mazurConstantFlatRepresentedAmbientSheaf coeffPrime ⟶
      constantFlatPointCokernelFppfSheaf
        (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ) :=
  constantFlatRepresentedPointCokernelFppfProjection
    (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)

private theorem mazurConstantFlatRepresentedSubgroupMap_comp_projection_zero
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    mazurConstantFlatRepresentedSubgroupMap coeffPrime level ≫
      mazurConstantFlatRepresentedCokernelProjection coeffPrime level = 0 := by
  let inclusion := constantFlatInclusion
    (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)
  calc
    representedAddPointFppfMap inclusion ≫
        ((representedAddPointFppfSheafIso
          (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj).hom ≫
            pointCokernelFppfProjection inclusion) =
      (representedAddPointFppfMap inclusion ≫
        (representedAddPointFppfSheafIso
          (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj).hom) ≫
            pointCokernelFppfProjection inclusion := (Category.assoc _ _ _).symm
    _ = ((representedAddPointFppfSheafIso
          (mazurConstantFlat coeffPrime level).obj).hom ≫
            addPointFppfMap inclusion) ≫
          pointCokernelFppfProjection inclusion := by
      rw [representedAddPointFppfMap_comp_sheafificationIso]
    _ = (representedAddPointFppfSheafIso
          (mazurConstantFlat coeffPrime level).obj).hom ≫
        (addPointFppfMap inclusion ≫ pointCokernelFppfProjection inclusion) :=
      Category.assoc _ _ _
    _ = 0 := by
      have hz : addPointFppfMap inclusion ≫
          pointCokernelFppfProjection inclusion = 0 :=
        (pointCokernelFppfSequence inclusion).zero
      rw [hz]
      simp

private noncomputable def mazurConstantFlatRepresentedCokernelSequence
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    ShortComplex
      (Sheaf (Scheme.fppfTopology.over (Spec (.of ℤ))) AddCommGrpCat.{1}) :=
  ShortComplex.mk
    (mazurConstantFlatRepresentedSubgroupMap coeffPrime level)
    (mazurConstantFlatRepresentedCokernelProjection coeffPrime level)
    (mazurConstantFlatRepresentedSubgroupMap_comp_projection_zero
      coeffPrime level)

private theorem mazurConstantFlatRepresentedCokernelSequence_shortExact
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    (mazurConstantFlatRepresentedCokernelSequence
      coeffPrime level).ShortExact := by
  let inclusion := constantFlatInclusion
    (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)
  let S := mazurConstantFlatRepresentedCokernelSequence coeffPrime level
  let S₀ := pointCokernelFppfSequence inclusion
  let e : S ≅ S₀ :=
    ShortComplex.isoMk
      (representedAddPointFppfSheafIso
        (mazurConstantFlat coeffPrime level).obj)
      (representedAddPointFppfSheafIso
        (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj)
      (Iso.refl _) (by
        exact (representedAddPointFppfMap_comp_sheafificationIso inclusion).symm)
      (by
        change (representedAddPointFppfSheafIso
            (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj).hom ≫
              pointCokernelFppfProjection inclusion =
          ((representedAddPointFppfSheafIso
            (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj).hom ≫
              pointCokernelFppfProjection inclusion) ≫ 𝟙 _
        simp)
  exact ShortComplex.shortExact_of_iso e.symm
    (pointCokernelFppfSequence_shortExact_of_mono inclusion)

private theorem mazurConstantFlatRepresentedCokernelProjection_base_surjective
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    Function.Surjective
      ((mazurConstantFlatRepresentedCokernelProjection
        coeffPrime level).hom.app
          (Opposite.op (Over.mk (𝟙 (Spec (.of ℤ)))))).hom := by
  intro q
  obtain ⟨x, hx⟩ :=
    mazurConstantFlatGlobalCokernelProjection_surjective
      coeffPrime level hlevel (Multiplicative.ofAdd q)
  exact ⟨x.toAdd, congrArg Multiplicative.toAdd hx⟩

/-! ### Injectivity on the actual represented fppf `H¹` -/

private theorem fppfHOne_mulEquivUlift_mapHom
    {X : Scheme.{u}}
    {A B : (Over X)ᵒᵖ ⥤ CommGrpCat.{u}}
    (f : A ⟶ B)
    (x : Scheme.FppfHOne.{u, u, u} X
      (CategoryTheory.PresheafOfCommGroups.toGroups A)) :
    Scheme.FppfHOne.mulEquivUlift.{u + 1}
        B (Scheme.FppfHOne.mapHom f x) =
      Scheme.FppfHOne.mapHom
        (Functor.whiskerRight f CommGrpCat.uliftFunctor.{u + 1})
        (Scheme.FppfHOne.mulEquivUlift.{u + 1} A x) := by
  induction x using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨cover, value⟩
      induction value using Quot.inductionOn with
      | _ c =>
          change Scheme.FppfHOne.mk cover _ =
            Scheme.FppfHOne.mk cover _
          apply congrArg (Scheme.FppfHOne.mk cover)
          congr 1

private theorem mazurConstantFlatFppfHOneMap_ulift_injective
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    let inclusion := constantFlatInclusion
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)
    Function.Injective
      (Scheme.FppfHOne.mapHom.{1, 0, 0}
        (Functor.whiskerRight (commPointPresheafMap inclusion)
          CommGrpCat.uliftFunctor.{1})) := by
  dsimp only
  let S := mazurConstantFlatRepresentedCokernelSequence coeffPrime level
  change Function.Injective
    (Scheme.FppfHOne.mapHom
      (Scheme.FppfHOne.addCommSheafCommPresheafMap S.f))
  exact Scheme.FppfHOne.mapHom_injective_of_shortExact_of_base_surjective
    S
    (mazurConstantFlatRepresentedCokernelSequence_shortExact coeffPrime level)
    (mazurConstantFlatRepresentedCokernelProjection_base_surjective
      coeffPrime level hlevel)

/-- At a prime bad level, the actual map from the constant-flat model to the ambient constant
group is injective on represented global fppf `H¹`. -/
theorem mazurConstantFlatFppfHOneMap_injective
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    Function.Injective
      (CommGroupScheme.fppfHOneMap.{0}
        (constantFlatInclusion
          (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ))) := by
  let inclusion := constantFlatInclusion
    (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)
  let A := (mazurConstantFlat coeffPrime level).obj.commPointPresheaf
  let B :=
    (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj.commPointPresheaf
  let i := commPointPresheafMap inclusion
  change Function.Injective (Scheme.FppfHOne.mapHom.{0, 0, 0} i)
  intro x y hxy
  apply (Scheme.FppfHOne.mulEquivUlift.{1} A).injective
  apply mazurConstantFlatFppfHOneMap_ulift_injective
    coeffPrime level hlevel
  rw [← fppfHOne_mulEquivUlift_mapHom i x,
    ← fppfHOne_mulEquivUlift_mapHom i y, hxy]

/-! ### Carrier-preserving five- and eleven-adic bounds -/

/-- An ambient global `H¹` bound pulls back to the actual constant-flat `H¹` with no extra
supported-cokernel exponent. -/
noncomputable def mazurConstantFlatFppfHOneBoundedDataOfAmbient
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime)
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime
      (mazurConstantFlat coeffPrime level).FppfHOne.{0} :=
  ambientData.ofInjective
    (CommGroupScheme.fppfHOneMap.{0}
      (constantFlatInclusion
        (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)))
    (mazurConstantFlatFppfHOneMap_injective coeffPrime level hlevel)

@[simp]
theorem mazurConstantFlatFppfHOneBoundedDataOfAmbient_length
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime)
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (mazurConstantFlatFppfHOneBoundedDataOfAmbient
      coeffPrime level hlevel ambientData).length = ambientData.length :=
  rfl

/-- The actual level-five constant-flat `H¹` inherits the ambient bound without a `+1`. -/
noncomputable def mazurConstantFlatFppfHOneBoundedDataAtFive
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime
      (mazurConstantFlat coeffPrime 5).FppfHOne.{0} :=
  mazurConstantFlatFppfHOneBoundedDataOfAmbient
    coeffPrime 5 (by decide) ambientData

/-- The actual level-eleven constant-flat `H¹` inherits the ambient bound without a `+1`. -/
noncomputable def mazurConstantFlatFppfHOneBoundedDataAtEleven
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    FinitePGroup.BoundedData coeffPrime
      (mazurConstantFlat coeffPrime 11).FppfHOne.{0} :=
  mazurConstantFlatFppfHOneBoundedDataOfAmbient
    coeffPrime 11 (by decide) ambientData

@[simp]
theorem mazurConstantFlatFppfHOneBoundedDataAtFive_length
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (mazurConstantFlatFppfHOneBoundedDataAtFive
      coeffPrime ambientData).length = ambientData.length :=
  rfl

@[simp]
theorem mazurConstantFlatFppfHOneBoundedDataAtEleven_length
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (ambientData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime)) :
    (mazurConstantFlatFppfHOneBoundedDataAtEleven
      coeffPrime ambientData).length = ambientData.length :=
  rfl

namespace FppfLowDegreeExactSequence

variable {coeffPrime level : ℕ} [NeZero coeffPrime]
variable {G : QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ))}

/-- The actual constant-flat injection removes the supported-cokernel term from the bad-level
Euler estimate. -/
theorem fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_ambientInjection
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (hlevel : level.Prime) (datum : MuFlatDatum coeffPrime level)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime level) G (muFlat coeffPrime level datum))
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime level datum).FppfHOne.{0})
    (bound : ℕ)
    (hbound : ambientConstantHOneData.length + quotientHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound := by
  have hodd : Odd coeffPrime := hprime.odd_of_ne_two hprime2
  have hconstant :
      ∀ x : BasePoint (mazurConstantFlat coeffPrime level), x = 1 := by
    intro x
    exact constantFlatBasePoint_eq_one ℤ (Multiplicative (ZMod coeffPrime))
      (level : ℤ) (by
        rw [Int.ofNat_isUnit]
        exact hlevel.not_isUnit) x
  have hmu : ∀ x : BasePoint (muFlat coeffPrime level datum), x = 1 :=
    fun x ↦ muFlatBasePoint_eq_one coeffPrime level datum hodd x
  have hconstantLength :
      (mazurConstantFlatBasePointCertifiedDataOfPrimeLevel
        coeffPrime level hlevel).length = 0 := rfl
  have hmuLength :
      (muFlatBasePointCertifiedDataOfOdd
        coeffPrime level datum hodd).length = 0 := rfl
  apply fppfHOne_natCard_le_pow_ofFppfQuotientPresentation_bounded
    D.toFppfQuotientPresentation
    (mazurConstantFlatBasePointCertifiedDataOfPrimeLevel
      coeffPrime level hlevel)
    (D.middleBasePointCertifiedData coeffPrime hconstant hmu)
    (muFlatBasePointCertifiedDataOfOdd coeffPrime level datum hodd)
    (mazurConstantFlatFppfHOneBoundedDataOfAmbient
      coeffPrime level hlevel ambientConstantHOneData)
    quotientHOneData hprime bound
  simpa [hconstantLength, hmuLength] using hbound

/-- The level-five Euler endpoint uses the actual constant-flat `H¹` carrier and has no
localization datum or supported-cokernel exponent among its premises. -/
theorem fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_atFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 5) G (muFlat coeffPrime 5 datum))
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    (bound : ℕ)
    (hbound : ambientConstantHOneData.length + quotientHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound :=
  fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_ambientInjection
    hprime hprime2 (by decide) datum D ambientConstantHOneData quotientHOneData
      bound hbound

/-- The corresponding actual-carrier Euler endpoint at level eleven. -/
theorem fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_atEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 11) G (muFlat coeffPrime 11 datum))
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    (bound : ℕ)
    (hbound : ambientConstantHOneData.length + quotientHOneData.length ≤ bound) :
    Nat.card G.FppfHOne.{0} ≤ coeffPrime ^ bound :=
  fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_ambientInjection
    hprime hprime2 (by decide) datum D ambientConstantHOneData quotientHOneData
      bound hbound

/-- The level-five Euler bound feeds the checked rank-zero criterion.  The Mordell--Weil
carrier, its exact multiplication-by-`coeffPrime` torsion law, and the Kummer injection remain
explicit arithmetic premises. -/
theorem finrank_eq_zero_of_fppfKummer_constantFlatKernel_muFlatQuotient_atFive
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 5)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 5) G (muFlat coeffPrime 5 datum))
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 5 datum).FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : ambientConstantHOneData.length + quotientHOneData.length ≤
      torsionLength) :
    Module.finrank ℤ A = 0 := by
  let constantHOneData :=
    mazurConstantFlatFppfHOneBoundedDataAtFive
      coeffPrime ambientConstantHOneData
  letI : Finite
      D.toFppfQuotientPresentation.kernelPresentation.kernel.FppfHOne.{0} := by
    simpa using constantHOneData.finite
  letI : Finite D.toFppfQuotientPresentation.quotient.FppfHOne.{0} := by
    simpa using quotientHOneData.finite
  letI : Finite G.FppfHOne.{0} :=
    D.toFppfQuotientPresentation.middleFppfHOne_finite
  apply FiniteFlatCommGroupScheme.finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hprime hkernel kummer hkummer
  exact fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_atFive
    hprime hprime2 datum D ambientConstantHOneData quotientHOneData
      torsionLength hbound

/-- The same actual-carrier Kummer/rank-zero endpoint at level eleven. -/
theorem finrank_eq_zero_of_fppfKummer_constantFlatKernel_muFlatQuotient_atEleven
    (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (datum : MuFlatDatum coeffPrime 11)
    (D : FppfExtensionPresentation
      (mazurConstantFlat coeffPrime 11) G (muFlat coeffPrime 11 datum))
    (ambientConstantHOneData : FinitePGroup.BoundedData coeffPrime
      (MazurConstantAmbientFppfHOne coeffPrime))
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      (muFlat coeffPrime 11 datum).FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : ambientConstantHOneData.length + quotientHOneData.length ≤
      torsionLength) :
    Module.finrank ℤ A = 0 := by
  let constantHOneData :=
    mazurConstantFlatFppfHOneBoundedDataAtEleven
      coeffPrime ambientConstantHOneData
  letI : Finite
      D.toFppfQuotientPresentation.kernelPresentation.kernel.FppfHOne.{0} := by
    simpa using constantHOneData.finite
  letI : Finite D.toFppfQuotientPresentation.quotient.FppfHOne.{0} := by
    simpa using quotientHOneData.finite
  letI : Finite G.FppfHOne.{0} :=
    D.toFppfQuotientPresentation.middleFppfHOne_finite
  apply FiniteFlatCommGroupScheme.finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hprime hkernel kummer hkummer
  exact fppfHOne_natCard_le_pow_of_constantFlatKernel_muFlatQuotient_atEleven
    hprime hprime2 datum D ambientConstantHOneData quotientHOneData
      torsionLength hbound

end FppfLowDegreeExactSequence

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
