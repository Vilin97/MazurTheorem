/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.ZMod.QuotientRing
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlatGlobalHOneLocalization
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ElementaryGlobalSections
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfHOneBridge
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfLocalization

/-!
# Closed-fibre control of the constant-flat supported cokernel

The localization handoff uses global sections of the actual fppf cokernel sheaf attached to
Mazur's constant-flat inclusion.  This file defines its canonical restriction from `Spec ℤ`
to the bad fibre `Spec (ZMod level)`.  It also identifies that fibre with the previously named
closed fibre `Spec (ℤ / (level))`.

The represented ambient constant sheaf on a prime fibre has exactly `coeffPrime` sections.
Its actual evaluated projection to the cokernel sheaf is named below.  Consequently, a section
of that projection, together with injectivity of canonical restriction to the fibre, gives a
checked `coeffPrime ^ 1` bound for the original global cokernel sections.
`MazurConstantFlatBadFiberClosedFiberControl` records precisely these geometric obligations.  It
does not accept a finiteness or cardinality certificate for the source or an arbitrary injection
into a finite carrier.

Constructing this control remains the next closed-fibre theorem: one must split the actual
evaluated cokernel projection on the closed fibre and prove that restriction of supported global
sections is injective.  The definitions specialized at fibres `5` and `11` are the consumers
needed by the selected formal-immersion route.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open CommGroupScheme
open FiniteFlatCommGroupScheme

/-- The closed-fibre inclusion `Spec (ZMod level) ⟶ Spec ℤ`. -/
abbrev zmodLevelFiberInclusion (level : ℕ) :
    Spec (.of (ZMod level)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod level)))

/-- The quotient-ring model of the level fibre is canonically the `ZMod` model. -/
def levelClosedFiberIsoZMod (level : ℕ) :
    levelClosedFiber (level : ℤ) ≅ Spec (.of (ZMod level)) :=
  (Scheme.Spec.mapIso
    (Int.quotientSpanNatEquivZMod level).toCommRingCatIso.op).symm

/-- The `ZMod` fibre inclusion agrees with the named quotient-ring closed-fibre inclusion. -/
theorem levelClosedFiberIsoZMod_hom_comp_inclusion (level : ℕ) :
    (levelClosedFiberIsoZMod level).hom ≫ zmodLevelFiberInclusion level =
      levelClosedFiberι (level : ℤ) := by
  dsimp [levelClosedFiberIsoZMod, zmodLevelFiberInclusion, levelClosedFiberι]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  ext n
  change (Int.quotientSpanNatEquivZMod level).symm ((n : ℤ) : ZMod level) =
    Ideal.Quotient.mk (Ideal.span ({(level : ℤ)} : Set ℤ)) n
  exact DFunLike.congr_fun
    (Int.quotientSpanNatEquivZMod_comp_castRingHom level) n

/-- Global sections of the ambient constant group after actual base change to the level fibre. -/
abbrev MazurConstantClosedFiberHZero
    (coeffPrime level : ℕ) [NeZero coeffPrime] :=
  FiniteFlatCommGroupScheme.BasePoint <|
    (FiniteFlatCommGroupScheme.baseChange
      (zmodLevelFiberInclusion level)).obj
        (constantScheme ℤ (Multiplicative (ZMod coeffPrime)))

/-- The level fibre as an object of the relative site over `Spec ℤ`. -/
def zmodLevelFiberOverBase (level : ℕ) : Over (Spec (.of ℤ)) :=
  Over.mk (zmodLevelFiberInclusion level)

/-- The named fibre test object is canonically the image of the terminal fibre object under
composition with the closed-fibre inclusion. -/
def zmodLevelFiberOverBaseIsoMappedBaseObject (level : ℕ) :
    zmodLevelFiberOverBase level ≅
      (Over.map (zmodLevelFiberInclusion level)).obj
        (CommGroupScheme.baseObject (Spec (.of (ZMod level)))) :=
  Over.isoMk (Iso.refl _) (by
    simp [zmodLevelFiberOverBase, CommGroupScheme.baseObject])

/-- The structural map from the level-fibre test object to the terminal relative test object. -/
def zmodLevelFiberToBaseObject (level : ℕ) :
    zmodLevelFiberOverBase level ⟶
      CommGroupScheme.baseObject (Spec (.of ℤ)) :=
  Over.homMk (zmodLevelFiberInclusion level) (by
    change zmodLevelFiberInclusion level ≫ 𝟙 _ = zmodLevelFiberInclusion level
    simp)

/-- Sections of the actual constant-flat cokernel sheaf on the level-fibre test object. -/
abbrev MazurConstantFlatClosedFiberCokernelHZero
    (coeffPrime level : ℕ) [NeZero coeffPrime] :=
  Multiplicative
    ((constantFlatPointCokernelFppfSheaf
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)).obj.obj
        (Opposite.op (zmodLevelFiberOverBase level)))

/-- Sections of the actual represented ambient constant sheaf on the level-fibre test object.
The `ULift` in this carrier is the one used by concrete fppf sheafification. -/
abbrev MazurConstantFlatClosedFiberAmbientHZero
    (coeffPrime level : ℕ) [NeZero coeffPrime] :=
  Multiplicative
    (((representedAddPointFppfSheaf
      (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj).obj).obj
        (Opposite.op (zmodLevelFiberOverBase level)))

/-- The actual evaluated projection from the represented ambient constant sheaf to the
constant-flat cokernel sheaf on the level fibre. -/
def mazurConstantFlatClosedFiberCokernelProjection
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatClosedFiberAmbientHZero coeffPrime level →*
      MazurConstantFlatClosedFiberCokernelHZero coeffPrime level :=
  AddMonoidHom.toMultiplicative <|
    ((constantFlatRepresentedPointCokernelFppfProjection
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)).hom.app
        (Opposite.op (zmodLevelFiberOverBase level))).hom

/-- Canonical restriction of actual supported-cokernel sections from the terminal object to the
level-fibre test object.  This is induced by the sheaf's own restriction map. -/
def mazurConstantFlatBadFiberRestriction
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatBadFiberHZero coeffPrime level →*
      MazurConstantFlatClosedFiberCokernelHZero coeffPrime level :=
  AddMonoidHom.toMultiplicative <|
    ((constantFlatPointCokernelFppfSheaf
      (R := ℤ) (G := Multiplicative (ZMod coeffPrime)) (level : ℤ)).obj.map
        (zmodLevelFiberToBaseObject level).op).hom

/-- On a prime level fibre, the actual base-changed ambient constant group has its indexing
group as global sections. -/
def mazurConstantClosedFiberHZeroMulEquiv
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    MazurConstantClosedFiberHZero coeffPrime level ≃*
      Multiplicative (ZMod coeffPrime) := by
  letI : Fact level.Prime := ⟨hlevel⟩
  exact
    (pointMulEquivOfIso
      (constantBaseChangeIso (R := ℤ) (K := ZMod level)
        (Multiplicative (ZMod coeffPrime)))
      (FiniteFlatCommGroupScheme.baseObject
        (Spec (.of (ZMod level))))).trans
        (constantBasePointMulEquiv_of_noZeroDivisors
          (ZMod level) (Multiplicative (ZMod coeffPrime)))

/-- The actual ambient constant group on a prime bad fibre has cardinality
`coeffPrime = coeffPrime ^ 1`. -/
def mazurConstantClosedFiberHZeroCertifiedData
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    FinitePGroup.CertifiedData coeffPrime
      (MazurConstantClosedFiberHZero coeffPrime level) := by
  letI : Fact level.Prime := ⟨hlevel⟩
  let e := mazurConstantClosedFiberHZeroMulEquiv coeffPrime level hlevel
  exact
    { finite := Finite.of_equiv (Multiplicative (ZMod coeffPrime)) e.symm.toEquiv
      length := 1
      card_eq := by
        rw [Nat.card_congr e.toEquiv, pow_one]
        exact (Nat.card_congr
          (Multiplicative.ofAdd : ZMod coeffPrime ≃
            Multiplicative (ZMod coeffPrime))).trans
              (Nat.card_zmod coeffPrime) }

/-- The represented-sheaf fibre carrier is canonically the base-point carrier of the actual
base-changed ambient constant group. -/
def mazurConstantFlatClosedFiberAmbientHZeroMulEquiv
    (coeffPrime level : ℕ) [NeZero coeffPrime] :
    MazurConstantFlatClosedFiberAmbientHZero coeffPrime level ≃*
      MazurConstantClosedFiberHZero coeffPrime level :=
  ((AddEquiv.ulift (α := Additive
    ((constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj.Point
      (zmodLevelFiberOverBase level)))).toMultiplicative).trans <|
    ((constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj.pointMulEquivOfOverIso
      (zmodLevelFiberOverBaseIsoMappedBaseObject level)).trans <|
        (CommGroupScheme.baseChangePointMulEquiv
          (zmodLevelFiberInclusion level)
          (constantScheme ℤ (Multiplicative (ZMod coeffPrime))).obj
          (CommGroupScheme.baseObject (Spec (.of (ZMod level))))).symm

/-- The actual represented ambient sheaf evaluation on a prime fibre has cardinality
`coeffPrime = coeffPrime ^ 1`. -/
def mazurConstantFlatClosedFiberAmbientHZeroCertifiedData
    (coeffPrime level : ℕ) [NeZero coeffPrime] (hlevel : level.Prime) :
    FinitePGroup.CertifiedData coeffPrime
      (MazurConstantFlatClosedFiberAmbientHZero coeffPrime level) :=
  (mazurConstantClosedFiberHZeroCertifiedData
    coeffPrime level hlevel).congr
      (mazurConstantFlatClosedFiberAmbientHZeroMulEquiv
        coeffPrime level).symm

/-- The remaining geometric closed-fibre control needed to bound the actual supported cokernel
sections.  The comparison must be a section of the actual evaluated ambient-to-cokernel
projection, and the canonical restriction map must independently detect global supported
sections. -/
structure MazurConstantFlatBadFiberClosedFiberControl
    (coeffPrime level : ℕ) [NeZero coeffPrime] where
  /-- A section candidate from actual cokernel sections to represented ambient sections. -/
  comparison : MazurConstantFlatClosedFiberCokernelHZero coeffPrime level →*
    MazurConstantFlatClosedFiberAmbientHZero coeffPrime level
  /-- The candidate really splits the actual evaluated fppf cokernel projection. -/
  projection_comp_comparison :
    (mazurConstantFlatClosedFiberCokernelProjection
      coeffPrime level).comp comparison = MonoidHom.id _
  /-- Canonical restriction itself detects every global supported section. -/
  restriction_injective : Function.Injective
    (mazurConstantFlatBadFiberRestriction coeffPrime level)

namespace MazurConstantFlatBadFiberClosedFiberControl

/-- A comparison which splits the actual cokernel projection is injective. -/
theorem comparison_injective
    {coeffPrime level : ℕ} [NeZero coeffPrime]
    (C : MazurConstantFlatBadFiberClosedFiberControl coeffPrime level) :
    Function.Injective C.comparison := by
  intro x y hxy
  apply_fun
    (mazurConstantFlatClosedFiberCokernelProjection coeffPrime level) at hxy
  simpa only [← MonoidHom.comp_apply, C.projection_comp_comparison,
    MonoidHom.id_apply] using hxy

/-- Closed-fibre control supplies the requested upper bound on the actual global cokernel
section group; no finiteness premise on that group is accepted. -/
def boundedData
    {coeffPrime level : ℕ} [NeZero coeffPrime]
    (C : MazurConstantFlatBadFiberClosedFiberControl coeffPrime level)
    (hlevel : level.Prime) :
    FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime level) := by
  exact
    (mazurConstantFlatClosedFiberAmbientHZeroCertifiedData
      coeffPrime level hlevel).toBoundedData.ofInjective
        (C.comparison.comp
          (mazurConstantFlatBadFiberRestriction coeffPrime level))
        (C.comparison_injective.comp C.restriction_injective)

@[simp]
theorem boundedData_length
    {coeffPrime level : ℕ} [NeZero coeffPrime]
    (C : MazurConstantFlatBadFiberClosedFiberControl coeffPrime level)
    (hlevel : level.Prime) :
    (C.boundedData hlevel).length = 1 :=
  rfl

/-- The selected auxiliary fibre at `5` supplies a length-one bound from closed-fibre control. -/
def boundedDataAtFive
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (C : MazurConstantFlatBadFiberClosedFiberControl coeffPrime 5) :
    FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime 5) :=
  C.boundedData (by decide)

/-- The order-35 auxiliary fibre at `11` supplies the same length-one bound. -/
def boundedDataAtEleven
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (C : MazurConstantFlatBadFiberClosedFiberControl coeffPrime 11) :
    FinitePGroup.BoundedData coeffPrime
      (MazurConstantFlatBadFiberHZero coeffPrime 11) :=
  C.boundedData (by decide)

@[simp]
theorem boundedDataAtFive_length
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (C : MazurConstantFlatBadFiberClosedFiberControl coeffPrime 5) :
    (C.boundedDataAtFive coeffPrime).length = 1 :=
  rfl

@[simp]
theorem boundedDataAtEleven_length
    (coeffPrime : ℕ) [NeZero coeffPrime]
    (C : MazurConstantFlatBadFiberClosedFiberControl coeffPrime 11) :
    (C.boundedDataAtEleven coeffPrime).length = 1 :=
  rfl

end MazurConstantFlatBadFiberClosedFiberControl

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
