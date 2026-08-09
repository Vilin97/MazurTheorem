/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspDifferentialQExpansion
import MazurTorsion.ModularCurve.AffineCuspPolynomialQCoordinate
import MazurTorsion.ModularCurve.EisensteinDifferentialQExpansion
import MazurTorsion.ModularCurve.NeronSectionSpecialization

/-!
# Arithmetic consumers of constructed cusp coordinates and eigen-differentials

This file is the downstream consumer of the completed polynomial cusp coordinate, the canonical
positive-index weight-two q-Hecke operator, and section specialization through a Néron model.
The local theorem supplies no DVR, uniformizer, cotangent, residue-field, or completion-coordinate
hypothesis: all of that data is constructed from one affine presentation.

For the order-35 endpoint the quotient map factors, near the cusp, through an affine open of its
Néron model.  The local q-expansion proves formal immersion into that open; invariance of completed
stalks under the open immersion transfers it to the actual quotient map.  The Néron specialization
consumer then derives the whole quotient-section collision from residue-fibre equality and
injectivity on torsion.  Since 5 divides 35, the order-35 endpoint correctly uses auxiliary prime
11; the prime-order companion uses auxiliary prime 5.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open Ideal.Fiber
open MazurTorsion.ModularCurve.AffineCuspQExpansion

namespace AlgebraicGeometry

universe u

private theorem localCompletion_map_congr
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f g : A →+* B) [IsLocalHom f] [IsLocalHom g] (h : f = g) :
    LocalCompletion.map f = LocalCompletion.map g := by
  subst g
  rfl

/-- An open immersion induces an isomorphism on the completed stalk at every source point and is
therefore a formal immersion there. -/
theorem isFormalImmersionAt_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsFormalImmersionAt f x := by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  change Function.Surjective (LocalCompletion.map e.toRingHom)
  letI : IsLocalHom e.toRingHom :=
    ⟨fun a ha ↦ (isLocalHom_equiv e).map_nonunit a ha⟩
  letI : IsLocalHom e.symm.toRingHom :=
    ⟨fun a ha ↦ (isLocalHom_equiv e.symm).map_nonunit a ha⟩
  intro y
  refine ⟨LocalCompletion.map e.symm.toRingHom y, ?_⟩
  change LocalCompletion.map e.toRingHom
      (LocalCompletion.map e.symm.toRingHom y) = y
  rw [← RingHom.comp_apply, ← LocalCompletion.map_comp]
  have he : e.toRingHom.comp e.symm.toRingHom =
      RingHom.id (X.presheaf.stalk x) := by
    ext a
    exact e.apply_symm_apply a
  have hmap := localCompletion_map_congr
    (e.toRingHom.comp e.symm.toRingHom)
    (RingHom.id (X.presheaf.stalk x)) he
  rw [hmap, LocalCompletion.map_id]
  rfl

end AlgebraicGeometry

namespace MazurTorsion.ModularCurve.AffineCuspPolynomialChart
namespace AffinePresentation

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The represented affine cusp chart as a scheme over its coefficient base. -/
def sourceOver (R T : Type u) [CommRing R] [CommRing T] [Algebra R T] :
    Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- The transported zero section, bundled as a point of the represented affine cusp over its
base. -/
noncomputable def zeroSectionOver (C : AffinePresentation R T) :
    Over.mk (𝟙 (Spec (.of R))) ⟶ sourceOver R T :=
  Over.homMk C.zeroSection.toSpec C.zeroSection.isSection

@[simp]
theorem zeroSectionOver_left (C : AffinePresentation R T) :
    C.zeroSectionOver.left = C.zeroSection.toSpec :=
  rfl

/-- The constructed completed q-coordinate on an affine polynomial cusp chart feeds the honest
first-order eigen-differential criterion. -/
theorem isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion
    [IsNoetherianRing R] [IsNoetherianRing S]
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (sourceParameter : Localization.AtPrime
      ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g))))
    (F Omega : PowerSeries p.ResidueField)
    (hqExpansion :
      C.qCoordinate p
          (completionRingHom (C.CuspLocalRing p)
            (localizedMap p g (C.zeroSection.fiberPrime p)
              sourceParameter)) = F)
    (scale : p.ResidueField) (hscale : scale ≠ 0)
    (hfirstOrder : PowerSeries.coeff 1 Omega =
      scale * PowerSeries.coeff 1 F)
    (hOmega : Omega ≠ 0)
    (hconstant : PowerSeries.coeff 0 Omega = 0)
    (level : {n : ℕ // 0 < n})
    (eigenvalue : {n : ℕ // 0 < n} → p.ResidueField)
    (heigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n Omega =
        eigenvalue n • Omega) :
    IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.zeroSection.fiberPrime p)) := by
  letI : IsNoetherianRing T := C.isNoetherianRing
  letI : IsNoetherianRing (p.Fiber T) := C.fiberIsNoetherianRing p
  exact
    isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion_of_structuralSection
      p g C.zeroSection (C.qParameter p)
      (C.maximalIdeal_eq_span_qParameter p)
      (C.qParameter_not_mem_maximalIdeal_sq p) sourceParameter hsourceMem
      (C.qCoordinate p) F Omega hqExpansion scale hscale hfirstOrder hOmega
      hconstant level eigenvalue heigen

/-- Elliptic-quotient specialization: the invariant eigen-differential is a unit multiple of the
differential of the pulled-back local parameter. -/
theorem
    isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion_of_unitMultiple
    [IsNoetherianRing R] [IsNoetherianRing S]
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (sourceParameter : Localization.AtPrime
      ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g))))
    (F Omega U : PowerSeries p.ResidueField)
    (hqExpansion :
      C.qCoordinate p
          (completionRingHom (C.CuspLocalRing p)
            (localizedMap p g (C.zeroSection.fiberPrime p)
              sourceParameter)) = F)
    (hDifferential : Omega =
      U * HeckeDifferentialQExpansion.logarithmicDerivativeExpansion F)
    (hunitConstant : PowerSeries.coeff 0 U ≠ 0)
    (hOmega : Omega ≠ 0)
    (level : {n : ℕ // 0 < n})
    (eigenvalue : {n : ℕ // 0 < n} → p.ResidueField)
    (heigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n Omega =
        eigenvalue n • Omega) :
    IsFormalImmersionAt
      (Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.zeroSection.fiberPrime p)) := by
  have hfirstOrder : PowerSeries.coeff 1 Omega =
      PowerSeries.coeff 0 U * PowerSeries.coeff 1 F := by
    rw [hDifferential,
      HeckeDifferentialQExpansion.coeff_one_mul_logarithmicDerivativeExpansion]
  have hconstant : PowerSeries.coeff 0 Omega = 0 := by
    rw [hDifferential, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply U]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply
      (HeckeDifferentialQExpansion.logarithmicDerivativeExpansion F)]
    rw [HeckeDifferentialQExpansion.coeff_zero_logarithmicDerivativeExpansion,
      mul_zero]
  exact C.isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion
    p g sourceParameter hsourceMem F Omega hqExpansion
      (PowerSeries.coeff 0 U) hunitConstant hfirstOrder hOmega hconstant
      level eigenvalue heigen

/-- A q-expansion on an affine target neighbourhood proves formal immersion for the actual
quotient map into the ambient model.  The open immersion contributes an isomorphism on completed
stalks. -/
theorem isFormalImmersionAt_of_affineOpen_weightTwoHeckeEigenDifferential_qExpansion
    {Y : Scheme.{u}} [IsNoetherianRing R] [IsNoetherianRing S]
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (targetOpen : Spec (.of S) ⟶ Y) [IsOpenImmersion targetOpen]
    (quotientMap : Spec (.of T) ⟶ Y)
    (hfactor : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen =
      quotientMap)
    (sourceParameter : Localization.AtPrime
      ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g))))
    (F Omega U : PowerSeries p.ResidueField)
    (hqExpansion :
      C.qCoordinate p
          (completionRingHom (C.CuspLocalRing p)
            (localizedMap p g (C.zeroSection.fiberPrime p)
              sourceParameter)) = F)
    (hDifferential : Omega =
      U * HeckeDifferentialQExpansion.logarithmicDerivativeExpansion F)
    (hunitConstant : PowerSeries.coeff 0 U ≠ 0)
    (hOmega : Omega ≠ 0)
    (level : {n : ℕ // 0 < n})
    (eigenvalue : {n : ℕ // 0 < n} → p.ResidueField)
    (heigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n Omega =
        eigenvalue n • Omega) :
    IsFormalImmersionAt quotientMap
      (targetSpecPoint p (C.zeroSection.fiberPrime p)) := by
  have hlocal :=
    C.isFormalImmersionAtSpecMap_of_weightTwoHeckeEigenDifferential_qExpansion_of_unitMultiple
      p g sourceParameter hsourceMem F Omega U hqExpansion hDifferential
      hunitConstant hOmega level eigenvalue heigen
  have hopen := isFormalImmersionAt_of_isOpenImmersion targetOpen
    ((Spec.map (CommRingCat.ofHom g.toRingHom))
      (targetSpecPoint p (C.zeroSection.fiberPrime p)))
  have hcomposite := hlocal.comp hopen
  rw [hfactor] at hcomposite
  exact hcomposite

/-- The canonical restricted-divisor-sum Eisenstein differential removes every abstract
eigenvector premise from the affine-open criterion.  The remaining differential equality is
precisely the geometric q-expansion realization that a modular quotient must supply. -/
theorem isFormalImmersionAt_of_affineOpen_eisensteinDifferential_qExpansion
    {Y : Scheme.{u}} [IsNoetherianRing R] [IsNoetherianRing S]
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime]
    (g : S →ₐ[R] T)
    (targetOpen : Spec (.of S) ⟶ Y) [IsOpenImmersion targetOpen]
    (quotientMap : Spec (.of T) ⟶ Y)
    (hfactor : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen =
      quotientMap)
    (sourceParameter : Localization.AtPrime
      ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.zeroSection.fiberPrime p).comap (Ideal.Fiber.map p g))))
    (level : {n : ℕ // 0 < n})
    (F U : PowerSeries p.ResidueField)
    (hqExpansion :
      C.qCoordinate p
          (completionRingHom (C.CuspLocalRing p)
            (localizedMap p g (C.zeroSection.fiberPrime p)
              sourceParameter)) = F)
    (hDifferential :
      EisensteinDifferentialQExpansion.eisensteinDifferentialExpansion level =
        U * HeckeDifferentialQExpansion.logarithmicDerivativeExpansion F)
    (hunitConstant : PowerSeries.coeff 0 U ≠ 0) :
    IsFormalImmersionAt quotientMap
      (targetSpecPoint p (C.zeroSection.fiberPrime p)) := by
  exact C.isFormalImmersionAt_of_affineOpen_weightTwoHeckeEigenDifferential_qExpansion
    p g targetOpen quotientMap hfactor sourceParameter hsourceMem
    F (EisensteinDifferentialQExpansion.eisensteinDifferentialExpansion level) U
    hqExpansion hDifferential hunitConstant
    (EisensteinDifferentialQExpansion.eisensteinDifferentialExpansion_ne_zero level)
    level (EisensteinDifferentialQExpansion.eisensteinHeckeEigenvalue level)
    (EisensteinDifferentialQExpansion.eisensteinDifferentialExpansion_simultaneousEigen level)

end AffinePresentation
end MazurTorsion.ModularCurve.AffineCuspPolynomialChart

namespace MazurTorsion.OrderThirtyFive

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open MazurTorsion.ModularCurve.AffineCuspPolynomialChart
open MazurTorsion.ModularCurve.AffineCuspPolynomialChart.AffinePresentation
open WeierstrassCurve.Affine

private abbrev ElevenBase := atEleven.adicCompletionIntegers ℚ

private abbrev ElevenPrime : Ideal ElevenBase :=
  affineCuspSpecialFiberIdealAtEleven

private def thirtyFiveLevel : {n : ℕ // 0 < n} :=
  ⟨35, by norm_num⟩

/-- The constructed q-coordinate and the explicit level-35 restricted-divisor-sum
eigen-differential reach the order-35 exclusion through an affine target neighbourhood and Néron
specialization.

Unlike the older affine consumer, this theorem does not take a completion coordinate, cusp DVR,
abstract eigenvector, eigenvalue family, eigen proof, formal immersion, distinct integral sections,
or equality after the quotient.  The affine calculation constructs the local data and formal
immersion; generic distinctness gives integral distinctness; and the Néron torsion argument derives
equality after the quotient from residue-fibre specialization.
-/
theorem
    rationalPoint_orderThirtyFive_ne_of_affineEisensteinDifferentialNeronSpecializationAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : CommGroupScheme (Spec (.of (atEleven.adicCompletion ℚ)))}
    (Ner : NeronModel ElevenBase (atEleven.adicCompletion ℚ) A)
    {S T : Type} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    [IsNoetherianRing S]
    (C : AffinePresentation ElevenBase T)
    (g : S →ₐ[ElevenBase] T)
    (targetOpen : Spec (.of S) ⟶ Ner.model.X.left)
    [IsOpenImmersion targetOpen]
    (quotientMap : sourceOver ElevenBase T ⟶ Ner.model.X)
    (hfactor :
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen = quotientMap.left)
    (modularSection :
      Over.mk (𝟙 (Spec (.of ElevenBase))) ⟶ sourceOver ElevenBase T)
    (sourceParameter : Localization.AtPrime
      ((C.zeroSection.fiberPrime ElevenPrime).comap
        (Ideal.Fiber.map ElevenPrime g)))
    (hsourceMem : sourceParameter ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime
        ((C.zeroSection.fiberPrime ElevenPrime).comap
          (Ideal.Fiber.map ElevenPrime g))))
    (F U : PowerSeries ElevenPrime.ResidueField)
    (hqExpansion :
      C.qCoordinate ElevenPrime
          (completionRingHom (C.CuspLocalRing ElevenPrime)
            (localizedMap ElevenPrime g
              (C.zeroSection.fiberPrime ElevenPrime) sourceParameter)) = F)
    (hDifferential :
      EisensteinDifferentialQExpansion.eisensteinDifferentialExpansion
          thirtyFiveLevel =
        U * HeckeDifferentialQExpansion.logarithmicDerivativeExpansion F)
    (hunitConstant : PowerSeries.coeff 0 U ≠ 0)
    (hgeneric_ne :
      fractionSpecMap ElevenBase (atEleven.adicCompletion ℚ) ≫
          modularSection.left ≠
        fractionSpecMap ElevenBase (atEleven.adicCompletion ℚ) ≫
          C.zeroSectionOver.left)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      restrictBaseSection (residueSpecMap ElevenBase)
          (sourceOver ElevenBase T) modularSection =
        restrictBaseSection (residueSpecMap ElevenBase)
          (sourceOver ElevenBase T) C.zeroSectionOver)
    (htorsion : IsOfFinOrder
      (Ner.basePointRestriction (modularSection ≫ quotientMap) /
        Ner.basePointRestriction (C.zeroSectionOver ≫ quotientMap)))
    (hinjective : ∀ z :
        Over.mk (𝟙 (Spec (.of (atEleven.adicCompletion ℚ)))) ⟶ A.X,
      IsOfFinOrder z →
        Ner.basePointSpecialization (residueSpecMap ElevenBase) z = 1 →
        z = 1)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  have hformalTarget : IsFormalImmersionAt quotientMap.left
      (targetSpecPoint ElevenPrime
        (C.zeroSection.fiberPrime ElevenPrime)) :=
    C.isFormalImmersionAt_of_affineOpen_eisensteinDifferential_qExpansion
      ElevenPrime g targetOpen quotientMap.left hfactor sourceParameter
      hsourceMem thirtyFiveLevel F U hqExpansion hDifferential hunitConstant
  have hcuspPoint :
      closedFiberPointAtEleven C.zeroSectionOver.left =
        targetSpecPoint ElevenPrime
          (C.zeroSection.fiberPrime ElevenPrime) := by
    change C.zeroSection.toSpec (IsLocalRing.closedPoint ElevenBase) =
      targetSpecPoint ElevenPrime
        (C.zeroSection.fiberPrime ElevenPrime)
    simpa only [closedFiberPointAtEleven, zeroSectionOver_left,
      ElevenPrime, affineCuspSpecialFiberIdealAtEleven,
      IsLocalRing.closedPoint] using C.zeroSection.atPrime ElevenPrime
  have hformal : IsFormalImmersionAt quotientMap.left
      (closedFiberPointAtEleven C.zeroSectionOver.left) := by
    rw [hcuspPoint]
    exact hformalTarget
  exact rationalPoint_orderThirtyFive_ne_of_neronSpecializationAtEleven
    Ner (sourceOver ElevenBase T) quotientMap modularSection C.zeroSectionOver
    hformal hgeneric_ne hspecializes htorsion hinjective P

end MazurTorsion.OrderThirtyFive
