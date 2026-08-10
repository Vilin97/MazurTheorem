/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTildeTensorOverlapNaturality
import MazurTorsion.Upstream.AffineDivisorTildeTensorPullbackSection

/-!
# Cross-chart naturality of chosen divisor restriction tensor addition

The deterministic tensor/addition maps on two affine charts commute with the chosen
equality-induced restriction comparisons on a common affine open.  The proof combines the
one-leg restriction/pullback square with multiplication naturality for the raw extended
inverse-ideal tilde sheaves.
-/

namespace MazurTorsion.AlgebraicGeometry

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

universe u

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForRestrictionOverlapNaturality
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

namespace AffineDivisorLocalization.CommonExtension

/-- The chosen equality-induced restriction comparisons commute with deterministic divisor
addition on a common affine open.  The sum comparison is the canonical one derived from the two
factorwise overlap equalities. -/
theorem lineBundleAddIso_restrict_viaPullback_naturality
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (extensionMap R₁ B)]
    [IsOpenImmersion (extensionMap R₂ B)]
    (D₁ E₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ E₂ : WeilDivisor (HeightOneSpectrum R₂))
    (hD : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂)
    (hE : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K E₁ E₂) :
    let hDE := Boundary.overlapInverseIdealExtensionEq_add
      R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
    (((Scheme.Modules.restrictFunctor (extensionMap R₁ B)).mapIso
          (ExplicitIdeal.lineBundleAddIso R₁ K D₁ E₁) ≪≫
        lineBundleTensorRestrictionIsoViaPullback R₁ B K D₁ E₁) ≪≫
        (chosenLineBundleRestrictionIsoOfOverlapExtensionEq
              R₁ R₂ B K D₁ D₂ hD ⊗ᵢ
          chosenLineBundleRestrictionIsoOfOverlapExtensionEq
              R₁ R₂ B K E₁ E₂ hE)) =
      chosenLineBundleRestrictionIsoOfOverlapExtensionEq
          R₁ R₂ B K (D₁ + E₁) (D₂ + E₂) hDE ≪≫
        ((Scheme.Modules.restrictFunctor (extensionMap R₂ B)).mapIso
            (ExplicitIdeal.lineBundleAddIso R₂ K D₂ E₂) ≪≫
          lineBundleTensorRestrictionIsoViaPullback R₂ B K D₂ E₂) := by
  dsimp only
  letI : IsScalarTower R₁ B K := hD.1
  letI : IsScalarTower R₂ B K := hD.2.1
  letI : Algebra.IsEpi R₁ B := algebraIsEpiOfOpenImmersion R₁ B
  letI : Module.Flat R₁ B := moduleFlatOfOpenImmersion R₁ B
  letI : Algebra.IsEpi R₂ B := algebraIsEpiOfOpenImmersion R₂ B
  letI : Module.Flat R₂ B := moduleFlatOfOpenImmersion R₂ B
  let F₁ := Scheme.Modules.restrictFunctor (extensionMap R₁ B)
  let F₂ := Scheme.Modules.restrictFunctor (extensionMap R₂ B)
  let a₁ := ExplicitIdeal.lineBundleAddIso R₁ K D₁ E₁
  let a₂ := ExplicitIdeal.lineBundleAddIso R₂ K D₂ E₂
  let κ₁ := lineBundleTensorRestrictionIsoViaPullback R₁ B K D₁ E₁
  let κ₂ := lineBundleTensorRestrictionIsoViaPullback R₂ B K D₂ E₂
  let A₁ := F₁.mapIso a₁ ≪≫ κ₁
  let A₂ := F₂.mapIso a₂ ≪≫ κ₂
  let ρ₁D := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₁ B K D₁
  let ρ₁E := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₁ B K E₁
  let ρ₁S := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₁ B K (D₁ + E₁)
  let ρ₂D := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₂ B K D₂
  let ρ₂E := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₂ B K E₂
  let ρ₂S := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₂ B K (D₂ + E₂)
  let ρ₁P := ρ₁D ⊗ᵢ ρ₁E
  let ρ₂P := ρ₂D ⊗ᵢ ρ₂E
  let m₁ := extendedInverseIdealAddIso R₁ B K D₁ E₁
  let m₂ := extendedInverseIdealAddIso R₂ B K D₂ E₂
  let hDE := Boundary.overlapInverseIdealExtensionEq_add
    R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
  let eD := extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ hD
  let eE := extendedInverseIdealTildeIso R₁ R₂ B K E₁ E₂ hE
  let eS := extendedInverseIdealTildeIso
    R₁ R₂ B K (D₁ + E₁) (D₂ + E₂) hDE
  let eP := eD ⊗ᵢ eE
  let tD := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    R₁ R₂ B K D₁ D₂ hD
  let tE := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    R₁ R₂ B K E₁ E₂ hE
  let tS := chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    R₁ R₂ B K (D₁ + E₁) (D₂ + E₂) hDE
  let tP := tD ⊗ᵢ tE
  change A₁ ≪≫ tP = tS ≪≫ A₂
  have hleg₁ := lineBundleAddIso_restrict_viaPullback R₁ B K D₁ E₁
  change A₁ ≪≫ ρ₁P = ρ₁S ≪≫ m₁ at hleg₁
  have hleg₂ := lineBundleAddIso_restrict_viaPullback R₂ B K D₂ E₂
  change A₂ ≪≫ ρ₂P = ρ₂S ≪≫ m₂ at hleg₂
  have hraw := extendedInverseIdealAddIso_naturality
    R₁ R₂ B K D₁ E₁ D₂ E₂ hD hE
  dsimp only at hraw
  change eS ≪≫ m₂ = m₁ ≪≫ eP at hraw
  have htD : tD.hom = ρ₁D.hom ≫ (eD.hom ≫ ρ₂D.inv) := by
    rfl
  have htE : tE.hom = ρ₁E.hom ≫ (eE.hom ≫ ρ₂E.inv) := by
    rfl
  have htP₁ := congrArg₂ (fun x y ↦ x ⊗ₘ y) htD htE
  change tP.hom =
    (ρ₁D.hom ≫ (eD.hom ≫ ρ₂D.inv)) ⊗ₘ
      (ρ₁E.hom ≫ (eE.hom ≫ ρ₂E.inv)) at htP₁
  have htP : tP.hom = ρ₁P.hom ≫ (eP.hom ≫ ρ₂P.inv) := by
    calc
      tP.hom =
          (ρ₁D.hom ≫ (eD.hom ≫ ρ₂D.inv)) ⊗ₘ
            (ρ₁E.hom ≫ (eE.hom ≫ ρ₂E.inv)) := htP₁
      _ = (ρ₁D.hom ⊗ₘ ρ₁E.hom) ≫
          ((eD.hom ≫ ρ₂D.inv) ⊗ₘ (eE.hom ≫ ρ₂E.inv)) :=
        (tensorHom_comp_tensorHom ρ₁D.hom ρ₁E.hom
          (eD.hom ≫ ρ₂D.inv) (eE.hom ≫ ρ₂E.inv)).symm
      _ = (ρ₁D.hom ⊗ₘ ρ₁E.hom) ≫
          ((eD.hom ⊗ₘ eE.hom) ≫ (ρ₂D.inv ⊗ₘ ρ₂E.inv)) :=
        congrArg ((ρ₁D.hom ⊗ₘ ρ₁E.hom) ≫ ·)
          (tensorHom_comp_tensorHom
            eD.hom eE.hom ρ₂D.inv ρ₂E.inv).symm
      _ = ρ₁P.hom ≫ (eP.hom ≫ ρ₂P.inv) := rfl
  have hleg₁Hom := congrArg (fun z ↦ z.hom) hleg₁
  change A₁.hom ≫ ρ₁P.hom = ρ₁S.hom ≫ m₁.hom at hleg₁Hom
  have hleg₂Hom := congrArg (fun z ↦ z.hom) hleg₂
  change A₂.hom ≫ ρ₂P.hom = ρ₂S.hom ≫ m₂.hom at hleg₂Hom
  have hrawHom := congrArg (fun z ↦ z.hom) hraw
  change eS.hom ≫ m₂.hom = m₁.hom ≫ eP.hom at hrawHom
  have hright : m₂.hom ≫ ρ₂P.inv = ρ₂S.inv ≫ A₂.hom := by
    apply (cancel_mono ρ₂P.hom).1
    calc
      (m₂.hom ≫ ρ₂P.inv) ≫ ρ₂P.hom =
          m₂.hom ≫ (ρ₂P.inv ≫ ρ₂P.hom) :=
        Category.assoc _ _ _
      _ = m₂.hom ≫ 𝟙 _ :=
        congrArg (m₂.hom ≫ ·) ρ₂P.inv_hom_id
      _ = m₂.hom := Category.comp_id _
      _ = 𝟙 _ ≫ m₂.hom := (Category.id_comp _).symm
      _ = (ρ₂S.inv ≫ ρ₂S.hom) ≫ m₂.hom :=
        congrArg (· ≫ m₂.hom) ρ₂S.inv_hom_id.symm
      _ = ρ₂S.inv ≫ (ρ₂S.hom ≫ m₂.hom) :=
        Category.assoc _ _ _
      _ = ρ₂S.inv ≫ (A₂.hom ≫ ρ₂P.hom) :=
        congrArg (ρ₂S.inv ≫ ·) hleg₂Hom.symm
      _ = (ρ₂S.inv ≫ A₂.hom) ≫ ρ₂P.hom :=
        (Category.assoc _ _ _).symm
  have htS : tS.hom = ρ₁S.hom ≫ (eS.hom ≫ ρ₂S.inv) := by
    rfl
  apply Iso.ext
  change A₁.hom ≫ tP.hom = tS.hom ≫ A₂.hom
  calc
    A₁.hom ≫ tP.hom =
        A₁.hom ≫ (ρ₁P.hom ≫ (eP.hom ≫ ρ₂P.inv)) :=
      congrArg (A₁.hom ≫ ·) htP
    _ = (A₁.hom ≫ ρ₁P.hom) ≫ (eP.hom ≫ ρ₂P.inv) :=
      (Category.assoc _ _ _).symm
    _ = (ρ₁S.hom ≫ m₁.hom) ≫ (eP.hom ≫ ρ₂P.inv) :=
      congrArg (· ≫ (eP.hom ≫ ρ₂P.inv)) hleg₁Hom
    _ = ρ₁S.hom ≫ (m₁.hom ≫ (eP.hom ≫ ρ₂P.inv)) :=
      Category.assoc _ _ _
    _ = ρ₁S.hom ≫ ((m₁.hom ≫ eP.hom) ≫ ρ₂P.inv) :=
      congrArg (ρ₁S.hom ≫ ·) (Category.assoc _ _ _).symm
    _ = ρ₁S.hom ≫ ((eS.hom ≫ m₂.hom) ≫ ρ₂P.inv) :=
      congrArg (fun z ↦ ρ₁S.hom ≫ (z ≫ ρ₂P.inv)) hrawHom.symm
    _ = ρ₁S.hom ≫ (eS.hom ≫ (m₂.hom ≫ ρ₂P.inv)) :=
      congrArg (ρ₁S.hom ≫ ·) (Category.assoc _ _ _)
    _ = ρ₁S.hom ≫ (eS.hom ≫ (ρ₂S.inv ≫ A₂.hom)) :=
      congrArg (fun z ↦ ρ₁S.hom ≫ (eS.hom ≫ z)) hright
    _ = ρ₁S.hom ≫ ((eS.hom ≫ ρ₂S.inv) ≫ A₂.hom) :=
      congrArg (ρ₁S.hom ≫ ·) (Category.assoc _ _ _).symm
    _ = (ρ₁S.hom ≫ (eS.hom ≫ ρ₂S.inv)) ≫ A₂.hom :=
      (Category.assoc _ _ _).symm
    _ = tS.hom ≫ A₂.hom := congrArg (· ≫ A₂.hom) htS.symm

end AffineDivisorLocalization.CommonExtension

end MazurTorsion.AlgebraicGeometry
