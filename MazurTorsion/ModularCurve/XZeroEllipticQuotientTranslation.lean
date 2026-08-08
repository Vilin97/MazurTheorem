/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteTranslationQuotientGroup
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfConnecting
import MazurTorsion.ModularCurve.XZeroFiniteFlatCyclicQuotient
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Translation actions attached to rational cyclic subgroups

This file turns the distinguished sections of the already constructed split constant subgroup
into a free finite-group action on the ambient Weierstrass group scheme.

The translation action is the one constructed in
`FiniteTranslationQuotientGroup`: using that same definition here makes the
stable atlas, freeness proof, quotient scheme, and descended group law share a
literal action rather than merely extensionally equal actions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open AlgebraicGeometry

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassGroupSchemeInterface
namespace EllipticQuotient

universe u

open XZeroModuli
open AlgebraicGeometry.FiniteTranslationQuotient

variable {K : Type u} [Field K] [DecidableEq K]
  {N : ℕ} [NeZero N]
  {W : WeierstrassCurve K} [W.IsElliptic]

noncomputable local instance rationalCyclicSubgroupFintype
    (C : RationalCyclicSubgroup W.toAffine.Point N) : Fintype C.carrier :=
  Fintype.ofFinite C.carrier

/-- The actual subgroup sections, transported from the affine self-test object to the terminal
object of the slice.  These are the sections used by the translation action. -/
noncomputable def rationalCyclicSubgroupSectionHom
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N) :
    Multiplicative C.carrier →* (𝟙_ (Over (Spec (.of K))) ⟶ M.groupScheme.X) :=
  (CommGroupScheme.pointMulEquivOfOverIso M.groupScheme
      (AffineCommGroupScheme.baseIsoSelfTestObject K)).symm.toMonoidHom.comp <|
    M.rationalPointEquiv.toMonoidHom.comp
      (rationalCyclicSubgroupParameterization W C)

omit [W.IsElliptic] in
/-- Distinct elements of the rational cyclic subgroup give distinct geometric sections. -/
theorem rationalCyclicSubgroupSectionHom_injective
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N) :
    Function.Injective (rationalCyclicSubgroupSectionHom M C) :=
  (CommGroupScheme.pointMulEquivOfOverIso M.groupScheme
      (AffineCommGroupScheme.baseIsoSelfTestObject K)).symm.injective.comp <|
    M.rationalPointEquiv.injective.comp <|
      rationalCyclicSubgroupParameterization_injective W C

omit [W.IsElliptic] in
/-- The translating section is literally the corresponding distinguished point of the checked
finite-flat subgroup, followed by its closed immersion into the ambient group scheme. -/
theorem rationalCyclicSubgroupSectionHom_eq_map_constantPoint
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N)
    (z : Multiplicative C.carrier) :
    rationalCyclicSubgroupSectionHom M C z =
      (CommGroupScheme.pointMulEquivOfOverIso M.groupScheme
        (AffineCommGroupScheme.baseIsoSelfTestObject K)).symm
        (CommGroupScheme.mapPoint
          (splitGammaZeroDatumOfRationalCyclicSubgroup W M C).subgroup.inclusion
          (AffineCommGroupScheme.testObject (R := K) K)
          (FiniteFlatCommGroupScheme.constantGeometricPoint K
            (Multiplicative C.carrier) z)) := by
  change (CommGroupScheme.pointMulEquivOfOverIso M.groupScheme
      (AffineCommGroupScheme.baseIsoSelfTestObject K)).symm
      (M.rationalPointEquiv (rationalCyclicSubgroupParameterization W C z)) =
    (CommGroupScheme.pointMulEquivOfOverIso M.groupScheme
      (AffineCommGroupScheme.baseIsoSelfTestObject K)).symm _
  congr 1
  exact (splitGammaZeroDatumOfRationalCyclicSubgroup_map_constantPoint
    W M C z).symm

/-- The finite translation action of the rational cyclic subgroup on the represented elliptic
curve.  Its underlying endomorphisms are genuine translations by the subgroup sections. -/
noncomputable abbrev rationalCyclicSubgroupAction
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N) :
    SchemeAction (Multiplicative C.carrier) M.groupScheme.X.left :=
  translationAction M.groupScheme (rationalCyclicSubgroupSectionHom M C)

omit [W.IsElliptic] in
/-- Translation by a nonidentity member of the rational cyclic subgroup has no fixed point after
arbitrary scheme-valued extension.  This is the freeness condition used by the finite quotient
construction, proved from injectivity of the actual subgroup sections. -/
theorem rationalCyclicSubgroupAction_free
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N) :
    ∀ g : Multiplicative C.carrier, g ≠ 1 →
      ∀ (T : Scheme.{u}) (t : T ⟶ M.groupScheme.X.left),
        t ≫ (rationalCyclicSubgroupAction M C).hom g = t → IsEmpty T := by
  intro g hg T t hfixed
  let T' : Over (Spec (.of K)) := Over.mk (t ≫ M.groupScheme.X.hom)
  let t' : T' ⟶ M.groupScheme.X := Over.homMk t rfl
  let sg : 𝟙_ (Over (Spec (.of K))) ⟶ M.groupScheme.X :=
    rationalCyclicSubgroupSectionHom M C g
  have hfixed' : t' ≫ translateBy M.groupScheme sg = t' := by
    apply Over.OverMorphism.ext
    exact hfixed
  letI : CommGroup (T' ⟶ M.groupScheme.X) := Hom.commGroup
  have hsgT : toUnit T' ≫ sg = (1 : T' ⟶ M.groupScheme.X) := by
    have hmul := hfixed'
    rw [translateBy_def, MonObj.comp_mul, Category.comp_id,
      comp_constSection] at hmul
    apply mul_left_cancel (a := t')
    simpa only [_root_.mul_one] using hmul
  refine ⟨fun z ↦ hg ?_⟩
  apply rationalCyclicSubgroupSectionHom_injective M C
  rw [map_one]
  apply Over.OverMorphism.ext
  apply section_eq_of_apply_closedPoint_eq M.groupScheme.X.hom
  · exact sg.w
  · exact (1 : 𝟙_ (Over (Spec (.of K))) ⟶ M.groupScheme.X).w
  · letI : Subsingleton (𝟙_ (Over (Spec (.of K)))).left := by
      change Subsingleton (PrimeSpectrum K)
      exact Ring.KrullDimLE.subsingleton_primeSpectrum K
    have hz := congrArg (fun f : T' ⟶ M.groupScheme.X ↦ f.left z) hsgT
    have hbase : (toUnit T').left z = IsLocalRing.closedPoint K :=
      Subsingleton.elim _ _
    change sg.left ((toUnit T').left z) =
      (η[M.groupScheme.X]).left ((toUnit T').left z) at hz
    change (rationalCyclicSubgroupSectionHom M C g).left
        (IsLocalRing.closedPoint K) =
      (η[M.groupScheme.X]).left (IsLocalRing.closedPoint K)
    simpa only [hbase, sg] using hz

end EllipticQuotient
end WeierstrassGroupSchemeInterface
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
