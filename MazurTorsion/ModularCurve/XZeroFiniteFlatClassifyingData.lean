/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroFiniteFlatCyclicQuotient

/-!
# Recovering rational `Gamma_0` data from a split finite-flat subgroup

This file records the inverse, point-level direction of the existing finite-flat
`Gamma_0(N)` construction.  A split finite-flat cyclic subgroup of a represented
Weierstrass group scheme has a finite cyclic group of rational points.  Its closed
immersion and the supplied comparison with Weierstrass coordinates therefore cut
out a genuine `RationalCyclicSubgroup` of exact order `N`.

For the canonical finite-flat subgroup constructed from a rational cyclic subgroup,
the recovered carrier is definitionally independent of the cyclic trivialization
and is proved to be the original carrier.  This is the strongest classifying-data
bridge below the remaining representability boundary: neither an elliptic quotient
`E/C` nor a coarse `X_0(N)` point is asserted.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

universe u

open XZeroModuli

variable {K : Type u} [Field K] [DecidableEq K]
  {N : ℕ} [NeZero N]
  {W : WeierstrassCurve K} [W.IsElliptic]

namespace WeierstrassGroupSchemeInterface

noncomputable local instance classifyingDataRationalCyclicSubgroupFintype
    (C : RationalCyclicSubgroup W.toAffine.Point N) : Fintype C.carrier :=
  Fintype.ofFinite C.carrier

/-- Rational points of the carrier of an arbitrary split finite-flat subgroup. -/
abbrev SplitSubgroupRationalPoint
    (M : WeierstrassGroupSchemeInterface W)
    (D : SplitGammaZeroDatum W M (N := N)) :=
  Additive (D.subgroup.carrier.Point
    (AffineCommGroupScheme.testObject (R := K) K))

/-- A chosen split trivialization.  Its choice affects the auxiliary equivalence
below, but not the subgroup image used to recover rational moduli data. -/
noncomputable def splitTrivialization
    (M : WeierstrassGroupSchemeInterface W)
    (D : SplitGammaZeroDatum W M (N := N)) :
    D.subgroup.carrier ≅ cyclicConstant K N :=
  D.subgroup.isSplit.some

/-- The rational points of a split carrier form the standard cyclic group of
order `N`. -/
noncomputable def splitSubgroupPointAddEquiv
    (M : WeierstrassGroupSchemeInterface W)
    (D : SplitGammaZeroDatum W M (N := N)) :
    SplitSubgroupRationalPoint M D ≃+
      Additive (CyclicIndex.{u} N) :=
  (AlgebraicGeometry.FiniteFlatCommGroupScheme.pointMulEquivOfIso
      (splitTrivialization M D)
      (AffineCommGroupScheme.testObject (R := K) K)).toAdditive.trans
    (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantPointMulEquiv_of_noZeroDivisors
      K (CyclicIndex.{u} N)).symm.toAdditive

/-- The point homomorphism induced by the actual finite-flat closed immersion,
transported back to Weierstrass coordinates. -/
def splitSubgroupCoordinatePointHom
    (M : WeierstrassGroupSchemeInterface W)
    (D : SplitGammaZeroDatum W M (N := N)) :
    SplitSubgroupRationalPoint M D →+ W.toAffine.Point :=
  (rationalPointAddEquiv M).symm.toAddMonoidHom.comp
    (CommGroupScheme.mapPoint D.subgroup.inclusion
      (AffineCommGroupScheme.testObject (R := K) K)).toAdditive

omit [W.IsElliptic] in
/-- Closedness of the subgroup immersion makes its map on rational points
injective. -/
theorem splitSubgroupCoordinatePointHom_injective
    (M : WeierstrassGroupSchemeInterface W)
    (D : SplitGammaZeroDatum W M (N := N)) :
    Function.Injective (splitSubgroupCoordinatePointHom M D) := by
  haveI : IsClosedImmersion
      (CommGroupScheme.underlyingHom D.subgroup.inclusion) :=
    D.subgroup.inclusion_isClosedImmersion
  haveI : Mono (CommGroupScheme.underlyingHom D.subgroup.inclusion) := inferInstance
  haveI : Mono D.subgroup.inclusion.hom.hom.hom :=
    Over.mono_of_mono_left _
  intro x y hxy
  apply (cancel_mono D.subgroup.inclusion.hom.hom.hom).1
  apply Additive.toMul.injective
  exact (rationalPointAddEquiv M).symm.injective hxy

/-- The coordinate-point image of an arbitrary split finite-flat subgroup is a
rational cyclic subgroup of exact order `N`. -/
noncomputable def rationalCyclicSubgroupOfSplitGammaZeroDatum
    (M : WeierstrassGroupSchemeInterface W)
    (D : SplitGammaZeroDatum W M (N := N)) :
    RationalCyclicSubgroup W.toAffine.Point N where
  carrier := (splitSubgroupCoordinatePointHom M D).range
  isAddCyclic := by
    let e : Additive (Multiplicative (ZMod N)) ≃+
        Additive (CyclicIndex.{u} N) :=
      MulEquiv.ulift.symm.toAdditive
    letI : IsAddCyclic (Additive (CyclicIndex.{u} N)) :=
      isAddCyclic_of_surjective e.toAddMonoidHom e.surjective
    letI : IsAddCyclic (SplitSubgroupRationalPoint M D) :=
      isAddCyclic_of_surjective
        (splitSubgroupPointAddEquiv M D).symm.toAddMonoidHom
        (splitSubgroupPointAddEquiv M D).symm.surjective
    apply isAddCyclic_of_surjective
      (splitSubgroupCoordinatePointHom M D).rangeRestrict
    exact AddMonoidHom.rangeRestrict_surjective _
  card_eq := by
    calc
      Nat.card (splitSubgroupCoordinatePointHom M D).range =
          Nat.card (SplitSubgroupRationalPoint M D) :=
        (Nat.card_congr
          (Equiv.ofInjective (splitSubgroupCoordinatePointHom M D)
            (splitSubgroupCoordinatePointHom_injective M D))).symm
      _ = Nat.card (Additive (CyclicIndex.{u} N)) :=
        Nat.card_congr (splitSubgroupPointAddEquiv M D).toEquiv
      _ = N := by
        change Nat.card (ULift (ZMod N)) = N
        rw [Nat.card_ulift]
        simp

/-- Forget a represented split finite-flat `Gamma_0(N)` datum to the checked raw
rational moduli datum. -/
noncomputable def rationalDatumOfSplitGammaZeroDatum
    (M : WeierstrassGroupSchemeInterface W)
    (D : SplitGammaZeroDatum W M (N := N)) :
  RationalDatum K N :=
  RationalDatum.datumOfRationalCyclicSubgroup W
    (rationalCyclicSubgroupOfSplitGammaZeroDatum M D)

omit [W.IsElliptic] in
/-- On the canonical finite-flat datum attached to a coordinate subgroup, the
recovered coordinate map sends the distinguished constant point indexed by
`z` to `z` itself. -/
@[simp]
theorem splitSubgroupCoordinatePointHom_ofRationalCyclicSubgroup_apply
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N)
    (z : C.carrier) :
    splitSubgroupCoordinatePointHom M
        (splitGammaZeroDatumOfRationalCyclicSubgroup W M C)
        (Additive.ofMul
          (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
            K (Multiplicative C.carrier) (Multiplicative.ofAdd z))) =
      (z : W.toAffine.Point) := by
  change Multiplicative.toAdd
      (M.rationalPointEquiv.symm
        (CommGroupScheme.mapPoint
          (splitGammaZeroDatumOfRationalCyclicSubgroup W M C).subgroup.inclusion
          (AffineCommGroupScheme.testObject (R := K) K)
          (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
            K (Multiplicative C.carrier) (Multiplicative.ofAdd z)))) = z
  rw [splitGammaZeroDatumOfRationalCyclicSubgroup_map_constantPoint]
  exact congrArg Multiplicative.toAdd
    (M.rationalPointEquiv.symm_apply_apply
      (rationalCyclicSubgroupParameterization W C (Multiplicative.ofAdd z)))

omit [W.IsElliptic] in
/-- The rational-point carrier recovered from the canonical finite-flat
construction is exactly the original coordinate subgroup.  In particular it
does not depend on the cyclic trivialization chosen to prove splitness. -/
theorem rationalCyclicSubgroupOfSplitGammaZeroDatum_carrier_ofRationalCyclicSubgroup
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N) :
    (rationalCyclicSubgroupOfSplitGammaZeroDatum M
        (splitGammaZeroDatumOfRationalCyclicSubgroup W M C)).carrier =
      C.carrier := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨z, hz⟩ :=
      AlgebraicGeometry.FiniteFlatCommGroupScheme.constantPoint_surjective_of_noZeroDivisors
        K (Multiplicative C.carrier) y.toMul
    have hy : y = Additive.ofMul
        (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
          K (Multiplicative C.carrier) z) := by
      apply Additive.toMul.injective
      exact hz.symm
    rw [hy]
    change Multiplicative.toAdd
        (M.rationalPointEquiv.symm
          (CommGroupScheme.mapPoint
            (splitGammaZeroDatumOfRationalCyclicSubgroup W M C).subgroup.inclusion
            (AffineCommGroupScheme.testObject (R := K) K)
            (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
              K (Multiplicative C.carrier) z))) ∈ C.carrier
    rw [splitGammaZeroDatumOfRationalCyclicSubgroup_map_constantPoint]
    rw [M.rationalPointEquiv.symm_apply_apply]
    exact (Multiplicative.toAdd z).property
  · intro x hx
    let z : C.carrier := ⟨x, hx⟩
    refine ⟨Additive.ofMul
      (AlgebraicGeometry.FiniteFlatCommGroupScheme.constantGeometricPoint
        K (Multiplicative C.carrier) (Multiplicative.ofAdd z)), ?_⟩
    exact splitSubgroupCoordinatePointHom_ofRationalCyclicSubgroup_apply M C z

omit [W.IsElliptic] in
/-- Constructing finite-flat `Gamma_0(N)` data from a rational subgroup and
then recovering coordinate data returns the original rational subgroup. -/
theorem rationalCyclicSubgroupOfSplitGammaZeroDatum_ofRationalCyclicSubgroup
    (M : WeierstrassGroupSchemeInterface W)
    (C : RationalCyclicSubgroup W.toAffine.Point N) :
    rationalCyclicSubgroupOfSplitGammaZeroDatum M
        (splitGammaZeroDatumOfRationalCyclicSubgroup W M C) = C := by
  apply RationalCyclicSubgroup.ext
  exact
    rationalCyclicSubgroupOfSplitGammaZeroDatum_carrier_ofRationalCyclicSubgroup M C

/-- The finite-flat construction followed by coordinate recovery is a section
of the forgetful map on every checked raw rational `Gamma_0(N)` datum. -/
theorem rationalDatumOfSplitGammaZeroDatum_ofRationalDatum
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :
    rationalDatumOfSplitGammaZeroDatum M
        (splitGammaZeroDatumOfRationalDatum x M) = x := by
  cases x with
  | mk curve isElliptic subgroup =>
      change RationalDatum.datumOfRationalCyclicSubgroup curve
          (rationalCyclicSubgroupOfSplitGammaZeroDatum M
            (splitGammaZeroDatumOfRationalCyclicSubgroup curve M subgroup)) =
        { curve := curve, isElliptic := isElliptic, subgroup := subgroup }
      rw [rationalCyclicSubgroupOfSplitGammaZeroDatum_ofRationalCyclicSubgroup]
      have hp :
          (RationalDatum.datumOfRationalCyclicSubgroup curve subgroup).isElliptic =
            isElliptic := Subsingleton.elim _ _
      cases hp
      rfl

end WeierstrassGroupSchemeInterface

end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
