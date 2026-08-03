/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePointComparison
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The integral standard chart of the projective Weierstrass cubic

This file identifies the degree-zero homogeneous localization at `Z` with
Mathlib's bivariate affine coordinate ring before quotienting by the
Weierstrass equation.  Under that equivalence, the localized homogeneous
cubic is the affine Weierstrass polynomial.  Its checked irreducibility makes
the chart equation prime, and hence its quotient scheme integral.

This is the algebraic prerequisite for geometric integrality of the concrete
projective cubic.  The remaining geometric step is to identify this quotient
with the `Z != 0` open of every field base change and prove that open dense;
the reduction at the end of the file records and consumes precisely those
data in the Tau Ceti abelian-variety bridge.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj DirectSum Polynomial.Bivariate

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem coordinate_mem_degree_one_geometric (i : Fin 3) :
    MvPolynomial.X i ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K i

/-- Set the projective coordinate `Z` equal to one, with `X` and `Y` landing in
the two variables of Mathlib's affine Weierstrass polynomial ring. -/
noncomputable def dehomogenizeZ :
    MvPolynomial (Fin 3) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
      (Polynomial.C : K →+* Polynomial K))
    ![Polynomial.C Polynomial.X, Polynomial.X, 1]

@[simp]
theorem dehomogenizeZ_X_zero :
    dehomogenizeZ (K := K) (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
  simp [dehomogenizeZ]

@[simp]
theorem dehomogenizeZ_X_one :
    dehomogenizeZ (K := K) (MvPolynomial.X 1) = Polynomial.X := by
  simp [dehomogenizeZ]

@[simp]
theorem dehomogenizeZ_X_two :
    dehomogenizeZ (K := K) (MvPolynomial.X 2) = 1 := by
  simp [dehomogenizeZ]

/-- Dehomogenizing the checked projective cubic at `Z = 1` gives exactly
Mathlib's affine Weierstrass polynomial. -/
theorem dehomogenizeZ_polynomial (W : WeierstrassCurve K) :
    dehomogenizeZ W.toProjective.polynomial = W.toAffine.polynomial := by
  simp [dehomogenizeZ, WeierstrassCurve.Projective.polynomial,
    WeierstrassCurve.Affine.polynomial]
  ring

/-- The affine equation obtained from the actual homogeneous cubic is
irreducible.  This is stronger than a pointwise nonsingularity calculation and
does not require ellipticity. -/
theorem dehomogenizeZ_polynomial_irreducible (W : WeierstrassCurve K) :
    Irreducible (dehomogenizeZ W.toProjective.polynomial) := by
  rw [dehomogenizeZ_polynomial]
  exact W.toAffine.irreducible_polynomial

/-- The ring of the standard `Z != 0` chart of projective two-space. -/
abbrev standardAmbientChartRing (K : Type u) [Field K] :=
  HomogeneousLocalization.Away (homogeneousPieces K)
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) K)

/-- Map affine bivariate polynomials to the standard projective chart by
`X |-> X/Z` and `Y |-> Y/Z`. -/
noncomputable def affineToStandardChart :
    Polynomial (Polynomial K) →+* standardAmbientChartRing K :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (coordinateChartConstantHom 2)
      (coordinateChartRatio 2 0))
    (coordinateChartRatio 2 1)

/-- Evaluate a homogeneous fraction on the standard chart at `Z = 1`. -/
noncomputable def standardChartToAffine :
    standardAmbientChartRing K →+* Polynomial (Polynomial K) :=
  (IsLocalization.Away.lift (R := MvPolynomial (Fin 3) K)
      (S := Localization.Away
        (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K))
      (P := Polynomial (Polynomial K)) (g := dehomogenizeZ (K := K))
      (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) (by
        rw [dehomogenizeZ_X_two]
        exact isUnit_one)).comp
    (algebraMap (standardAmbientChartRing K)
      (Localization.Away
        (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K)))

theorem standardChartToAffine_awayMk {n : ℕ}
    (q : MvPolynomial (Fin 3) K) (hq : q ∈ homogeneousPieces K n) :
    standardChartToAffine
        (HomogeneousLocalization.Away.mk (homogeneousPieces K)
          (coordinate_mem_degree_one_geometric 2) n q (by simpa using hq)) =
      dehomogenizeZ q := by
  simp only [standardChartToAffine, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  apply (IsLocalization.lift_mk'_spec _ _ _ _).2
  simp

@[simp]
theorem standardChartToAffine_coordinateChartConstantHom (a : K) :
    standardChartToAffine (coordinateChartConstantHom 2 a) =
      Polynomial.C (Polynomial.C a) := by
  rw [coordinateChartConstantHom_apply]
  rw [standardChartToAffine_awayMk (n := 0) (MvPolynomial.C a)
    (MvPolynomial.isHomogeneous_C (R := K) (σ := Fin 3) a)]
  simp [dehomogenizeZ]

@[simp]
theorem standardChartToAffine_coordinateChartRatio_zero :
    standardChartToAffine (coordinateChartRatio (K := K) 2 0) =
      Polynomial.C Polynomial.X := by
  rw [coordinateChartRatio]
  simpa using standardChartToAffine_awayMk (n := 1)
    (MvPolynomial.X 0 : MvPolynomial (Fin 3) K)
    (MvPolynomial.isHomogeneous_X K 0)

@[simp]
theorem standardChartToAffine_coordinateChartRatio_one :
    standardChartToAffine (coordinateChartRatio (K := K) 2 1) =
      Polynomial.X := by
  rw [coordinateChartRatio]
  simpa using standardChartToAffine_awayMk (n := 1)
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) K)
    (MvPolynomial.isHomogeneous_X K 1)

@[simp]
theorem standardChartToAffine_coordinateChartRatio_two :
    standardChartToAffine (coordinateChartRatio (K := K) 2 2) = 1 := by
  rw [coordinateChartRatio]
  simpa using standardChartToAffine_awayMk (n := 1)
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) K)
    (MvPolynomial.isHomogeneous_X K 2)

@[simp]
theorem coordinateChartRatio_two_two :
    coordinateChartRatio (K := K) 2 2 = 1 := by
  rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio 2 2,
    isLocalizationElem_self_degree_one]

@[simp]
theorem affineToStandardChart_C_C (a : K) :
    affineToStandardChart (Polynomial.C (Polynomial.C a)) =
      coordinateChartConstantHom 2 a := by
  simp [affineToStandardChart]

@[simp]
theorem affineToStandardChart_C_X :
    affineToStandardChart (K := K) (Polynomial.C Polynomial.X) =
      coordinateChartRatio 2 0 := by
  simp [affineToStandardChart]

@[simp]
theorem affineToStandardChart_X :
    affineToStandardChart (K := K) Polynomial.X =
      coordinateChartRatio 2 1 := by
  simp [affineToStandardChart]

theorem standardChartToAffine_comp_affineToStandardChart :
    (standardChartToAffine (K := K)).comp affineToStandardChart = RingHom.id _ := by
  ext a <;> simp

theorem affineToStandardChart_comp_standardChartToAffine :
    (affineToStandardChart (K := K)).comp standardChartToAffine = RingHom.id _ := by
  apply chartRingHom_ext 2
  · ext a
    simp
  · intro j
    fin_cases j <;> simp

/-- The bivariate affine polynomial ring is canonically the degree-zero
homogeneous localization of `K[X,Y,Z]` at `Z`. -/
noncomputable def standardChartRingEquiv :
    Polynomial (Polynomial K) ≃+* standardAmbientChartRing K where
  toFun := affineToStandardChart
  invFun := standardChartToAffine
  left_inv := DFunLike.congr_fun standardChartToAffine_comp_affineToStandardChart
  right_inv := DFunLike.congr_fun affineToStandardChart_comp_standardChartToAffine
  map_add' := map_add affineToStandardChart
  map_mul' := map_mul affineToStandardChart

/-- The homogeneous cubic divided by `Z³`, as an element of the standard
degree-zero projective chart. -/
noncomputable def standardChartEquation (W : WeierstrassCurve K) :
    standardAmbientChartRing K :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K)
    (coordinate_mem_degree_one_geometric 2) 3 W.toProjective.polynomial
    (polynomial_mem_degree_three W)

/-- Under the chart equivalence, the localized homogeneous equation is the
affine Weierstrass polynomial. -/
theorem standardChartEquation_eq_affineToStandardChart
    (W : WeierstrassCurve K) :
    standardChartEquation W = affineToStandardChart W.toAffine.polynomial := by
  apply (standardChartRingEquiv (K := K)).symm.injective
  change standardChartToAffine (standardChartEquation W) =
    standardChartToAffine (affineToStandardChart W.toAffine.polynomial)
  rw [show standardChartToAffine (standardChartEquation W) =
      dehomogenizeZ W.toProjective.polynomial from
    standardChartToAffine_awayMk W.toProjective.polynomial
      (polynomial_mem_degree_three W)]
  rw [dehomogenizeZ_polynomial]
  exact (DFunLike.congr_fun
    (standardChartToAffine_comp_affineToStandardChart (K := K)) _).symm

/-- The principal ideal cutting out the Weierstrass cubic on the standard
affine chart. -/
def standardChartIdeal (W : WeierstrassCurve K) :
    Ideal (standardAmbientChartRing K) :=
  Ideal.span {standardChartEquation W}

theorem standardChartIdeal_eq_map (W : WeierstrassCurve K) :
    standardChartIdeal W =
      Ideal.map (standardChartRingEquiv (K := K))
        (Ideal.span {W.toAffine.polynomial}) := by
  rw [standardChartIdeal, standardChartEquation_eq_affineToStandardChart]
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

/-- The actual standard-chart equation ideal is prime.  This is the algebraic
content needed from the affine chart in the projective integrality proof. -/
instance standardChartIdeal_isPrime (W : WeierstrassCurve K) :
    (standardChartIdeal W).IsPrime := by
  rw [standardChartIdeal_eq_map]
  letI : (Ideal.span {W.toAffine.polynomial} : Ideal (Polynomial (Polynomial K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime W.toAffine.irreducible_polynomial.prime
  infer_instance

/-- Coordinate ring of the standard affine open of the projective cubic. -/
abbrev standardAffineChartCoordinateRing (W : WeierstrassCurve K) :=
  standardAmbientChartRing K ⧸ standardChartIdeal W

/-- The usual affine Weierstrass coordinate ring, retained as a named source
for the scheme-level standard-chart comparison. -/
abbrev affineWeierstrassCoordinateRing (W : WeierstrassCurve K) :=
  Polynomial (Polynomial K) ⧸ Ideal.span {W.toAffine.polynomial}

/-- The checked ambient chart equivalence descends through the actual
Weierstrass equation ideals.  Thus the source appearing in the later
base-change witness is not merely abstractly integral: it is the usual affine
Weierstrass quotient. -/
noncomputable def affineEquationToStandardChartRingEquiv
    (W : WeierstrassCurve K) :
    affineWeierstrassCoordinateRing W ≃+*
      standardAffineChartCoordinateRing W :=
  Ideal.quotientEquiv
    (Ideal.span {W.toAffine.polynomial}) (standardChartIdeal W)
    (standardChartRingEquiv (K := K)) (standardChartIdeal_eq_map W)

instance standardAffineChartCoordinateRing_isDomain (W : WeierstrassCurve K) :
    IsDomain (standardAffineChartCoordinateRing W) := by
  infer_instance

/-- The integral affine scheme supplied by the `Z != 0` chart equation. -/
abbrev standardAffineChartScheme (W : WeierstrassCurve K) : Scheme.{u} :=
  Spec (.of (standardAffineChartCoordinateRing W))

/-- Scheme-level form of `affineEquationToStandardChartRingEquiv`.  This is
the concrete source side of the still-missing identification with the
canonical `D₊(Z)` pullback open. -/
noncomputable def affineEquationSchemeIsoStandardChart
    (W : WeierstrassCurve K) :
  Spec (.of (affineWeierstrassCoordinateRing W)) ≅
      standardAffineChartScheme W :=
  Scheme.Spec.mapIso
    (affineEquationToStandardChartRingEquiv W).toCommRingCatIso.symm.op

instance standardAffineChartScheme_isIntegral (W : WeierstrassCurve K) :
    IsIntegral (standardAffineChartScheme W) := by
  infer_instance

/-- Base change of the concrete reduced projective cubic to a field
extension. -/
abbrev fieldBaseChange (W : WeierstrassCurve K) (L : Type u)
    [Field L] [Algebra K L] : Scheme.{u} :=
  pullback (structureMap W)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The projection from a field base change of the concrete cubic back to the
original cubic. -/
noncomputable def fieldBaseChangeProjection (W : WeierstrassCurve K)
    (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChange W L ⟶ scheme W :=
  pullback.fst (structureMap W)
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The projection is the first leg of the defining base-change square. -/
@[reassoc]
theorem fieldBaseChangeProjection_comp_structureMap
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChangeProjection W L ≫ structureMap W =
      pullback.snd (structureMap W)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  exact pullback.condition

/-- The field-base-changed cubic, viewed in the original projective plane.

This map is deliberately defined through the pullback projection.  Thus its
inverse image of `D₊(Z)` is the canonical standard open of the *actual*
base change used by `GeometricallyIntegral`, without first postulating an
identification with the cubic reconstructed from `W.map`. -/
noncomputable def fieldBaseChangeAmbientMap (W : WeierstrassCurve K)
    (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChange W L ⟶ projectivePlane K :=
  fieldBaseChangeProjection W L ≫ inclusion W

/-- The canonical `Z ≠ 0` open of the actual field base change, obtained by
pulling back Mathlib's checked `Proj.awayι` chart. -/
abbrev canonicalStandardOpen (W : WeierstrassCurve K) (L : Type u)
    [Field L] [Algebra K L] : Scheme.{u} :=
  pullback
    (Proj.awayι (homogeneousPieces K)
      (MvPolynomial.X (2 : Fin 3)) (coordinate_mem_degree_one_geometric 2)
      (by omega))
    (fieldBaseChangeAmbientMap W L)

/-- The canonical standard open immersed into the actual field base change. -/
noncomputable def canonicalStandardOpenMap (W : WeierstrassCurve K)
    (L : Type u) [Field L] [Algebra K L] :
    canonicalStandardOpen W L ⟶ fieldBaseChange W L :=
  pullback.snd
    (Proj.awayι (homogeneousPieces K)
      (MvPolynomial.X (2 : Fin 3)) (coordinate_mem_degree_one_geometric 2)
      (by omega))
    (fieldBaseChangeAmbientMap W L)

/-- The canonical standard open is genuinely an open subscheme of the actual
field base change.  This is the base-change-stability part supplied directly
by Mathlib's `Proj.awayι` and pullback APIs. -/
instance canonicalStandardOpenMap_isOpenImmersion (W : WeierstrassCurve K)
    (L : Type u) [Field L] [Algebra K L] :
    IsOpenImmersion (canonicalStandardOpenMap W L) := by
  dsimp only [canonicalStandardOpenMap]
  infer_instance

/-- The range of the canonical chart is exactly the inverse image of the
ambient projective `D₊(Z)` chart.  This pins down which open must be compared
with the checked principal quotient. -/
theorem canonicalStandardOpenMap_opensRange (W : WeierstrassCurve K)
    (L : Type u) [Field L] [Algebra K L] :
    (canonicalStandardOpenMap W L).opensRange =
      fieldBaseChangeAmbientMap W L ⁻¹ᵁ
        (Proj.awayι (homogeneousPieces K)
          (MvPolynomial.X (2 : Fin 3)) (coordinate_mem_degree_one_geometric 2)
          (by omega)).opensRange := by
  simpa only [canonicalStandardOpenMap] using
    (Scheme.Hom.opensRange_pullbackSnd
      (Proj.awayι (homogeneousPieces K)
        (MvPolynomial.X (2 : Fin 3)) (coordinate_mem_degree_one_geometric 2)
        (by omega))
      (fieldBaseChangeAmbientMap W L))

/-- In particular, the canonical open is exactly the inverse image of the
standard projective coordinate open `D₊(Z)`, rather than merely an unspecified
open subscheme. -/
theorem canonicalStandardOpenMap_opensRange_eq_preimage_basicOpen
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    (canonicalStandardOpenMap W L).opensRange =
      fieldBaseChangeAmbientMap W L ⁻¹ᵁ
        Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (2 : Fin 3)) := by
  rw [canonicalStandardOpenMap_opensRange, Proj.opensRange_awayι]

/-- A comparison package separating the now-canonical open immersion from
the two remaining geometric inputs.

The isomorphism is the precise quotient/restriction comparison still needed:
it must identify the already checked principal quotient after scalar
extension with the pullback of the actual reduced projective cubic.  Neither
density nor reducedness is folded into that comparison. -/
structure StandardChartComparison (W : WeierstrassCurve K)
    (L : Type u) [Field L] [Algebra K L] where
  /-- Scheme-level comparison between the checked quotient chart and the
  canonical pullback open. -/
  chartIso : standardAffineChartScheme (W.map (algebraMap K L)) ≅
    canonicalStandardOpen W L
  /-- Compatibility of the reduced projective cubic construction with this
  field extension.  Unlike a reducedness hypothesis, this is a concrete
  scheme comparison; reducedness of its source follows from the already
  checked reducedness of `scheme (W.map ...)`. -/
  targetBaseChangeIso : fieldBaseChange W L ≅
    scheme (W.map (algebraMap K L))
  /-- Density of the canonical `Z ≠ 0` open in the actual pullback. -/
  canonicalMap_denseRange : DenseRange (canonicalStandardOpenMap W L)

/-- The exact geometric data still needed to pass from the checked integral
affine equation to an integral field base change of the projective cubic.

The source is not an abstract integral scheme: it is the quotient of the
actual degree-zero localization by the localized projective Weierstrass
equation, proved integral above.  A future constructor for this structure
must identify that source with the `Z != 0` open of the pullback. -/
structure StandardChartBaseChangeWitness (W : WeierstrassCurve K)
    (L : Type u) [Field L] [Algebra K L] where
  /-- Identification of the checked standard chart with an open of the
  field-base-changed projective cubic. -/
  chartMap : standardAffineChartScheme (W.map (algebraMap K L)) ⟶
    fieldBaseChange W L
  /-- The chart comparison really is an open immersion. -/
  chartMap_isOpenImmersion : IsOpenImmersion chartMap
  /-- The standard chart is dense in the projective cubic after base
  change. -/
  chartMap_denseRange : DenseRange chartMap
  /-- Reducedness of the concrete pullback.  This is stated separately
  because the current cubic was reduced before, rather than after, base
  change. -/
  target_isReduced : IsReduced (fieldBaseChange W L)

/-- Turn the exact quotient/open comparison into the original dense-chart
witness.  The open-immersion proof is no longer caller-supplied: it is the
composition of an isomorphism with the canonical pulled-back `Proj.awayι`.

This is a real downstream consumer of `StandardChartComparison`; composing it
with `geometricallyIntegral_of_standardChartBaseChangeWitness` below reaches
the Tau Ceti/Γ₀ package without adding geometric-integrality assumptions. -/
noncomputable def StandardChartComparison.toBaseChangeWitness
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (D : StandardChartComparison W L) :
    StandardChartBaseChangeWitness W L where
  chartMap := D.chartIso.hom ≫ canonicalStandardOpenMap W L
  chartMap_isOpenImmersion := by infer_instance
  chartMap_denseRange :=
    D.canonicalMap_denseRange.comp D.chartIso.hom.surjective.denseRange
      (canonicalStandardOpenMap W L).continuous
  target_isReduced := by
    letI : IsReduced (scheme (W.map (algebraMap K L))) := by infer_instance
    exact isReduced_of_isOpenImmersion D.targetBaseChangeIso.hom

/-- A dense integral standard chart in every field base change, together
with reducedness of the ambient pullback, proves geometric integrality of the
concrete projective cubic.

This theorem is the checked reduction consumed by the Tau Ceti bridge below:
the remaining work is exactly the construction of
`StandardChartBaseChangeWitness`, not a fresh irreducibility argument. -/
theorem geometricallyIntegral_of_standardChartBaseChangeWitness
    (W : WeierstrassCurve K)
    (hchart : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartBaseChangeWitness W L) :
    GeometricallyIntegral (structureMap W) := by
  letI : GeometricallyReduced (structureMap W) := by
    constructor
    rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro L _ _
    exact (hchart L).target_isReduced
  letI : GeometricallyIrreducible (structureMap W) := by
    constructor
    rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro L _ _
    let D := hchart L
    have himage : IsIrreducible (Set.range D.chartMap) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ
        (standardAffineChartScheme (W.map (algebraMap K L)))).image
          D.chartMap D.chartMap.continuous.continuousOn
    have htarget : IsIrreducible
        (Set.univ : Set (fieldBaseChange W L)) := by
      rw [← D.chartMap_denseRange.closure_range]
      exact himage.closure
    exact (irreducibleSpace_def _).2 htarget
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
    (structureMap W)

/-- The canonical comparison package reaches geometric integrality of the
actual projective cubic.  This is the checked consumer ensuring that the new
comparison interface has exactly the data required by the existing
dense-chart reduction. -/
theorem geometricallyIntegral_of_standardChartComparison
    (W : WeierstrassCurve K)
    (hcomparison : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartComparison W L) :
    GeometricallyIntegral (structureMap W) :=
  geometricallyIntegral_of_standardChartBaseChangeWitness W fun L ↦
    (hcomparison L).toBaseChangeWitness W L

/-- The dense-chart criterion reaches Tau Ceti's actual abelian-variety
constructor.  This is the first downstream consumer of the new interface and
removes geometric integrality as a separately supplied typeclass at the call
site. -/
noncomputable def toAbelianVarietyOfStandardChartBaseChangeWitness
    (W : WeierstrassCurve K) [GrpObj (toOver W)]
    (hchart : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartBaseChangeWitness W L) :
    TauCeti.AlgebraicGeometry.AbelianVariety K := by
  letI : GeometricallyIntegral (toOver W).hom := by
    change GeometricallyIntegral (structureMap W)
    exact geometricallyIntegral_of_standardChartBaseChangeWitness W hchart
  exact toAbelianVariety W

/-- The canonical quotient/open comparison reaches Tau Ceti's concrete
abelian-variety constructor, not only the intermediate integrality
proposition. -/
noncomputable def toAbelianVarietyOfStandardChartComparison
    (W : WeierstrassCurve K) [GrpObj (toOver W)]
    (hcomparison : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartComparison W L) :
    TauCeti.AlgebraicGeometry.AbelianVariety K := by
  letI : GeometricallyIntegral (toOver W).hom := by
    change GeometricallyIntegral (structureMap W)
    exact geometricallyIntegral_of_standardChartComparison W hcomparison
  exact toAbelianVariety W

/-- Group-law compatibility of the canonical coordinate-to-scheme point map,
phrased independently of a named geometric-integrality instance.

The quantification over the (proof-irrelevant) instance lets the chart
criterion install geometric integrality internally.  This packages only the
genuine remaining group-law equations; point-set bijectivity is already
checked in the projective-point comparison module. -/
structure CanonicalPointGroupLawCompatibility
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    [GrpObj (toOver W)] : Prop where
  map_zero : ∀ [GeometricallyIntegral (toOver W).hom],
    projectivePointToAbelianVarietyRationalPoint W 0 = 1
  map_add : ∀ [GeometricallyIntegral (toOver W).hom]
    (P Q : W.toProjective.Point),
    projectivePointToAbelianVarietyRationalPoint W (P + Q) =
      projectivePointToAbelianVarietyRationalPoint W P *
        projectivePointToAbelianVarietyRationalPoint W Q

/-- A dependent package recording that the standard-chart criterion has
reached the finite-flat `Gamma_0(N)` consumer.  The comparison field exposes
the exact abelian variety/group scheme used by the datum. -/
structure StandardChartSplitGammaZeroPackage
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [DecidableEq K] [W.IsElliptic] where
  comparison : WeierstrassAbelianVarietyComparison W
  datum : WeierstrassGroupSchemeInterface.SplitGammaZeroDatum
    (N := N) W comparison.toGroupSchemeInterface

/-- Construct the finite-flat split `Gamma_0(N)` datum from the checked dense
standard chart, the still-explicit group-law equations, and a coordinate
point of exact order `N`.

In particular, this consumer no longer requests
`GeometricallyIntegral (toOver W).hom`: it derives that instance from the
base-change witnesses and immediately uses it in the concrete cubic's Tau
Ceti bridge. -/
noncomputable def standardChartSplitGammaZeroPackage
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [DecidableEq K] [W.IsElliptic] [GrpObj (toOver W)]
    (hchart : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartBaseChangeWitness W L)
    (hgroup : CanonicalPointGroupLawCompatibility W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    StandardChartSplitGammaZeroPackage (N := N) W := by
  letI : GeometricallyIntegral (toOver W).hom := by
    change GeometricallyIntegral (structureMap W)
    exact geometricallyIntegral_of_standardChartBaseChangeWitness W hchart
  let e := canonicalProjectivePointEquivOfGroupLaw W
    hgroup.map_zero hgroup.map_add
  exact
    { comparison := toAbelianVarietyComparison W e
      datum := splitGammaZeroDatumOfProjectiveCubic W e P hP }

/-- The packaged downstream subgroup has the requested constant geometric
order.  This theorem ensures that the new criterion is checked all the way
through the finite-flat consumer, rather than merely returning an abstract
abelian variety. -/
theorem standardChartSplitGammaZeroPackage_hasConstantOrder
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [DecidableEq K] [W.IsElliptic] [GrpObj (toOver W)]
    (hchart : ∀ (L : Type u) [Field L] [Algebra K L],
      StandardChartBaseChangeWitness W L)
    (hgroup : CanonicalPointGroupLawCompatibility W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (standardChartSplitGammaZeroPackage W hchart hgroup P hP).datum.subgroup.carrier
      |>.HasConstantOrder N := by
  letI : GeometricallyIntegral (toOver W).hom := by
    change GeometricallyIntegral (structureMap W)
    exact geometricallyIntegral_of_standardChartBaseChangeWitness W hchart
  simpa [standardChartSplitGammaZeroPackage] using
    (splitGammaZeroDatumOfProjectiveCubic_hasConstantOrder W
      (canonicalProjectivePointEquivOfGroupLaw W hgroup.map_zero hgroup.map_add)
      P hP)

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
