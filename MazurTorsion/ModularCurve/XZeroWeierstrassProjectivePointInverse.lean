/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveCubic

/-!
# Recovering coordinates from projective Weierstrass scheme points

This file continues the reverse point comparison for the concrete reduced
projective Weierstrass cubic.  The basic-chart factor constructed in
`XZeroWeierstrassProjectiveCubic` induces a map from the degree-zero homogeneous
localization to the base field.  We prove that this map fixes constants, that
homogeneous fractions are evaluated by its three coordinate ratios, and that
the extracted nonzero triple satisfies the cubic equation.

For an elliptic Weierstrass curve the extracted triple is nonsingular, so every
scheme-valued point produces an actual Mathlib projective point.  This does not
yet assert that mapping that coordinate point forward recovers the original
scheme morphism: the remaining comparison is the explicit pullback computation
for `X_j / X_i` along `Proj.fromOfGlobalSections`, followed by chart-ring
extensionality.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj DirectSum

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

universe u

namespace WeierstrassProjectiveCubic

variable {K : Type u} [Field K]

private theorem coordinate_mem_degree_one (i : Fin 3) :
    MvPolynomial.X i ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K i

private theorem constant_mem_chart_degree_zero (a : K) :
    MvPolynomial.C a ∈ homogeneousPieces K (0 • (1 : ℕ)) := by
  simp [homogeneousPieces]

/-- The degree-zero chart element `X_j / X_i`. -/
noncomputable def coordinateChartRatio (i j : Fin 3) :
  HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K)
    (coordinate_mem_degree_one i) 1 (MvPolynomial.X j)
    (by simpa using (coordinate_mem_degree_one j))

/-- Constants in the degree-zero homogeneous localization of the `i`-th chart. -/
noncomputable def coordinateChartConstantHom (i : Fin 3) :
    K →+* HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
    (Submonoid.powers (MvPolynomial.X i))).comp
      (algebraMap K (homogeneousPieces K 0))

/-- The structure map of a coordinate chart is induced by its constant homomorphism. -/
theorem awayι_comp_projectivePlaneStructureMap (i : Fin 3) :
    Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one i) (by omega) ≫
      projectivePlaneStructureMap K =
    Spec.map (CommRingCat.ofHom (coordinateChartConstantHom i)) := by
  rw [projectivePlaneStructureMap, ← Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Because a cubic point is a morphism over `Spec K`, its chosen-chart ring map fixes the
base-field constants. -/
theorem chartRingHomOfOverPoint_comp_coordinateChartConstantHom
    (W : WeierstrassCurve K)
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    (chartRingHomOfOverPoint W g).comp
        (coordinateChartConstantHom (chartIndexOfOverPoint W g)) =
      RingHom.id K := by
  let i := chartIndexOfOverPoint W g
  let l := chartLiftOfOverPoint W g
  have hbase : ambientMorphismOfOverPoint W g ≫ projectivePlaneStructureMap K = 𝟙 _ := by
    have hleft : ambientMorphismOfOverPoint W g ≫ projectivePlaneStructureMap K =
        g.left ≫ (toOver W).hom := by
      dsimp only [ambientMorphismOfOverPoint, toOver, structureMap]
      exact Category.assoc _ _ _
    rw [hleft, g.w]
    simp [AffineCommGroupScheme.testObject]
  have hl : l ≫ Spec.map (CommRingCat.ofHom (coordinateChartConstantHom i)) = 𝟙 _ := by
    calc
      l ≫ Spec.map (CommRingCat.ofHom (coordinateChartConstantHom i)) =
          l ≫ (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
            (coordinate_mem_degree_one i) (by omega) ≫
              projectivePlaneStructureMap K) := by
                rw [awayι_comp_projectivePlaneStructureMap]
      _ = (l ≫ Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
            (coordinate_mem_degree_one i) (by omega)) ≫
              projectivePlaneStructureMap K := (Category.assoc _ _ _).symm
      _ = ambientMorphismOfOverPoint W g ≫ projectivePlaneStructureMap K := by
            rw [chartLiftOfOverPoint_fac]
      _ = 𝟙 _ := hbase
  have hp := congrArg Spec.preimage hl
  rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at hp
  exact congrArg CommRingCat.Hom.hom hp

/-- Membership in the projective prime on a coordinate chart is membership of the corresponding
homogeneous fraction in the affine-chart prime. -/
theorem polynomial_mem_awayι_iff_awayMk_mem (i : Fin 3)
    (q : PrimeSpectrum (HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X i)))
    (p : MvPolynomial (Fin 3) K) {n : ℕ} (hp : p ∈ homogeneousPieces K n) :
    p ∈ ((Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one i) (by omega)) q).asHomogeneousIdeal ↔
      (HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (coordinate_mem_degree_one i) n p (by simpa using hp) :
          HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i)) ∈
        q.asIdeal := by
  let e := Proj.basicOpenIsoSpec (homogeneousPieces K) (MvPolynomial.X i)
    (coordinate_mem_degree_one i) (by omega)
  let xs : (Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i)).toScheme :=
    e.inv q
  let z : HomogeneousLocalization.NumDenSameDeg (homogeneousPieces K)
      (.powers (MvPolynomial.X i)) :=
    ⟨n, ⟨p, hp⟩,
      ⟨MvPolynomial.X i ^ n, by simpa using
        (SetLike.pow_mem_graded (A := homogeneousPieces K) n
          (coordinate_mem_degree_one i))⟩,
      ⟨n, rfl⟩⟩
  have h := AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
    (homogeneousPieces K) xs z
  have hq :
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec
        (homogeneousPieces K) (MvPolynomial.X i)).base xs = q := by
    change (e.hom xs) = q
    exact congrArg (fun f ↦ f q) e.inv_hom_id
  rw [hq] at h
  have hxs : xs.1 =
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one i) (by omega) q := by
    exact congrArg (fun f ↦ f q)
      (Proj.basicOpenIsoSpec_inv_ι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one i) (by omega))
  rw [← hxs]
  change p ∈ xs.1.asHomogeneousIdeal ↔ _
  rw [← h]
  have hz : HomogeneousLocalization.mk z =
      (HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (coordinate_mem_degree_one i) n p (by simpa using hp) :
          HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i)) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [hz]

/-- At the closed point of `Spec K`, membership in the affine-chart prime is exactly vanishing
under the induced chart ring homomorphism. -/
theorem mem_chartLift_closedPoint_iff_map_eq_zero
    (W : WeierstrassCurve K)
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W)
    (z : HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X (chartIndexOfOverPoint W g))) :
    z ∈ (chartLiftOfOverPoint W g (IsLocalRing.closedPoint K)).asIdeal ↔
      chartRingHomOfOverPoint W g z = 0 := by
  rw [← Spec.map_preimage (chartLiftOfOverPoint W g)]
  change chartRingHomOfOverPoint W g z ∈ (IsLocalRing.closedPoint K).asIdeal ↔ _
  rw [show (IsLocalRing.closedPoint K).asIdeal = ⊥ from
    IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.mem_bot

theorem coordinateChartConstantHom_apply (i : Fin 3) (a : K) :
    coordinateChartConstantHom i a =
      HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (coordinate_mem_degree_one i) 0 (MvPolynomial.C a)
          (constant_mem_chart_degree_zero a) := by
  apply HomogeneousLocalization.val_injective
  simp only [coordinateChartConstantHom, RingHom.coe_comp, Function.comp_apply]
  change Localization.mk (MvPolynomial.C a) _ = Localization.mk (MvPolynomial.C a) _
  rfl

/-- Every homogeneous fraction on a coordinate chart is obtained by evaluating its numerator at
chart constants and coordinate ratios. -/
theorem coordinateChartAwayMk_eq_eval₂Hom (i : Fin 3) {n : ℕ}
    (q : MvPolynomial (Fin 3) K) (hq : q ∈ homogeneousPieces K n) :
    HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (coordinate_mem_degree_one i) n q (by simpa using hq) =
      MvPolynomial.eval₂Hom (coordinateChartConstantHom i)
        (coordinateChartRatio i) q := by
  induction hq using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, map_zero,
        HomogeneousLocalization.val_zero, Localization.mk_zero]
  | add p q hp hq ihp ihq =>
      have hp' : p ∈ homogeneousPieces K n := hp
      have hq' : q ∈ homogeneousPieces K n := hq
      calc
        _ = HomogeneousLocalization.Away.mk (homogeneousPieces K)
              (coordinate_mem_degree_one i) n p (by simpa using hp') +
            HomogeneousLocalization.Away.mk (homogeneousPieces K)
              (coordinate_mem_degree_one i) n q (by simpa using hq') := by
              apply HomogeneousLocalization.val_injective
              simp only [HomogeneousLocalization.Away.val_mk,
                HomogeneousLocalization.val_add]
              rw [Localization.add_mk_self]
        _ = MvPolynomial.eval₂Hom (coordinateChartConstantHom i)
              (coordinateChartRatio i) p +
            MvPolynomial.eval₂Hom (coordinateChartConstantHom i)
              (coordinateChartRatio i) q := by
              rw [ihp, ihq]
        _ = _ := by rw [map_add]
  | monomial d a hd =>
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk,
        MvPolynomial.eval₂Hom_monomial]
      change _ = algebraMap
        (HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i))
          (coordinateChartConstantHom i a *
            d.prod fun j e ↦ coordinateChartRatio i j ^ e)
      rw [map_mul]
      simp only [Finsupp.prod, map_prod]
      simp only [HomogeneousLocalization.algebraMap_apply,
        coordinateChartConstantHom_apply, coordinateChartRatio,
        HomogeneousLocalization.val_pow,
        HomogeneousLocalization.Away.val_mk]
      simp only [Localization.mk_pow, Localization.mk_prod, Localization.mk_mul]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      simp only [OneMemClass.coe_one, Submonoid.coe_mul,
        SubmonoidClass.coe_pow, SubmonoidClass.coe_finsetProd]
      rw [MvPolynomial.monomial_eq, Finsupp.prod,
        Finset.prod_pow_eq_pow_sum]
      simp only [pow_zero, pow_one]
      have hsum : ∑ j ∈ d.support, d j = n := by
        rw [Finsupp.weight_apply] at hd
        simpa [Finsupp.sum, smul_eq_mul] using hd
      simp [hsum]

/-- For degree-one coordinate variables, Mathlib's localization element is the explicit chart
ratio defined above. -/
theorem isLocalizationElem_degree_one_eq_coordinateChartRatio (i j : Fin 3) :
    HomogeneousLocalization.Away.isLocalizationElem
        (coordinate_mem_degree_one (K := K) i)
        (coordinate_mem_degree_one (K := K) j) =
      coordinateChartRatio (K := K) i j := by
  apply HomogeneousLocalization.val_injective
    (x := Submonoid.powers (MvPolynomial.X i))
  simp [HomogeneousLocalization.Away.isLocalizationElem, coordinateChartRatio]

/-- The localized cubic vanishes under the chart ring map of every scheme-valued cubic point. -/
theorem chartRingHomOfOverPoint_cubic_eq_zero
    (W : WeierstrassCurve K)
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    chartRingHomOfOverPoint W g
      (HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (coordinate_mem_degree_one (chartIndexOfOverPoint W g)) 3
        W.toProjective.polynomial (polynomial_mem_degree_three W)) = 0 := by
  let i := chartIndexOfOverPoint W g
  let q := chartLiftOfOverPoint W g (IsLocalRing.closedPoint K)
  have hpoly : W.toProjective.polynomial ∈
      ((Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one i) (by omega)) q).asHomogeneousIdeal := by
    change W.toProjective.polynomial ∈
      ((chartLiftOfOverPoint W g ≫
        Proj.awayι (homogeneousPieces K)
          (MvPolynomial.X (chartIndexOfOverPoint W g))
          (coordinate_mem_degree_one (chartIndexOfOverPoint W g))
          (by omega)) (IsLocalRing.closedPoint K)).asHomogeneousIdeal
    rw [chartLiftOfOverPoint_fac]
    exact ambientMorphismOfOverPoint_polynomial_mem W g _
  have haway :
      (HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (coordinate_mem_degree_one i) 3 W.toProjective.polynomial
        (polynomial_mem_degree_three W) :
          HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X i)) ∈
        q.asIdeal :=
    (polynomial_mem_awayι_iff_awayMk_mem i q W.toProjective.polynomial
      (polynomial_mem_degree_three W)).mp hpoly
  exact (mem_chartLift_closedPoint_iff_map_eq_zero W g _).mp haway

/-- The normalized coordinates extracted from a scheme-valued point satisfy the homogeneous
Weierstrass equation. -/
theorem eval_coordinateRepresentativeOfOverPoint_polynomial_eq_zero
    (W : WeierstrassCurve K)
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    MvPolynomial.eval (coordinateRepresentativeOfOverPoint W g)
      W.toProjective.polynomial = 0 := by
  let i := chartIndexOfOverPoint W g
  let φ := chartRingHomOfOverPoint W g
  have hzero := chartRingHomOfOverPoint_cubic_eq_zero W g
  rw [coordinateChartAwayMk_eq_eval₂Hom i W.toProjective.polynomial
    (polynomial_mem_degree_three W)] at hzero
  simp only [MvPolynomial.map_eval₂Hom] at hzero
  have hconst : φ.comp (coordinateChartConstantHom i) = RingHom.id K :=
    chartRingHomOfOverPoint_comp_coordinateChartConstantHom W g
  rw [hconst] at hzero
  have hratio : (fun j ↦ φ (coordinateChartRatio i j)) =
      coordinateRepresentativeOfOverPoint W g := by
    funext j
    rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio i j]
    rfl
  rw [hratio] at hzero
  exact hzero

/-- On an elliptic Weierstrass curve, every nonzero homogeneous solution is nonsingular. -/
theorem projective_nonsingular_of_equation_of_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : Fin 3 → K) (hP : P ≠ 0) (heq : W.toProjective.Equation P) :
    W.toProjective.Nonsingular P := by
  by_cases hZ : P 2 = 0
  · rw [W.toProjective.nonsingular_of_Z_eq_zero hZ]
    refine ⟨heq, Or.inr ?_⟩
    have hX : P 0 = 0 :=
      W.toProjective.X_eq_zero_of_Z_eq_zero heq hZ
    have hY : P 1 ≠ 0 := by
      intro hY
      apply hP
      funext j
      fin_cases j <;> simp [hX, hY, hZ]
    simpa [hX] using pow_ne_zero 2 hY
  · rw [W.toProjective.nonsingular_of_Z_ne_zero hZ]
    exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((W.toProjective.equation_of_Z_ne_zero hZ).mp heq)

/-- Under ellipticity, the normalized coordinates extracted from any scheme-valued cubic point
form a Mathlib nonsingular projective point. -/
theorem coordinateRepresentativeOfOverPoint_nonsingular
    (W : WeierstrassCurve K) [W.IsElliptic]
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    W.toProjective.Nonsingular (coordinateRepresentativeOfOverPoint W g) :=
  projective_nonsingular_of_equation_of_ne_zero W _
    (coordinateRepresentativeOfOverPoint_ne_zero W g)
    (eval_coordinateRepresentativeOfOverPoint_polynomial_eq_zero W g)

/-- The Mathlib projective point recovered from an arbitrary scheme-valued point of the concrete
elliptic cubic. -/
noncomputable def projectivePointOfOverPoint
    (W : WeierstrassCurve K) [W.IsElliptic]
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    W.toProjective.Point :=
  ⟨(W.toProjective.nonsingularLift_iff
    (coordinateRepresentativeOfOverPoint W g)).mpr
      (coordinateRepresentativeOfOverPoint_nonsingular W g)⟩

/-- Send the recovered projective point back to the concrete cubic.  Proving this morphism equal
to `g` is the remaining explicit chart-pullback comparison needed for surjectivity. -/
noncomputable def recoveredPointOverMorphism
    (W : WeierstrassCurve K) [W.IsElliptic]
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W :=
  projectivePointOverMorphism W (projectivePointOfOverPoint W g)

end WeierstrassProjectiveCubic

end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
