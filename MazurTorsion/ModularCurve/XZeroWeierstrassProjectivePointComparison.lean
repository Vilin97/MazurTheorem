/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePointInverse

/-!
# Comparing projective Weierstrass scheme points with coordinates

This file completes the reverse point comparison for the concrete reduced
projective Weierstrass cubic.  A chosen coordinate chart recovers the value of
every homogeneous fraction from its normalized coordinate triple.  We prove
that chart maps are determined by constants and the three coordinate ratios,
and that two `K`-points with the same ambient closed point are equal.

For an elliptic cubic, affine normalization changes the recovered homogeneous
triple only by a unit scalar.  Hence its forward scheme point has the same
ambient closed point as the original point, and the chart comparison proves
that `recoveredPointOverMorphism W g = g`.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj DirectSum WeierstrassCurve.Projective

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem coordinate_mem_degree_one' (i : Fin 3) :
    MvPolynomial.X i ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K i

/-- The chosen-chart map evaluates every homogeneous fraction at the normalized coordinates
recovered from the scheme point. -/
theorem chartRingHomOfOverPoint_awayMk_eq_eval
    (W : WeierstrassCurve K)
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W)
    (p : MvPolynomial (Fin 3) K) {n : ℕ} (hp : p ∈ homogeneousPieces K n) :
    chartRingHomOfOverPoint W g
        (HomogeneousLocalization.Away.mk (homogeneousPieces K)
          (coordinate_mem_degree_one' (chartIndexOfOverPoint W g)) n p
          (by simpa using hp)) =
      MvPolynomial.eval (coordinateRepresentativeOfOverPoint W g) p := by
  let i := chartIndexOfOverPoint W g
  let φ := chartRingHomOfOverPoint W g
  rw [coordinateChartAwayMk_eq_eval₂Hom i p hp]
  simp only [MvPolynomial.map_eval₂Hom]
  have hconst : φ.comp (coordinateChartConstantHom i) = RingHom.id K :=
    chartRingHomOfOverPoint_comp_coordinateChartConstantHom W g
  rw [hconst]
  have hratio : (fun j ↦ φ (coordinateChartRatio i j)) =
      coordinateRepresentativeOfOverPoint W g := by
    funext j
    rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio i j]
    rfl
  rw [hratio]
  rfl

/-- A positive-degree homogeneous polynomial belongs to the ambient image prime exactly when it
vanishes on the normalized coordinate representative. -/
theorem mem_ambientMorphismOfOverPoint_iff_eval_coordinateRepresentative
    (W : WeierstrassCurve K)
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W)
    (p : MvPolynomial (Fin 3) K) {n : ℕ} (hp : p ∈ homogeneousPieces K n) :
    p ∈ (ambientMorphismOfOverPoint W g (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      MvPolynomial.eval (coordinateRepresentativeOfOverPoint W g) p = 0 := by
  let i := chartIndexOfOverPoint W g
  let q := chartLiftOfOverPoint W g (IsLocalRing.closedPoint K)
  have hfacPoint := congrArg (fun f ↦ f (IsLocalRing.closedPoint K))
    (chartLiftOfOverPoint_fac W g)
  have hfacIdeal := congrArg (fun x : projectivePlane K ↦ x.asHomogeneousIdeal)
    hfacPoint
  rw [← hfacIdeal]
  change p ∈
    ((Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
      (coordinate_mem_degree_one' i) (by omega)) q).asHomogeneousIdeal ↔ _
  rw [polynomial_mem_awayι_iff_awayMk_mem i q p hp,
    mem_chartLift_closedPoint_iff_map_eq_zero,
    chartRingHomOfOverPoint_awayMk_eq_eval W g p hp]

/-- A degree-zero homogeneous polynomial belongs to a projective prime exactly when it is zero. -/
theorem mem_projective_degree_zero_iff_eq_zero
    (x : projectivePlane K)
    (p : MvPolynomial (Fin 3) K) (hp : p ∈ homogeneousPieces K 0) :
    p ∈ x.asHomogeneousIdeal ↔ p = 0 := by
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let a : K := (degreeZeroRingEquiv K).symm ⟨p, hp⟩
  have hpa : (degreeZeroRingEquiv K) a = ⟨p, hp⟩ :=
    (degreeZeroRingEquiv K).apply_symm_apply ⟨p, hp⟩
  have hpa' : MvPolynomial.C a = p := congrArg Subtype.val hpa
  constructor
  · intro hmem
    by_contra hp0
    have ha0 : a ≠ 0 := by
      intro ha
      apply hp0
      rw [← hpa', ha, map_zero]
    have hu : IsUnit p := by
      rw [← hpa']
      exact (isUnit_iff_ne_zero.mpr ha0).map (MvPolynomial.C :
        K →+* MvPolynomial (Fin 3) K)
    exact (x.asHomogeneousIdeal.toIdeal.notMem_of_isUnit hu hmem).elim
  · rintro rfl
    exact zero_mem _

private theorem eval_smul_of_mem_homogeneous
    (u : K) (P : Fin 3 → K) (p : MvPolynomial (Fin 3) K) {n : ℕ}
    (hp : p ∈ homogeneousPieces K n) :
    MvPolynomial.eval (u • P) p = u ^ n * MvPolynomial.eval P p := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial d a hd =>
      simp only [MvPolynomial.eval_monomial, Pi.smul_apply, smul_eq_mul,
        mul_pow]
      have hsum : ∑ j ∈ d.support, d j = n := by
        rw [Finsupp.weight_apply] at hd
        simpa [Finsupp.sum, smul_eq_mul] using hd
      simp only [Finsupp.prod]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
      ring

private theorem eval_zero_iff_of_equiv
    {P Q : Fin 3 → K} (hPQ : P ≈ Q)
    (p : MvPolynomial (Fin 3) K) {n : ℕ} (hp : p ∈ homogeneousPieces K n) :
    MvPolynomial.eval P p = 0 ↔ MvPolynomial.eval Q p = 0 := by
  rcases hPQ with ⟨u, rfl⟩
  change MvPolynomial.eval ((u : K) • Q) p = 0 ↔ _
  rw [eval_smul_of_mem_homogeneous (u : K) Q p hp]
  simp only [pow_ne_zero n u.ne_zero, mul_eq_zero, false_or]

/-- Unit-equivalent nonzero homogeneous triples define the same closed point of projective space. -/
theorem ambientPoint_closedPoint_eq_of_equiv
    (P Q : Fin 3 → K) (hP : P ≠ 0) (hQ : Q ≠ 0) (hPQ : P ≈ Q) :
    ambientPoint P hP (IsLocalRing.closedPoint K) =
      ambientPoint Q hQ (IsLocalRing.closedPoint K) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  cases n with
  | zero =>
      rw [mem_projective_degree_zero_iff_eq_zero _ p hp,
        mem_projective_degree_zero_iff_eq_zero _ p hp]
  | succ n =>
      rw [mem_ambientPoint_closedPoint_iff P hP p (Nat.succ_pos n) hp,
        mem_ambientPoint_closedPoint_iff Q hQ p (Nat.succ_pos n) hp]
      exact eval_zero_iff_of_equiv hPQ p hp

/-- The normalized coordinate triple extracted from a scheme point represents its ambient closed
point. -/
theorem ambientPoint_coordinateRepresentative_closedPoint
    (W : WeierstrassCurve K) [W.IsElliptic]
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    ambientPoint (coordinateRepresentativeOfOverPoint W g)
        (coordinateRepresentativeOfOverPoint_ne_zero W g)
        (IsLocalRing.closedPoint K) =
      ambientMorphismOfOverPoint W g (IsLocalRing.closedPoint K) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  cases n with
  | zero =>
      rw [mem_projective_degree_zero_iff_eq_zero _ p hp,
        mem_projective_degree_zero_iff_eq_zero _ p hp]
  | succ n =>
      rw [mem_ambientPoint_closedPoint_iff _ _ p (Nat.succ_pos n) hp,
        mem_ambientMorphismOfOverPoint_iff_eval_coordinateRepresentative W g p hp]

/-- Forward mapping the recovered Mathlib point preserves the ambient closed point. -/
theorem ambientClosedPoint_recoveredPointOverMorphism
    (W : WeierstrassCurve K) [W.IsElliptic]
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    ambientClosedPointOfOverPoint W (recoveredPointOverMorphism W g) =
      ambientClosedPointOfOverPoint W g := by
  let R := coordinateRepresentativeOfOverPoint W g
  let hR : W.toProjective.Nonsingular R :=
    coordinateRepresentativeOfOverPoint_nonsingular W g
  let P : W.toProjective.Point := projectivePointOfOverPoint W g
  have hPdef : P = projectivePointOfOverPoint W g := rfl
  have hRne : R ≠ 0 := coordinateRepresentativeOfOverPoint_ne_zero W g
  suffices hforward :
      ambientClosedPointOfOverPoint W (recoveredPointOverMorphism W g) =
        ambientPoint R hRne (IsLocalRing.closedPoint K) by
    exact hforward.trans
      (ambientPoint_coordinateRepresentative_closedPoint W g)
  by_cases hZ : R 2 = 0
  · have hto : P.toAffineLift = 0 := by
      rw [hPdef]
      exact WeierstrassCurve.Projective.Point.toAffineLift_of_Z_eq_zero
        ((W.toProjective.nonsingularLift_iff R).mpr hR) hZ
    have hequiv : (![0, 1, 0] : Fin 3 → K) ≈ R :=
      Setoid.symm (W.toProjective.equiv_zero_of_Z_eq_zero hR hZ)
    have hclosed := ambientPoint_closedPoint_eq_of_equiv
      (![0, 1, 0] : Fin 3 → K) R
      (nonsingular_ne_zero W _ W.toProjective.nonsingular_zero) hRne hequiv
    have hmorph :
        ambientMorphismOfOverPoint W (recoveredPointOverMorphism W g) =
          ambientPoint ![0, 1, 0]
            (nonsingular_ne_zero W _ W.toProjective.nonsingular_zero) := by
      change (projectivePointOverMorphism W P).left ≫ inclusion W = _
      rw [projectivePointOverMorphism_left]
      change affinePointMorphism W P.toAffineLift ≫ inclusion W = _
      rw [hto]
      change pointOfNonsingularRepresentative W ![0, 1, 0]
          W.toProjective.nonsingular_zero ≫ inclusion W = _
      rw [pointOfNonsingularRepresentative_comp_inclusion]
    exact (congrArg (fun f : Spec (.of K) ⟶ projectivePlane K ↦
      f (IsLocalRing.closedPoint K)) hmorph).trans hclosed
  · have hto : P.toAffineLift =
        .some (R 0 / R 2) (R 1 / R 2)
          ((W.toProjective.nonsingular_of_Z_ne_zero hZ).mp hR) := by
      rw [hPdef]
      exact WeierstrassCurve.Projective.Point.toAffineLift_of_Z_ne_zero hZ
    let Q : Fin 3 → K := ![R 0 / R 2, R 1 / R 2, 1]
    have hQ : W.toProjective.Nonsingular Q := by
      exact (W.toProjective.nonsingular_some _ _).mpr
        ((W.toProjective.nonsingular_of_Z_ne_zero hZ).mp hR)
    have hequiv : Q ≈ R :=
      Setoid.symm (WeierstrassCurve.Projective.equiv_some_of_Z_ne_zero hZ)
    have hclosed := ambientPoint_closedPoint_eq_of_equiv
      Q R (nonsingular_ne_zero W Q hQ) hRne hequiv
    have hmorph :
        ambientMorphismOfOverPoint W (recoveredPointOverMorphism W g) =
          ambientPoint Q (nonsingular_ne_zero W Q hQ) := by
      change (projectivePointOverMorphism W P).left ≫ inclusion W = _
      rw [projectivePointOverMorphism_left]
      change affinePointMorphism W P.toAffineLift ≫ inclusion W = _
      rw [hto, affinePointMorphism_some,
        pointOfNonsingularRepresentative_comp_inclusion]
    exact (congrArg (fun f : Spec (.of K) ⟶ projectivePlane K ↦
      f (IsLocalRing.closedPoint K)) hmorph).trans hclosed

/-- A map from a standard projective chart is determined by the base constants and its three
coordinate ratios. -/
theorem chartRingHom_ext {B : Type*} [CommRing B] (i : Fin 3)
    {f g : HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X i) →+* B}
    (hconst : f.comp (coordinateChartConstantHom i) =
      g.comp (coordinateChartConstantHom i))
    (hratio : ∀ j, f (coordinateChartRatio i j) =
      g (coordinateChartRatio i j)) : f = g := by
  ext z
  obtain ⟨n, q, hq, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (homogeneousPieces K)
      (coordinate_mem_degree_one' i) z
  have hq' : q ∈ homogeneousPieces K n := by simpa using hq
  rw [coordinateChartAwayMk_eq_eval₂Hom i q hq']
  simp only [MvPolynomial.map_eval₂Hom]
  rw [hconst]
  have heval :
      MvPolynomial.eval₂Hom (g.comp (coordinateChartConstantHom i))
          (fun j ↦ f (coordinateChartRatio i j)) =
        MvPolynomial.eval₂Hom (g.comp (coordinateChartConstantHom i))
          (fun j ↦ g (coordinateChartRatio i j)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp only [MvPolynomial.eval₂Hom_X']
      exact hratio j
  exact DFunLike.congr_fun heval q

/-- Two `K`-points of the concrete cubic with the same ambient closed point are equal. -/
theorem overPoint_eq_of_ambientClosedPoint_eq
    (W : WeierstrassCurve K)
    (g h : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W)
    (hpoint : ambientClosedPointOfOverPoint W g =
      ambientClosedPointOfOverPoint W h) : g = h := by
  let i := chartIndexOfOverPoint W g
  have hih : MvPolynomial.X i ∉
      (ambientClosedPointOfOverPoint W h).asHomogeneousIdeal := by
    rw [← hpoint]
    exact chartIndexOfOverPoint_spec W g
  have hrangeh : Set.range (ambientMorphismOfOverPoint W h) ⊆
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one' i) (by omega)).opensRange := by
    rw [Proj.opensRange_awayι]
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact (ProjectiveSpectrum.mem_basicOpen
      (homogeneousPieces K) (MvPolynomial.X i) _).2 hih
  let lh : Spec (.of K) ⟶
      Spec (.of (HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X i))) :=
    IsOpenImmersion.lift
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one' i) (by omega))
      (ambientMorphismOfOverPoint W h) hrangeh
  have lhfac : lh ≫
      Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one' i) (by omega) =
      ambientMorphismOfOverPoint W h :=
    IsOpenImmersion.lift_fac
      (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
        (coordinate_mem_degree_one' i) (by omega))
      (ambientMorphismOfOverPoint W h) hrangeh
  let ψ : HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X i) →+* K := (Spec.preimage lh).hom
  have hbaseh : ambientMorphismOfOverPoint W h ≫ projectivePlaneStructureMap K = 𝟙 _ := by
    have hleft : ambientMorphismOfOverPoint W h ≫ projectivePlaneStructureMap K =
        h.left ≫ (toOver W).hom := by
      dsimp only [ambientMorphismOfOverPoint, toOver, structureMap]
      exact Category.assoc _ _ _
    rw [hleft, h.w]
    simp [AffineCommGroupScheme.testObject]
  have hψconst : ψ.comp (coordinateChartConstantHom i) = RingHom.id K := by
    have hlbase : lh ≫ Spec.map
        (CommRingCat.ofHom (coordinateChartConstantHom i)) = 𝟙 _ := by
      calc
        lh ≫ Spec.map (CommRingCat.ofHom (coordinateChartConstantHom i)) =
            lh ≫ (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
              (coordinate_mem_degree_one' i) (by omega) ≫
                projectivePlaneStructureMap K) := by
                  rw [awayι_comp_projectivePlaneStructureMap]
        _ = (lh ≫ Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
              (coordinate_mem_degree_one' i) (by omega)) ≫
                projectivePlaneStructureMap K := (Category.assoc _ _ _).symm
        _ = ambientMorphismOfOverPoint W h ≫ projectivePlaneStructureMap K := by
              rw [lhfac]
        _ = 𝟙 _ := hbaseh
    have hp := congrArg Spec.preimage hlbase
    rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at hp
    exact congrArg CommRingCat.Hom.hom hp
  have hq :
      chartLiftOfOverPoint W g (IsLocalRing.closedPoint K) =
        lh (IsLocalRing.closedPoint K) := by
    apply (Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
      (coordinate_mem_degree_one' i) (by omega)).isOpenEmbedding.injective
    change
      (chartLiftOfOverPoint W g ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
          (coordinate_mem_degree_one' i) (by omega))
          (IsLocalRing.closedPoint K) =
      (lh ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
          (coordinate_mem_degree_one' i) (by omega))
          (IsLocalRing.closedPoint K)
    rw [chartLiftOfOverPoint_fac, lhfac]
    exact hpoint
  have hmemψ (z : HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X i)) :
      z ∈ (lh (IsLocalRing.closedPoint K)).asIdeal ↔ ψ z = 0 := by
    rw [← Spec.map_preimage lh]
    change ψ z ∈ (IsLocalRing.closedPoint K).asIdeal ↔ _
    rw [show (IsLocalRing.closedPoint K).asIdeal = ⊥ from
      IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.mem_bot
  have hφ : chartRingHomOfOverPoint W g = ψ := by
    apply chartRingHom_ext i
    · rw [chartRingHomOfOverPoint_comp_coordinateChartConstantHom,
        hψconst]
    · intro j
      let a := chartRingHomOfOverPoint W g (coordinateChartRatio i j)
      let z := coordinateChartRatio i j - coordinateChartConstantHom i a
      have hzg : chartRingHomOfOverPoint W g z = 0 := by
        have hconst := congrArg (fun f : K →+* K ↦ f a)
          (chartRingHomOfOverPoint_comp_coordinateChartConstantHom W g)
        change chartRingHomOfOverPoint W g (coordinateChartConstantHom i a) = a at hconst
        simp only [z, map_sub, hconst, a, sub_self]
      have hmemg :
          z ∈ (chartLiftOfOverPoint W g (IsLocalRing.closedPoint K)).asIdeal :=
        (mem_chartLift_closedPoint_iff_map_eq_zero W g z).mpr hzg
      have hmemh :
          z ∈ (lh (IsLocalRing.closedPoint K)).asIdeal := by
        rw [← hq]
        exact hmemg
      have hzh : ψ z = 0 := (hmemψ z).mp hmemh
      have hconst := congrArg (fun f : K →+* K ↦ f a)
        hψconst
      change ψ (coordinateChartConstantHom i a) = a at hconst
      change chartRingHomOfOverPoint W g (coordinateChartRatio i j) =
        ψ (coordinateChartRatio i j)
      rw [show chartRingHomOfOverPoint W g (coordinateChartRatio i j) = a from rfl]
      exact (sub_eq_zero.mp (by simpa only [z, map_sub, hconst] using hzh)).symm
  have hpre : Spec.preimage (chartLiftOfOverPoint W g) =
      Spec.preimage lh := by
    ext z
    exact DFunLike.congr_fun hφ z
  have hlift : chartLiftOfOverPoint W g = lh := by
    rw [← Spec.map_preimage (chartLiftOfOverPoint W g),
      ← Spec.map_preimage lh, hpre]
  have hamb : ambientMorphismOfOverPoint W g = ambientMorphismOfOverPoint W h := by
    calc
      ambientMorphismOfOverPoint W g =
          chartLiftOfOverPoint W g ≫
            Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
              (coordinate_mem_degree_one' i) (by omega) :=
        (chartLiftOfOverPoint_fac W g).symm
      _ = lh ≫ Proj.awayι (homogeneousPieces K) (MvPolynomial.X i)
              (coordinate_mem_degree_one' i) (by omega) := by rw [hlift]
      _ = ambientMorphismOfOverPoint W h := lhfac
  let ambientOver : Over (Spec (.of K)) := Over.mk (projectivePlaneStructureMap K)
  let inclusionOver : toOver W ⟶ ambientOver := Over.homMk (inclusion W) (by rfl)
  letI : Mono (inclusion W) :=
    SurjectiveOnStalks.mono_of_injective
      (inclusion W).isClosedEmbedding.toIsEmbedding.injective
  letI : Mono inclusionOver.left := by
    change Mono (inclusion W)
    infer_instance
  letI : Mono inclusionOver := Over.mono_of_mono_left inclusionOver
  have hover : g ≫ inclusionOver = h ≫ inclusionOver := by
    apply Over.OverMorphism.ext
    exact hamb
  exact (cancel_mono inclusionOver).1 hover

/-- Sending the normalized projective point recovered from a scheme-valued point back to the
concrete cubic recovers the original point. -/
theorem recoveredPointOverMorphism_eq
    (W : WeierstrassCurve K) [W.IsElliptic]
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    recoveredPointOverMorphism W g = g :=
  overPoint_eq_of_ambientClosedPoint_eq W _ _
    (ambientClosedPoint_recoveredPointOverMorphism W g)

/-- Every scheme-valued `K`-point of the elliptic cubic comes from a Mathlib projective
Weierstrass point. -/
theorem projectivePointOverMorphism_surjective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Surjective (projectivePointOverMorphism W) := by
  intro g
  exact ⟨projectivePointOfOverPoint W g, recoveredPointOverMorphism_eq W g⟩

/-- The canonical comparison between Mathlib projective points and scheme-valued `K`-points of
the concrete elliptic cubic is bijective. -/
theorem projectivePointOverMorphism_bijective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Bijective (projectivePointOverMorphism W) :=
  ⟨projectivePointOverMorphism_injective W,
    projectivePointOverMorphism_surjective W⟩

/-- The canonical map to rational points of the Tau Ceti abelian variety carried by this exact
cubic is surjective; the proof uses only ellipticity, not group-law compatibility. -/
theorem projectivePointToAbelianVarietyRationalPoint_surjective
    (W : WeierstrassCurve K) [W.IsElliptic]
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom] :
    Function.Surjective (projectivePointToAbelianVarietyRationalPoint W) :=
  projectivePointOverMorphism_surjective W

/-- Multiplicative spelling of the checked surjectivity, ready for
`canonicalProjectivePointEquiv`. -/
theorem projectivePointToAbelianVarietyRationalPoint_surjective_multiplicative
    (W : WeierstrassCurve K) [W.IsElliptic]
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom] :
    Function.Surjective
      (fun P : Multiplicative W.toProjective.Point =>
        projectivePointToAbelianVarietyRationalPoint W P.toAdd) := by
  intro g
  obtain ⟨P, rfl⟩ := projectivePointToAbelianVarietyRationalPoint_surjective W g
  exact ⟨Multiplicative.ofAdd P, rfl⟩

/-- Once the canonical point map is compatible with the group law, its checked point-set
surjectivity supplies the multiplicative equivalence without an additional hypothesis. -/
noncomputable def canonicalProjectivePointEquivOfGroupLaw
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom]
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q) :
    Multiplicative W.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety W) :=
  canonicalProjectivePointEquiv W hzero hadd
    (projectivePointToAbelianVarietyRationalPoint_surjective_multiplicative W)

@[simp]
theorem canonicalProjectivePointEquivOfGroupLaw_apply
    (W : WeierstrassCurve K) [DecidableEq K] [W.IsElliptic]
    [GrpObj (toOver W)] [GeometricallyIntegral (toOver W).hom]
    (hzero : projectivePointToAbelianVarietyRationalPoint W 0 = 1)
    (hadd : ∀ P Q : W.toProjective.Point,
      projectivePointToAbelianVarietyRationalPoint W (P + Q) =
        projectivePointToAbelianVarietyRationalPoint W P *
          projectivePointToAbelianVarietyRationalPoint W Q)
    (P : Multiplicative W.toProjective.Point) :
    canonicalProjectivePointEquivOfGroupLaw W hzero hadd P =
      projectivePointToAbelianVarietyRationalPoint W P.toAdd :=
  rfl

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
