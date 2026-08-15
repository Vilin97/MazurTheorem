/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartGeneratorExtension
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistTripleOverlap

/-!
# Comparing affine-chart ratios with Serre transition functions

The affine chart `D₊(Xⱼ)` has coordinate ring
`(k[X₀, …, X_d]_{Xⱼ})₀`.  Localizing it at the regular function
`Xᵢ / Xⱼ` gives the homogeneous localization at `XⱼXᵢ`.
After commuting the two factors in the denominator, that regular function
is exactly the fraction used to define the Serre transition function.
-/

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MvPolynomial
open SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/-- The scheme-theoretic overlap of two standard open subschemes is the
product projective basic open. -/
def openOverlapToBasicOpenIso (i j : Fin (d + 1)) :
    pullback ((SerreTwist.cover k d).f i)
        ((SerreTwist.cover k d).f j) ≅
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)).toScheme :=
  (isPullback_opens_inf
      (standardChart k i) (standardChart k j)).isoPullback.symm ≪≫
    (scheme k d).isoOfEq
      (by
        change
          Proj.basicOpen (homogeneousGrading k d) (coordinate k i) ⊓
              Proj.basicOpen (homogeneousGrading k d) (coordinate k j) =
            Proj.basicOpen (homogeneousGrading k d)
              (coordinate k i * coordinate k j)
        exact (Proj.basicOpen_mul _ _ _).symm)

/-- The preceding overlap isomorphism is the canonical lift used in the
definition of the Serre transition function. -/
theorem openOverlapToBasicOpenIso_hom
    (i j : Fin (d + 1)) :
    (openOverlapToBasicOpenIso k d i j).hom =
      overlapHom k d i j := by
  rw [← cancel_mono
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)).ι]
  rw [overlapHom_comp_ι]
  rw [glueData_f]
  change
    (openOverlapToBasicOpenIso k d i j).hom ≫
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).ι =
      pullback.fst (standardChart k i).ι
          (standardChart k j).ι ≫
        (standardChart k i).ι
  calc
    _ = (isPullback_opens_inf
          (standardChart k i)
          (standardChart k j)).isoPullback.inv ≫
          (standardChart k i ⊓ standardChart k j).ι := by
      let hBasicOpen :
          standardChart k i ⊓ standardChart k j =
            Proj.basicOpen (homogeneousGrading k d)
              (coordinate k i * coordinate k j) := by
        change
          Proj.basicOpen (homogeneousGrading k d) (coordinate k i) ⊓
              Proj.basicOpen (homogeneousGrading k d) (coordinate k j) = _
        exact (Proj.basicOpen_mul _ _ _).symm
      change
        ((isPullback_opens_inf
              (standardChart k i)
              (standardChart k j)).isoPullback.inv ≫
            ((scheme k d).isoOfEq hBasicOpen).hom) ≫
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j)).ι = _
      calc
        _ = (isPullback_opens_inf
              (standardChart k i)
              (standardChart k j)).isoPullback.inv ≫
            (((scheme k d).isoOfEq hBasicOpen).hom ≫
              (Proj.basicOpen (homogeneousGrading k d)
                (coordinate k i * coordinate k j)).ι) :=
          Category.assoc _ _ _
        _ = _ := CategoryTheory.whisker_eq
          (isPullback_opens_inf
            (standardChart k i)
            (standardChart k j)).isoPullback.inv
          (Scheme.isoOfEq_hom_ι (scheme k d) hBasicOpen)
    _ = ((isPullback_opens_inf
            (standardChart k i)
            (standardChart k j)).isoPullback.inv ≫
          (scheme k d).homOfLE inf_le_left) ≫
            (standardChart k i).ι := by
      rw [Category.assoc, Scheme.homOfLE_ι]
    _ = pullback.fst (standardChart k i).ι
          (standardChart k j).ι ≫
            (standardChart k i).ι := by
      rw [IsPullback.isoPullback_inv_fst]

/-- Explicit affine-spectrum model of the overlap used by the Serre
descent datum. -/
def openOverlapIso (i j : Fin (d + 1)) :
    pullback ((SerreTwist.cover k d).f i)
        ((SerreTwist.cover k d).f j) ≅
      Spec (.of <| Away (homogeneousGrading k d)
        (coordinate k i * coordinate k j)) :=
  openOverlapToBasicOpenIso k d i j ≪≫
    Proj.basicOpenIsoSpec
      (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
      (coordinate_mul_mem_degreeTwo k d i j)
      (by omega)

/-- In the affine-spectrum model of the scheme-theoretic overlap, the
Serre transition function is represented by `awayFraction`. -/
theorem openOverlapIso_appTop_awayFraction
    (i j : Fin (d + 1)) :
    (openOverlapIso k d i j).hom.appTop
        ((Scheme.ΓSpecIso (.of <| Away (homogeneousGrading k d)
          (coordinate k i * coordinate k j))).inv
            (awayFraction k d i j)) =
      (overlapUnit k d i j).val := by
  rw [overlapUnit_val_eq]
  simp only [openOverlapIso, Iso.trans_hom,
    Scheme.Hom.comp_appTop, openOverlapToBasicOpenIso_hom,
    Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top,
    CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- Commuting the two factors in a product denominator induces the
corresponding equivalence of degree-zero homogeneous localizations. -/
def chartProductSwap (i j : Fin (d + 1)) :
    Away (homogeneousGrading k d)
        (coordinate k j * coordinate k i) ≃+*
      Away (homogeneousGrading k d)
        (coordinate k i * coordinate k j) :=
  RingEquiv.cast (mul_comm (coordinate k j) (coordinate k i))

theorem castAway_mk
    {R A : Type} [CommRing R] [CommRing A] [Module R A]
    {𝒜 : ℕ → Submodule R A} [GradedRing 𝒜]
    {f g a : A} {q n : ℕ}
    (hfg : f = g)
    (hf : f ∈ 𝒜 q) (hg : g ∈ 𝒜 q)
    (ha : a ∈ 𝒜 (n • q)) :
    RingEquiv.cast hfg (Away.mk 𝒜 hf n a ha) =
      Away.mk 𝒜 hg n a ha := by
  subst g
  rfl

/-- The image of the affine-chart function `Xᵢ/Xⱼ` in the product
localization is the homogeneous fraction `Xᵢ/Xⱼ` defining the Serre
transition function. -/
theorem chartProductSwap_awayMap_chartRatio
    (i j : Fin (d + 1)) :
    chartProductSwap k d i j
        (awayMap (homogeneousGrading k d)
          (coordinate_mem_degreeOne k i)
          (rfl :
            coordinate k j * coordinate k i =
              coordinate k j * coordinate k i)
          (chartRatio k d i j)) =
      awayFraction k d i j := by
  rw [chartRatio, Away.isLocalizationElem, awayMap_mk]
  simp only [pow_one, awayFraction]
  change
    chartProductSwap k d i j
        (Away.mk (homogeneousGrading k d)
          (coordinate_mul_mem_degreeTwo k d j i) 1
          (coordinate k i * coordinate k i)
          (coordinate_mul_mem_degreeTwo k d i i)) =
      Away.mk (homogeneousGrading k d)
        (coordinate_mul_mem_degreeTwo k d i j) 1
        (coordinate k i * coordinate k i)
        (coordinate_mul_mem_degreeTwo k d i i)
  exact castAway_mk
    (𝒜 := homogeneousGrading k d) (q := 2) (n := 1)
    (mul_comm (coordinate k j) (coordinate k i))
    (coordinate_mul_mem_degreeTwo k d j i)
    (coordinate_mul_mem_degreeTwo k d i j)
    (coordinate_mul_mem_degreeTwo k d i i)

/-- The denominator-swap equivalence, contravariantly on affine spectra. -/
def chartProductSwapSpecIso (i j : Fin (d + 1)) :
    Spec (.of <| Away (homogeneousGrading k d)
        (coordinate k i * coordinate k j)) ≅
      Spec (.of <| Away (homogeneousGrading k d)
        (coordinate k j * coordinate k i)) :=
  Scheme.Spec.mapIso
    (chartProductSwap k d i j).toCommRingCatIso.op

private theorem castAwaySpecIso_hom_awayι
    {R A : Type} [CommRing R] [CommRing A] [Module R A]
    {𝒜 : ℕ → Submodule R A} [GradedRing 𝒜]
    {q : ℕ} {f g : A} (h : f = g)
    (hf : f ∈ 𝒜 q) (hg : g ∈ 𝒜 q) (hq : 0 < q) :
    (Scheme.Spec.mapIso
      (RingEquiv.cast h).toCommRingCatIso.op).hom ≫
        Proj.awayι 𝒜 f hf hq =
      Proj.awayι 𝒜 g hg hq := by
  subst g
  have hhg : hg = hf := Subsingleton.elim _ _
  subst hg
  have he :
      RingEquiv.cast (rfl : f = f) =
        RingEquiv.refl (Away 𝒜 f) := by
    ext x
    rfl
  rw [he]
  simp only [Scheme.Spec_map, Functor.mapIso_hom,
    Iso.op_hom, Quiver.Hom.unop_op]
  have hmap :
      (RingEquiv.refl (Away 𝒜 f)).toCommRingCatIso.hom =
        𝟙 (CommRingCat.of (Away 𝒜 f)) := by
    ext x
    rfl
  rw [hmap, Spec.map_id]
  change
    𝟙 (Scheme.Spec.obj
        (Opposite.op (CommRingCat.of (Away 𝒜 f)))) ≫
        Proj.awayι 𝒜 f hf hq =
      Proj.awayι 𝒜 f hf hq
  exact Category.id_comp _

/-- Commuting a product denominator does not change the corresponding
open immersion into projective space. -/
theorem chartProductSwapSpecIso_inv_awayι
    (i j : Fin (d + 1)) :
    (chartProductSwapSpecIso k d i j).inv ≫
        Proj.awayι (homogeneousGrading k d)
          (coordinate k i * coordinate k j)
          (coordinate_mul_mem_degreeTwo k d i j)
          (by omega) =
      Proj.awayι (homogeneousGrading k d)
        (coordinate k j * coordinate k i)
        (coordinate_mul_mem_degreeTwo k d j i)
        (by omega) := by
  simp only [chartProductSwapSpecIso,
    Functor.mapIso_inv, Iso.op_inv]
  have he :
      (chartProductSwap k d i j).toCommRingCatIso.symm =
        (RingEquiv.cast
          (mul_comm (coordinate k i)
            (coordinate k j))).toCommRingCatIso := by
    ext x
    rfl
  have hehom :
      (chartProductSwap k d i j).toCommRingCatIso.inv =
        (RingEquiv.cast
          (mul_comm (coordinate k i)
            (coordinate k j))).toCommRingCatIso.hom :=
    congrArg Iso.hom he
  rw [hehom]
  exact
    castAwaySpecIso_hom_awayι
      (R := k)
      (A := MvPolynomial (Fin (d + 1)) k)
      (𝒜 := homogeneousGrading k d)
      (q := 2)
      (f := coordinate k i * coordinate k j)
      (g := coordinate k j * coordinate k i)
      (mul_comm (coordinate k i) (coordinate k j))
      (coordinate_mul_mem_degreeTwo k d i j)
      (coordinate_mul_mem_degreeTwo k d j i)
      (by omega)

/-- The basic open `D(Xᵢ/Xⱼ)` inside the `j`-th affine chart is the
spectrum of the homogeneous localization at `XⱼXᵢ`. -/
def chartRatioOpenIso (i j : Fin (d + 1)) :
    (show (Spec (chartRing k d j)).Opens from
      PrimeSpectrum.basicOpen
        (chartRatioElement k d i j)).toScheme ≅
      Spec (.of <| Away (homogeneousGrading k d)
        (coordinate k j * coordinate k i)) := by
  change
    (show
      (Spec (.of <| Away (homogeneousGrading k d)
        (coordinate k j))).Opens
      from PrimeSpectrum.basicOpen (chartRatio k d i j)).toScheme ≅
      Spec (.of <| Away (homogeneousGrading k d)
        (coordinate k j * coordinate k i))
  let a : Away (homogeneousGrading k d)
        (coordinate k j) →+*
      Away (homogeneousGrading k d)
        (coordinate k j * coordinate k i) :=
    awayMap (homogeneousGrading k d)
      (coordinate_mem_degreeOne k i)
      (rfl :
        coordinate k j * coordinate k i =
          coordinate k j * coordinate k i)
  letI := a.toAlgebra
  letI :
      IsLocalization.Away (chartRatio k d i j)
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i)) := by
    change
      IsLocalization.Away
        (Away.isLocalizationElem
          (coordinate_mem_degreeOne k j)
          (coordinate_mem_degreeOne k i))
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i))
    exact Away.isLocalization_mul
      (coordinate_mem_degreeOne k j)
      (coordinate_mem_degreeOne k i)
      rfl Nat.one_ne_zero
  let ψ :
      Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i)) ⟶
        Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j)) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap
        (Away (homogeneousGrading k d) (coordinate k j))
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i))))
  letI : IsOpenImmersion ψ := by
    dsimp only [ψ]
    exact IsOpenImmersion.of_isLocalization
      (chartRatio k d i j)
  have hRange :
      ψ.opensRange =
        PrimeSpectrum.basicOpen
          (chartRatio k d i j) := by
    apply TopologicalSpace.Opens.ext
    exact
      PrimeSpectrum.localization_away_comap_range
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i))
        (chartRatio k d i j)
  exact
    IsOpenImmersion.isoOfRangeEq
      (show (Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j))).Opens from
        PrimeSpectrum.basicOpen
          (chartRatio k d i j)).ι
      ψ (by
        rw [Scheme.Opens.range_ι,
          ← Scheme.Hom.coe_opensRange]
        exact congrArg SetLike.coe hRange.symm)

/-- The affine-spectrum model of the ratio basic open factors its
inclusion into the `j`-th chart through the localization morphism. -/
theorem chartRatioOpenIso_hom_fac
    (i j : Fin (d + 1)) :
    (chartRatioOpenIso k d i j).hom ≫
        Spec.map (CommRingCat.ofHom
          (awayMap (homogeneousGrading k d)
            (coordinate_mem_degreeOne k i)
            (rfl :
              coordinate k j * coordinate k i =
                coordinate k j * coordinate k i))) =
      (show
        (Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j))).Opens
        from
        PrimeSpectrum.basicOpen
          (chartRatio k d i j)).ι := by
  let a : Away (homogeneousGrading k d)
        (coordinate k j) →+*
      Away (homogeneousGrading k d)
        (coordinate k j * coordinate k i) :=
    awayMap (homogeneousGrading k d)
      (coordinate_mem_degreeOne k i)
      (rfl :
        coordinate k j * coordinate k i =
          coordinate k j * coordinate k i)
  letI := a.toAlgebra
  letI :
      IsLocalization.Away (chartRatio k d i j)
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i)) := by
    change
      IsLocalization.Away
        (Away.isLocalizationElem
          (coordinate_mem_degreeOne k j)
          (coordinate_mem_degreeOne k i))
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i))
    exact Away.isLocalization_mul
      (coordinate_mem_degreeOne k j)
      (coordinate_mem_degreeOne k i)
      rfl Nat.one_ne_zero
  let ψ :
      Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i)) ⟶
        Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j)) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap
        (Away (homogeneousGrading k d) (coordinate k j))
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i))))
  letI : IsOpenImmersion ψ := by
    dsimp only [ψ]
    exact IsOpenImmersion.of_isLocalization
      (chartRatio k d i j)
  have hRange :
      ψ.opensRange =
        PrimeSpectrum.basicOpen
          (chartRatio k d i j) := by
    apply TopologicalSpace.Opens.ext
    exact
      PrimeSpectrum.localization_away_comap_range
        (Away (homogeneousGrading k d)
          (coordinate k j * coordinate k i))
        (chartRatio k d i j)
  have he :
      Set.range
          (show (Spec (.of <| Away (homogeneousGrading k d)
            (coordinate k j))).Opens from
            PrimeSpectrum.basicOpen
              (chartRatio k d i j)).ι =
        Set.range ψ := by
    rw [Scheme.Opens.range_ι,
      ← Scheme.Hom.coe_opensRange]
    exact congrArg SetLike.coe hRange.symm
  change
    (chartRatioOpenIso k d i j).hom ≫
        ψ =
      (show
        (Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j))).Opens
        from PrimeSpectrum.basicOpen
          (chartRatio k d i j)).ι
  unfold chartRatioOpenIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ he

/-- After commuting the product denominator, the affine-chart ratio basic
open has the same explicit spectrum model as the Serre overlap. -/
def chartRatioOpenToProductIso (i j : Fin (d + 1)) :
    (show (Spec (chartRing k d j)).Opens from
      PrimeSpectrum.basicOpen
        (chartRatioElement k d i j)).toScheme ≅
      Spec (.of <| Away (homogeneousGrading k d)
        (coordinate k i * coordinate k j)) :=
  chartRatioOpenIso k d i j ≪≫
    (chartProductSwapSpecIso k d i j).symm

/-- The ratio basic open, identified directly with the corresponding
projective product basic open. -/
def chartRatioOpenToBasicOpenIso (i j : Fin (d + 1)) :
    (show (Spec (chartRing k d j)).Opens from
      PrimeSpectrum.basicOpen
        (chartRatioElement k d i j)).toScheme ≅
      (Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)).toScheme :=
  chartRatioOpenToProductIso k d i j ≪≫
    (Proj.basicOpenIsoSpec
      (homogeneousGrading k d)
      (coordinate k i * coordinate k j)
      (coordinate_mul_mem_degreeTwo k d i j)
      (by omega)).symm

/-- The preceding isomorphism is over projective space: its product-open
inclusion is the original ratio-open inclusion followed by the standard
chart immersion. -/
theorem chartRatioOpenToBasicOpenIso_hom_ι
    (i j : Fin (d + 1)) :
    (chartRatioOpenToBasicOpenIso k d i j).hom ≫
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).ι =
      (show (Spec (chartRing k d j)).Opens from
        PrimeSpectrum.basicOpen
          (chartRatioElement k d i j)).ι ≫
        (standardAffineOpenCover k d).f j := by
  change
    (chartRatioOpenToBasicOpenIso k d i j).hom ≫
        (Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).ι =
      (show
        (Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j))).Opens
        from PrimeSpectrum.basicOpen
          (chartRatio k d i j)).ι ≫
        (standardAffineOpenCover k d).f j
  calc
    _ = (chartRatioOpenIso k d i j).hom ≫
          (chartProductSwapSpecIso k d i j).inv ≫
          Proj.awayι (homogeneousGrading k d)
            (coordinate k i * coordinate k j)
            (coordinate_mul_mem_degreeTwo k d i j)
            (by omega) := by
      simp only [chartRatioOpenToBasicOpenIso,
        chartRatioOpenToProductIso, Iso.trans_hom,
        Iso.symm_hom, Category.assoc]
      rw [Proj.basicOpenIsoSpec_inv_ι]
    _ = (chartRatioOpenIso k d i j).hom ≫
          Proj.awayι (homogeneousGrading k d)
            (coordinate k j * coordinate k i)
            (coordinate_mul_mem_degreeTwo k d j i)
            (by omega) := by
      rw [chartProductSwapSpecIso_inv_awayι]
    _ = (chartRatioOpenIso k d i j).hom ≫
          Spec.map (CommRingCat.ofHom
            (awayMap (homogeneousGrading k d)
              (coordinate_mem_degreeOne k i)
              (rfl :
                coordinate k j * coordinate k i =
                  coordinate k j * coordinate k i))) ≫
          Proj.awayι (homogeneousGrading k d)
            (coordinate k j)
            (coordinate_mem_degreeOne k j)
            Nat.zero_lt_one := by
      rw [Proj.SpecMap_awayMap_awayι]
    _ = _ := by
      rw [← Category.assoc,
        chartRatioOpenIso_hom_fac]
      rfl

/-- Pulling the Serre overlap fraction back to the affine-chart ratio
basic open agrees with restricting the chart function `Xᵢ/Xⱼ`. -/
theorem chartRatioOpenToProductIso_appTop_awayFraction
    (i j : Fin (d + 1)) :
    (chartRatioOpenToProductIso k d i j).hom.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k i * coordinate k j))).inv
            (awayFraction k d i j)) =
      (show (Spec (chartRing k d j)).Opens from
        PrimeSpectrum.basicOpen
          (chartRatioElement k d i j)).ι.appTop
        ((Scheme.ΓSpecIso (chartRing k d j)).inv
          (chartRatioElement k d i j)) := by
  change
    (chartRatioOpenToProductIso k d i j).hom.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k i * coordinate k j))).inv
            (awayFraction k d i j)) =
      (show
        (Spec (.of <| Away (homogeneousGrading k d)
          (coordinate k j))).Opens
        from PrimeSpectrum.basicOpen
          (chartRatio k d i j)).ι.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k j))).inv
            (chartRatio k d i j))
  have hring :
      (chartProductSwap k d i j).symm
          (awayFraction k d i j) =
        awayMap (homogeneousGrading k d)
          (coordinate_mem_degreeOne k i)
          (rfl :
            coordinate k j * coordinate k i =
              coordinate k j * coordinate k i)
          (chartRatio k d i j) := by
    have h := congrArg (chartProductSwap k d i j).symm
      (chartProductSwap_awayMap_chartRatio k d i j)
    simpa only [RingEquiv.symm_apply_apply] using h.symm
  have hswap :
      (Spec.map
          (chartProductSwap k d i j).toCommRingCatIso.inv).appTop
          ((Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k i * coordinate k j))).inv
              (awayFraction k d i j)) =
        (Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k j * coordinate k i))).inv
            (awayMap (homogeneousGrading k d)
              (coordinate_mem_degreeOne k i)
              (rfl :
                coordinate k j * coordinate k i =
                  coordinate k j * coordinate k i)
              (chartRatio k d i j)) := by
    calc
      _ = (Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k j * coordinate k i))).inv
          ((chartProductSwap k d i j).symm
            (awayFraction k d i j)) := by
        rw [← CommRingCat.comp_apply,
          ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      _ = _ := congrArg _ hring
  have haway :
      (Spec.map (CommRingCat.ofHom
          (awayMap (homogeneousGrading k d)
            (coordinate_mem_degreeOne k i)
            (rfl :
              coordinate k j * coordinate k i =
                coordinate k j * coordinate k i)))).appTop
          ((Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k j))).inv
              (chartRatio k d i j)) =
        (Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k j * coordinate k i))).inv
            (awayMap (homogeneousGrading k d)
              (coordinate_mem_degreeOne k i)
              (rfl :
                coordinate k j * coordinate k i =
                  coordinate k j * coordinate k i)
              (chartRatio k d i j)) := by
    rw [← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    rfl
  rw [← chartRatioOpenIso_hom_fac k d i j]
  simp only [chartRatioOpenToProductIso, Iso.trans_hom,
    Scheme.Hom.comp_appTop]
  simp only [chartProductSwapSpecIso]
  calc
    _ = (chartRatioOpenIso k d i j).hom.appTop
          ((Scheme.ΓSpecIso (.of <| Away
            (homogeneousGrading k d)
            (coordinate k j * coordinate k i))).inv
              (awayMap (homogeneousGrading k d)
                (coordinate_mem_degreeOne k i)
                (rfl :
                  coordinate k j * coordinate k i =
                    coordinate k j * coordinate k i)
                (chartRatio k d i j))) :=
      congrArg (chartRatioOpenIso k d i j).hom.appTop hswap
    _ = (chartRatioOpenIso k d i j).hom.appTop
          ((Spec.map (CommRingCat.ofHom
            (awayMap (homogeneousGrading k d)
              (coordinate_mem_degreeOne k i)
              (rfl :
                coordinate k j * coordinate k i =
                  coordinate k j * coordinate k i)))).appTop
            ((Scheme.ΓSpecIso (.of <| Away
              (homogeneousGrading k d)
              (coordinate k j))).inv
                (chartRatio k d i j))) :=
      congrArg (chartRatioOpenIso k d i j).hom.appTop haway.symm
    _ = _ := (CommRingCat.comp_apply _ _ _).symm

/-- On structure-sheaf sections, the ratio-open/product-open
identification sends the homogeneous fraction to the restricted affine
chart ratio. -/
theorem chartRatioOpenToBasicOpenIso_appTop_awayFraction
    (i j : Fin (d + 1)) :
    (chartRatioOpenToBasicOpenIso k d i j).hom.appTop
        ((Proj.basicOpen (homogeneousGrading k d)
          (coordinate k i * coordinate k j)).topIso.inv
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i * coordinate k j)
            (awayFraction k d i j))) =
      (show (Spec (chartRing k d j)).Opens from
        PrimeSpectrum.basicOpen
          (chartRatioElement k d i j)).ι.appTop
        ((Scheme.ΓSpecIso (chartRing k d j)).inv
          (chartRatioElement k d i j)) := by
  have hspec :
      (Proj.basicOpenIsoSpec
        (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
        (coordinate_mul_mem_degreeTwo k d i j)
        (by omega)).inv.appTop
          ((Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j)).topIso.inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k i * coordinate k j)
              (awayFraction k d i j))) =
        (Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k i * coordinate k j))).inv
            (awayFraction k d i j) := by
    let e :=
      Proj.basicOpenIsoSpec
        (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
        (coordinate_mul_mem_degreeTwo k d i j)
        (by omega)
    have hhom :
        e.hom.appTop
            ((Scheme.ΓSpecIso (.of <| Away
              (homogeneousGrading k d)
              (coordinate k i * coordinate k j))).inv
                (awayFraction k d i j)) =
          (Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j)).topIso.inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k i * coordinate k j)
              (awayFraction k d i j)) := by
      dsimp only [e]
      simp only [Proj.basicOpenIsoSpec_hom,
        Proj.basicOpenToSpec_app_top,
        CommRingCat.comp_apply, Iso.inv_hom_id_apply]
      rw [CommRingCat.comp_apply]
    calc
      _ = e.inv.appTop
          (e.hom.appTop
            ((Scheme.ΓSpecIso (.of <| Away
              (homogeneousGrading k d)
              (coordinate k i * coordinate k j))).inv
                (awayFraction k d i j))) :=
        congrArg e.inv.appTop hhom.symm
      _ = _ := by
        rw [← CommRingCat.comp_apply,
          ← Scheme.Hom.comp_appTop]
        simp
  change
    (chartRatioOpenToProductIso k d i j).hom.appTop
        ((Proj.basicOpenIsoSpec
          (homogeneousGrading k d)
          (coordinate k i * coordinate k j)
          (coordinate_mul_mem_degreeTwo k d i j)
          (by omega)).inv.appTop
          ((Proj.basicOpen (homogeneousGrading k d)
            (coordinate k i * coordinate k j)).topIso.inv
            (Proj.awayToSection (homogeneousGrading k d)
              (coordinate k i * coordinate k j)
              (awayFraction k d i j)))) =
      (show (Spec (chartRing k d j)).Opens from
        PrimeSpectrum.basicOpen
          (chartRatioElement k d i j)).ι.appTop
        ((Scheme.ΓSpecIso (chartRing k d j)).inv
          (chartRatioElement k d i j))
  calc
    _ = (chartRatioOpenToProductIso k d i j).hom.appTop
        ((Scheme.ΓSpecIso (.of <| Away
          (homogeneousGrading k d)
          (coordinate k i * coordinate k j))).inv
            (awayFraction k d i j)) :=
      congrArg
        (chartRatioOpenToProductIso k d i j).hom.appTop hspec
    _ = _ :=
      chartRatioOpenToProductIso_appTop_awayFraction
        k d i j

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
