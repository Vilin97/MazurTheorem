/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.AffineIdealSheafPullback
import MazurTorsion.AlgebraicGeometry.Jacobian.OrderedIncidenceOpenRestriction

/-!
# Pullback preserves products of ideal sheaves

Scheme-theoretic pullback of an ideal sheaf preserves finite products along
an arbitrary scheme morphism.  The proof is local on the source.  Around
each source point, choose an affine open mapping into an affine target open.
The target restriction preserves products because it is an open immersion,
and the resulting morphism between affine schemes preserves products by the
right-exact tensor-product calculation in `AffineIdealSheafPullback`.

The named downstream consumer is `GeometricAssignedRefinedSupportQuotient`,
where this theorem identifies the assembled refined graph-product ideal with
the genuine pullback of the universal ordered-incidence ideal.
-/

noncomputable section

universe u v

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.IdealSheafPullbackProduct

open AffineIdealSheafPullback
open OrderedIncidenceOpenRestriction
open UniversalEffectiveDivisor

/-- Pullback along any scheme morphism preserves products of ideal sheaves. -/
theorem idealSheaf_comap_mul
    {X Y : Scheme.{u}} (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  classical
  have hU : ∀ x : X, ∃ U : Y.affineOpens, f x ∈ U.1 := by
    intro x
    obtain ⟨_, ⟨U, hUa, rfl⟩, hfx, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f x)) isOpen_univ
    exact ⟨⟨U, hUa⟩, hfx⟩
  choose U hxU using hU
  have hV : ∀ x : X, ∃ V : X.affineOpens,
      x ∈ V.1 ∧ V.1 ≤ f ⁻¹ᵁ (U x).1 := by
    intro x
    obtain ⟨_, ⟨V, hVa, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (hxU x) ((f ⁻¹ᵁ (U x).1).2)
    exact ⟨⟨V, hVa⟩, hxV, hVU⟩
  choose V hxV hVU using hV
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
  · apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  · intro x
    let g : (V x).1.toScheme ⟶ (U x).1.toScheme :=
      X.homOfLE (hVU x) ≫ f ∣_ (U x).1
    have hfac : (V x).1.ι ≫ f = g ≫ (U x).1.ι := by
      dsimp only [g]
      rw [Category.assoc, morphismRestrict_ι,
        ← Category.assoc, Scheme.homOfLE_ι]
    have hlocal :
        ((I * J).comap f).comap (V x).1.ι =
          (I.comap f * J.comap f).comap (V x).1.ι := by
      calc
        ((I * J).comap f).comap (V x).1.ι =
            (I * J).comap ((V x).1.ι ≫ f) :=
          (Scheme.IdealSheafData.comap_comp
            (I * J) (V x).1.ι f).symm
        _ = (I * J).comap (g ≫ (U x).1.ι) := by rw [hfac]
        _ = ((I * J).comap (U x).1.ι).comap g :=
          Scheme.IdealSheafData.comap_comp (I * J) g (U x).1.ι
        _ = (I.comap (U x).1.ι * J.comap (U x).1.ι).comap g := by
          rw [idealSheaf_comap_mul_of_isOpenImmersion]
        _ = (I.comap (U x).1.ι).comap g *
              (J.comap (U x).1.ι).comap g :=
          idealSheaf_comap_mul_of_isAffine _ _ g
        _ = I.comap (g ≫ (U x).1.ι) *
              J.comap (g ≫ (U x).1.ι) := by
          simp only [g, ← Scheme.IdealSheafData.comap_comp]
        _ = I.comap ((V x).1.ι ≫ f) *
              J.comap ((V x).1.ι ≫ f) := by rw [hfac]
        _ = (I.comap f).comap (V x).1.ι *
              (J.comap f).comap (V x).1.ι := by
          rw [Scheme.IdealSheafData.comap_comp,
            Scheme.IdealSheafData.comap_comp]
        _ = (I.comap f * J.comap f).comap (V x).1.ι :=
          (idealSheaf_comap_mul_of_isOpenImmersion
            (I.comap f) (J.comap f) (V x).1.ι).symm
    let Wtop : (V x).1.toScheme.affineOpens :=
      ⟨⊤, @isAffineOpen_top (V x).1.toScheme
        (inferInstance : IsAffine (V x).1.toScheme)⟩
    have htop := congrArg
      (fun L : (V x).1.toScheme.IdealSheafData ↦
        L.ideal Wtop) hlocal
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
        ((I * J).comap f) (V x).1.ι Wtop,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
        (I.comap f * J.comap f) (V x).1.ι Wtop] at htop
    have himage := Ideal.comap_injective_of_surjective
      ((V x).1.ι.appIso Wtop).inv.hom
      (ConcreteCategory.bijective_of_isIso
        ((V x).1.ι.appIso Wtop).inv).2 htop
    dsimp only [Wtop] at himage
    let Wimage : X.affineOpens :=
      ⟨(V x).1.ι ''ᵁ (⊤ : (V x).1.toScheme.Opens),
        (@isAffineOpen_top (V x).1.toScheme
          (inferInstance : IsAffine (V x).1.toScheme)).image_of_isOpenImmersion
            (V x).1.ι⟩
    change ((I * J).comap f).ideal Wimage =
      (I.comap f * J.comap f).ideal Wimage at himage
    have hWimage : Wimage = V x := by
      apply Subtype.ext
      exact Scheme.Opens.ι_image_top (V x).1
    rw [hWimage] at himage
    exact himage

/-- Pullback along any scheme morphism preserves finite products of ideal
sheaves. -/
theorem idealSheaf_comap_finsetProd
    {X Y : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (F : ι → Y.IdealSheafData) (f : X ⟶ Y) :
    (s.prod F).comap f = s.prod (fun i ↦ (F i).comap f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        idealSheaf_comap_mul, ih]

/-- Ideal sheaves on a coproduct of affine schemes agree if their pullbacks
to every coproduct summand agree. -/
theorem idealSheafData_ext_sigma
    {ι : Type v} [Small.{u} ι] (F : ι → Scheme.{u})
    [∀ i, IsAffine (F i)]
    (I J : (∐ F : Scheme.{u}).IdealSheafData)
    (h : ∀ i, I.comap (Sigma.ι F i) = J.comap (Sigma.ι F i)) :
    I = J := by
  classical
  let W (i : ι) : (∐ F : Scheme.{u}).affineOpens :=
    ⟨(Sigma.ι F i).opensRange, isAffineOpen_opensRange (Sigma.ι F i)⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top W
  · change ⨆ i, (Sigma.ι F i).opensRange = ⊤
    exact Scheme.OpenCover.iSup_opensRange (sigmaOpenCover F)
  · intro i
    let Utop : (F i).affineOpens :=
      ⟨⊤, @isAffineOpen_top (F i) (inferInstance : IsAffine (F i))⟩
    have htop := congrArg
      (fun L : (F i).IdealSheafData ↦ L.ideal Utop) (h i)
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
        I (Sigma.ι F i) Utop,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
        J (Sigma.ι F i) Utop] at htop
    have himage := Ideal.comap_injective_of_surjective
      ((Sigma.ι F i).appIso Utop).inv.hom
      (ConcreteCategory.bijective_of_isIso
        ((Sigma.ι F i).appIso Utop).inv).2 htop
    dsimp only [Utop] at himage
    let Wimage : (∐ F : Scheme.{u}).affineOpens :=
      ⟨Sigma.ι F i ''ᵁ (⊤ : (F i).Opens),
        (@isAffineOpen_top (F i)
          (inferInstance : IsAffine (F i))).image_of_isOpenImmersion
            (Sigma.ι F i)⟩
    change I.ideal Wimage = J.ideal Wimage at himage
    have hWimage : Wimage = W i := by
      apply Subtype.ext
      change Sigma.ι F i ''ᵁ (⊤ : (F i).Opens) =
        (Sigma.ι F i).opensRange
      exact Scheme.Hom.image_top_eq_opensRange (Sigma.ι F i)
    rw [hWimage] at himage
    exact himage

/-- The pullback of the universal ordered-incidence ideal along an arbitrary
scheme morphism is the product of the pulled-back coordinate-graph ideals. -/
theorem orderedIncidenceIdeal_comap
    (S : Scheme.{u}) (d : ℕ) (X : Over S) [IsSeparated X.hom]
    {Y : Scheme.{u}} (f : Y ⟶ (orderedAmbient S d X).left) :
    (orderedIncidenceIdeal S d X).comap f =
      Finset.univ.prod (fun i ↦ (coordinateGraphIdeal S d X i).comap f) :=
  idealSheaf_comap_finsetProd
    Finset.univ (coordinateGraphIdeal S d X) f

/-- The arbitrary pullback of ordered incidence is the product of the
kernels of the pulled-back coordinate graphs. -/
theorem orderedIncidenceIdeal_comap_eq_prod_pullbackKernels
    (S : Scheme.{u}) (d : ℕ) (X : Over S) [IsSeparated X.hom]
    {Y : Scheme.{u}} (f : Y ⟶ (orderedAmbient S d X).left) :
    (orderedIncidenceIdeal S d X).comap f =
      Finset.univ.prod (fun i ↦
        (pullback.fst f (coordinateGraphι S d X i).left).ker) := by
  rw [orderedIncidenceIdeal_comap]
  congr 1
  funext i
  exact coordinateGraphIdeal_comap_eq_pullbackKernel S d X f i

end MazurTorsion.AlgebraicGeometry.Jacobian.IdealSheafPullbackProduct
