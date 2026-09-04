/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveGroupLaw

/-!
# Associativity and the canonical projective Weierstrass group object

This module proves associativity of the globally glued projective addition.
Its design boundary is the standard-by-standard chart of the triple product:
the three universal chart points are evaluated in the fraction field of the
triple tensor coordinate ring, where Mathlib's checked elliptic-curve point
group supplies associativity.  Explicit tensor contractions prove that every
denominator used by the two iterated additions is nonzero.  Dominance of the
generic point and separatedness of the cubic then extend the equality to the
entire triple product.

The named downstream consumer is `projectiveGrpObj`, which packages the
global addition, infinity section, and negation as the canonical `GrpObj`
structure used by the represented modular-curve interfaces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped WeierstrassCurve.Projective

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u
variable {K : Type u} [Field K]

private abbrev A (W : WeierstrassCurve K) :=
  coveringChartCoordinateRing W true

private abbrev B (W : WeierstrassCurve K) :=
  TensorProduct K (A W) (A W)

private abbrev T (W : WeierstrassCurve K) :=
  TensorProduct K (B W) (A W)

private noncomputable instance t_nontrivial
    (W : WeierstrassCurve K) [W.IsElliptic] : Nontrivial (T W) := by
  letI : IsDomain (B W) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  letI : Nontrivial (B W) :=
    (projectivePairChartCoordinateRing_isDomain W (true, true)).toNontrivial
  letI : IsDomain (A W) := coveringChartCoordinateRing_isDomain W true
  letI : Module.Free K (B W) := Module.Free.of_divisionRing K (B W)
  letI : Module.Flat K (B W) := Module.Flat.of_free
  have hA : Function.Injective (algebraMap K (A W)) :=
    RingHom.injective (algebraMap K (A W))
  exact (Algebra.TensorProduct.includeLeft_injective
    (R := K) (S := K) (A := B W) (B := A W) hA).nontrivial

private noncomputable abbrev Triple (W : WeierstrassCurve K) : Scheme :=
  pullback (projectivePairStructureMap W) (structureMap W)

private noncomputable def tripleCover (W : WeierstrassCurve K) :
    (Triple W).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (projectivePairOpenCover W)
    (coveringChartsOpenCover W) (projectivePairStructureMap W)
      (structureMap W)

private noncomputable abbrev U (W : WeierstrassCurve K) : Scheme :=
  (tripleCover W).X ((true, true), true)

private noncomputable abbrev uMap (W : WeierstrassCurve K) : U W ⟶ Triple W :=
  (tripleCover W).f ((true, true), true)

private noncomputable def uFst (W : WeierstrassCurve K) :
    U W ⟶ projectivePairChartScheme W (true, true) :=
  pullback.fst
    (projectivePairChartMap W (true, true) ≫ projectivePairStructureMap W)
    (coveringChartMap W true ≫ structureMap W)

private noncomputable def uSnd (W : WeierstrassCurve K) :
    U W ⟶ coveringChartScheme W true :=
  pullback.snd
    (projectivePairChartMap W (true, true) ≫ projectivePairStructureMap W)
    (coveringChartMap W true ≫ structureMap W)

private instance uMap_open (W : WeierstrassCurve K) :
    IsOpenImmersion (uMap W) :=
  (tripleCover W).map_prop ((true, true), true)

private theorem uMap_fst (W : WeierstrassCurve K) :
    uMap W ≫ pullback.fst
        (projectivePairStructureMap W) (structureMap W) =
      uFst W ≫ projectivePairChartMap W (true, true) := by
  change pullback.map
      (projectivePairChartMap W (true, true) ≫
        projectivePairStructureMap W)
      (coveringChartMap W true ≫ structureMap W)
      (projectivePairStructureMap W) (structureMap W)
      (projectivePairChartMap W (true, true))
      (coveringChartMap W true) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫
        pullback.fst (projectivePairStructureMap W) (structureMap W) = _
  change pullback.lift _ _ _ ≫
      pullback.fst (projectivePairStructureMap W) (structureMap W) = _
  rw [pullback.lift_fst]
  rfl

private theorem uMap_snd (W : WeierstrassCurve K) :
    uMap W ≫ pullback.snd
        (projectivePairStructureMap W) (structureMap W) =
      uSnd W ≫ coveringChartMap W true := by
  change pullback.map
      (projectivePairChartMap W (true, true) ≫
        projectivePairStructureMap W)
      (coveringChartMap W true ≫ structureMap W)
      (projectivePairStructureMap W) (structureMap W)
      (projectivePairChartMap W (true, true))
      (coveringChartMap W true) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫
        pullback.snd (projectivePairStructureMap W) (structureMap W) = _
  change pullback.lift _ _ _ ≫
      pullback.snd (projectivePairStructureMap W) (structureMap W) = _
  rw [pullback.lift_snd]
  rfl

private theorem pairChart_comp_base (W : WeierstrassCurve K) :
    projectivePairChartMap W (true, true) ≫ projectivePairStructureMap W =
      pullback.fst
          (coveringChartMap W true ≫ structureMap W)
          (coveringChartMap W true ≫ structureMap W) ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W true)) := by
  calc
    _ = (projectivePairChartMap W (true, true) ≫
          pullback.fst (structureMap W) (structureMap W)) ≫
        structureMap W := by
          rw [projectivePairStructureMap, Category.assoc]
    _ = (pullback.fst
            (coveringChartMap W true ≫ structureMap W)
            (coveringChartMap W true ≫ structureMap W) ≫
          coveringChartMap W true) ≫ structureMap W := by
            rw [projectivePairChartMap_comp_fst]
    _ = pullback.fst
          (coveringChartMap W true ≫ structureMap W)
          (coveringChartMap W true ≫ structureMap W) ≫
        (coveringChartMap W true ≫ structureMap W) :=
      Category.assoc _ _ _
    _ = _ := congrArg
      (fun q ↦ pullback.fst
          (coveringChartMap W true ≫ structureMap W)
          (coveringChartMap W true ≫ structureMap W) ≫ q)
      (coveringChartMap_comp_structureMap W true)

private theorem pairSpec_comp_base (W : WeierstrassCurve K) :
    (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
        projectivePairChartMap W (true, true) ≫
          projectivePairStructureMap W =
      Spec.map (CommRingCat.ofHom (algebraMap K (B W))) := by
  apply (cancel_epi
    (projectivePairChartIsoSpecTensor W (true, true)).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [pairChart_comp_base]
  exact (projectivePairChartIsoSpecTensor_hom_base W (true, true)).symm

private theorem pairIso_comp_base (W : WeierstrassCurve K) :
    (projectivePairChartIsoSpecTensor W (true, true)).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (B W))) =
      projectivePairChartMap W (true, true) ≫
        projectivePairStructureMap W := by
  rw [projectivePairChartIsoSpecTensor_hom_base,
    pairChart_comp_base]

private theorem uPullbackSquare (W : WeierstrassCurve K) :
    IsPullback
      (uFst W ≫
        (projectivePairChartIsoSpecTensor W (true, true)).hom)
      (uSnd W)
      (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))) := by
  let h := IsPullback.of_hasPullback
    (projectivePairChartMap W (true, true) ≫
      projectivePairStructureMap W)
    (coveringChartMap W true ≫ structureMap W)
  exact h.of_iso (Iso.refl _)
    (projectivePairChartIsoSpecTensor W (true, true))
    (Iso.refl _) (Iso.refl _)
    (by
      change pullback.fst _ _ ≫
          (projectivePairChartIsoSpecTensor W (true, true)).hom =
        𝟙 _ ≫ (pullback.fst _ _ ≫
          (projectivePairChartIsoSpecTensor W (true, true)).hom)
      exact (Category.id_comp _).symm)
    (by
      change pullback.snd _ _ ≫ 𝟙 _ =
        𝟙 _ ≫ pullback.snd _ _
      exact (Category.comp_id _).trans (Category.id_comp _).symm) (by
      simpa using (pairIso_comp_base W).symm) (by
      simpa using coveringChartMap_comp_structureMap W true)

private theorem tPullbackSquare (W : WeierstrassCurve K) :
    IsPullback
      (pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
        (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))))
      (pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
        (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))) :=
  IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
    (Spec.map (CommRingCat.ofHom (algebraMap K (A W))))

private noncomputable def uIsoPullback (W : WeierstrassCurve K) :
    U W ≅ pullback
    (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
    (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))) :=
  (uPullbackSquare W).isoIsPullback
    (Spec (.of (B W))) (Spec (.of (A W))) (tPullbackSquare W)

private theorem uIsoPullback_inv_fst (W : WeierstrassCurve K) :
    (uIsoPullback W).inv ≫
        (uFst W ≫
          (projectivePairChartIsoSpecTensor W (true, true)).hom) =
      pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
        (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))) := by
  exact (uPullbackSquare W).isoIsPullback_inv_fst
    (Spec (.of (B W))) (Spec (.of (A W))) (tPullbackSquare W)

private theorem uIsoPullback_inv_snd (W : WeierstrassCurve K) :
    (uIsoPullback W).inv ≫ uSnd W =
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
        (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))) := by
  exact (uPullbackSquare W).isoIsPullback_inv_snd
    (Spec (.of (B W))) (Spec (.of (A W))) (tPullbackSquare W)

private noncomputable def uIsoSpec (W : WeierstrassCurve K) :
    U W ≅ Spec (.of (T W)) :=
  (uIsoPullback W).trans (pullbackSpecIso K (B W) (A W))

private theorem uIsoSpec_inv_fst (W : WeierstrassCurve K) :
    (uIsoSpec W).inv ≫ uFst W =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := K) (A := B W) (B := A W))) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv := by
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, true)).hom).1
  calc
    ((uIsoSpec W).inv ≫ uFst W) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).hom =
      (pullbackSpecIso K (B W) (A W)).inv ≫
        ((uIsoPullback W).inv ≫
          (uFst W ≫
              (projectivePairChartIsoSpecTensor W (true, true)).hom)) := by
                rw [uIsoSpec, Iso.trans_inv]
                simp only [Category.assoc]
    _ = (pullbackSpecIso K (B W) (A W)).inv ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap K (B W))))
          (Spec.map (CommRingCat.ofHom (algebraMap K (A W)))) := by
            rw [uIsoPullback_inv_fst]
    _ = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom
          (R := K) (A := B W) (B := A W))) :=
      pullbackSpecIso_inv_fst K (B W) (A W)
    _ = (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := K) (A := B W) (B := A W))) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv) ≫
          (projectivePairChartIsoSpecTensor W (true, true)).hom := by simp

private theorem uIsoSpec_inv_snd (W : WeierstrassCurve K) :
    (uIsoSpec W).inv ≫ uSnd W =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := K) (A := B W) (B := A W)).toRingHom) := by
  rw [uIsoSpec, Iso.trans_inv]
  simp only [Category.assoc]
  rw [uIsoPullback_inv_snd, pullbackSpecIso_inv_snd]
  rfl

private noncomputable instance triple_integral
    (W : WeierstrassCurve K) [W.IsElliptic] : IsIntegral (Triple W) := by
  letI : IsIntegral (scheme W) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (structureMap W)
  letI : Flat (structureMap W) := by infer_instance
  letI : UniversallyOpen (structureMap W) := by infer_instance
  letI : LocallyOfFiniteType (structureMap W) := by infer_instance
  letI : IsLocallyNoetherian (scheme W) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap W)
  letI : IsIntegral (projectivePair W) := by infer_instance
  infer_instance

private noncomputable instance t_domain
    (W : WeierstrassCurve K) [W.IsElliptic] : IsDomain (T W) := by
  apply (affine_isIntegral_iff (.of (T W))).mp
  letI : Nonempty (Spec (.of (T W))) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  letI : Nonempty (U W) :=
    ⟨(uIsoSpec W).inv (Classical.choice
      (inferInstance : Nonempty (Spec (.of (T W)))))⟩
  letI : IsIntegral (U W) := isIntegral_of_isOpenImmersion (uMap W)
  exact IsIntegral.of_isIso (uIsoSpec W).hom

private noncomputable instance u_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] : Nonempty (U W) :=
  ⟨(uIsoSpec W).inv (Classical.choice
    (PrimeSpectrum.nonempty_iff_nontrivial.mpr
      (inferInstance : Nontrivial (T W))))⟩

private abbrev F (W : WeierstrassCurve K) := FractionRing (T W)

private noncomputable def firstToT (W : WeierstrassCurve K) :
    A W →ₐ[K] T W :=
  (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := B W) (B := A W)).comp
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A W) (B := A W))

private noncomputable def secondToT (W : WeierstrassCurve K) :
    A W →ₐ[K] T W :=
  (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := B W) (B := A W)).comp
    (Algebra.TensorProduct.includeRight
      (R := K) (A := A W) (B := A W))

private noncomputable def thirdToT (W : WeierstrassCurve K) :
    A W →ₐ[K] T W :=
  Algebra.TensorProduct.includeRight
    (R := K) (A := B W) (B := A W)

private noncomputable def twelveToT (W : WeierstrassCurve K) :
    B W →ₐ[K] T W :=
  Algebra.TensorProduct.includeLeft
    (R := K) (S := K) (A := B W) (B := A W)

private noncomputable def twentyThreeToT (W : WeierstrassCurve K) :
    B W →ₐ[K] T W :=
  (Algebra.TensorProduct.productMap
    (R := K) (S := T W) (A := A W) (B := A W)
    (secondToT W) (thirdToT W) :
      TensorProduct K (A W) (A W) →ₐ[K] T W)

private noncomputable def toF
    (W : WeierstrassCurve K) [W.IsElliptic] : T W →ₐ[K] F W :=
  IsScalarTower.toAlgHom K (T W) (F W)

private noncomputable def standardChartPointOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : A W →ₐ[K] L) :
    AffineCommGroupScheme.testObject (R := K) L ⟶ toOver W :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      coveringChartMap W true) (by
        change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
            coveringChartMap W true) ≫ structureMap W =
          Spec.map (CommRingCat.ofHom (algebraMap K L))
        rw [Category.assoc, coveringChartMap_comp_structureMap,
          ← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
        ext a
        exact φ.commutes a)

private noncomputable def genericFirst
    (W : WeierstrassCurve K) [W.IsElliptic] :
    AffineCommGroupScheme.testObject (R := K) (F W) ⟶ toOver W :=
  standardChartPointOver W ((toF W).comp (firstToT W))

private noncomputable def genericSecond
    (W : WeierstrassCurve K) [W.IsElliptic] :
    AffineCommGroupScheme.testObject (R := K) (F W) ⟶ toOver W :=
  standardChartPointOver W ((toF W).comp (secondToT W))

private noncomputable def genericThird
    (W : WeierstrassCurve K) [W.IsElliptic] :
    AffineCommGroupScheme.testObject (R := K) (F W) ⟶ toOver W :=
  standardChartPointOver W ((toF W).comp (thirdToT W))

private noncomputable def genericTripleOver
    (W : WeierstrassCurve K) [W.IsElliptic] :
    AffineCommGroupScheme.testObject (R := K) (F W) ⟶
      (toOver W ⊗ toOver W) ⊗ toOver W :=
  lift (lift (genericFirst W) (genericSecond W)) (genericThird W)

private noncomputable def genericToSpecT
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Spec (.of (F W)) ⟶ Spec (.of (T W)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (T W) (F W)))

private noncomputable def genericToU
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Spec (.of (F W)) ⟶ U W :=
  genericToSpecT W ≫ (uIsoSpec W).inv

private noncomputable def genericToTriple
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Spec (.of (F W)) ⟶ Triple W :=
  genericToU W ≫ uMap W

private instance genericToSpecT_dominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant (genericToSpecT W) := by
  constructor
  change DenseRange (PrimeSpectrum.comap
    (algebraMap (T W) (F W)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
    (IsFractionRing.injective (T W) (F W))]
  exact bot_le

private instance genericToU_dominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant (genericToU W) := by
  dsimp only [genericToU]
  infer_instance

private instance uMap_dominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant (uMap W) := by
  constructor
  exact (uMap W).isOpenEmbedding.isOpenMap
    |>.denseRange_of_isPreirreducibleSpace _

private instance genericToTriple_dominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant (genericToTriple W) := by
  dsimp only [genericToTriple]
  infer_instance

private noncomputable def standardPairPointOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    AffineCommGroupScheme.testObject (R := K) L ⟶
      toOver W ⊗ toOver W :=
  lift
    (standardChartPointOver W
      (φ.comp (Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := A W) (B := A W))))
    (standardChartPointOver W
      (φ.comp (Algebra.TensorProduct.includeRight
        (R := K) (A := A W) (B := A W))))

private theorem evaluatedStandardPair_fst
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true)) ≫
        pullback.fst (structureMap W) (structureMap W) =
      Spec.map (CommRingCat.ofHom
        (φ.comp (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A W) (B := A W))).toRingHom) ≫
        coveringChartMap W true := by
  calc
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          (projectivePairChartMap W (true, true) ≫
            pullback.fst (structureMap W) (structureMap W)) := by
              simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartFirstInput W (true, true) := by
            simp only [projectivePairChartMap_comp_fst,
              projectivePairChartFirstInput_eq]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          ((projectivePairChartIsoSpecTensor W (true, true)).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeft
                (R := K) (S := K) (A := A W) (B := A W)).toRingHom) ≫
              coveringChartMap W true) := by rfl
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft
            (R := K) (S := K) (A := A W) (B := A W)).toRingHom) ≫
          coveringChartMap W true := by simp
    _ = _ := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem evaluatedStandardPair_snd
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true)) ≫
        pullback.snd (structureMap W) (structureMap W) =
      Spec.map (CommRingCat.ofHom
        (φ.comp (Algebra.TensorProduct.includeRight
          (R := K) (A := A W) (B := A W))).toRingHom) ≫
        coveringChartMap W true := by
  calc
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          (projectivePairChartMap W (true, true) ≫
            pullback.snd (structureMap W) (structureMap W)) := by
              simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartSecondInput W (true, true) := by
            simp only [projectivePairChartMap_comp_snd,
              projectivePairChartSecondInput_eq]
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          ((projectivePairChartIsoSpecTensor W (true, true)).hom ≫
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight
                (R := K) (A := A W) (B := A W)).toRingHom) ≫
              coveringChartMap W true) := by rfl
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := K) (A := A W) (B := A W)).toRingHom) ≫
          coveringChartMap W true := by simp
    _ = _ := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem standardPairPointOver_left_eq
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    (standardPairPointOver W φ).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true) := by
  apply pullback.hom_ext
  · have h := congrArg (fun q ↦ q.left)
        (lift_fst
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeLeft
              (R := K) (S := K) (A := A W) (B := A W))))
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeRight
              (R := K) (A := A W) (B := A W)))))
    simp only [Over.comp_left, Over.fst_left] at h
    exact h.trans (evaluatedStandardPair_fst W φ).symm
  · have h := congrArg (fun q ↦ q.left)
        (lift_snd
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeLeft
              (R := K) (S := K) (A := A W) (B := A W))))
          (standardChartPointOver W
            (φ.comp (Algebra.TensorProduct.includeRight
              (R := K) (A := A W) (B := A W)))))
    simp only [Over.comp_left, Over.snd_left] at h
    exact h.trans (evaluatedStandardPair_snd W φ).symm

private theorem genericPair_eq_standardPairPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    lift (genericFirst W) (genericSecond W) =
      standardPairPointOver W ((toF W).comp (twelveToT W)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [genericFirst, standardPairPointOver, lift_fst]
    congr 1
  · simp only [genericSecond, standardPairPointOver, lift_snd]
    congr 1

private theorem genericToTriple_fst
    (W : WeierstrassCurve K) [W.IsElliptic] :
    genericToTriple W ≫
        pullback.fst (projectivePairStructureMap W) (structureMap W) =
      Spec.map (CommRingCat.ofHom
          ((toF W).comp (twelveToT W)).toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv ≫
          projectivePairChartMap W (true, true) := by
  calc
    _ = genericToU W ≫
        (uMap W ≫ pullback.fst
          (projectivePairStructureMap W) (structureMap W)) :=
      Category.assoc _ _ _
    _ = genericToU W ≫
        (uFst W ≫ projectivePairChartMap W (true, true)) := by
          rw [uMap_fst]
    _ = (genericToU W ≫ uFst W) ≫
        projectivePairChartMap W (true, true) :=
      (Category.assoc _ _ _).symm
    _ = ((genericToSpecT W ≫ (uIsoSpec W).inv) ≫ uFst W) ≫
        projectivePairChartMap W (true, true) := rfl
    _ = (genericToSpecT W ≫ ((uIsoSpec W).inv ≫ uFst W)) ≫
        projectivePairChartMap W (true, true) := by
          exact congrArg (fun q ↦
            q ≫ projectivePairChartMap W (true, true))
              (Category.assoc _ _ _)
    _ = (genericToSpecT W ≫
          (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom
                (R := K) (A := B W) (B := A W))) ≫
            (projectivePairChartIsoSpecTensor W (true, true)).inv)) ≫
        projectivePairChartMap W (true, true) := by
          rw [uIsoSpec_inv_fst]
    _ = _ := by
      simp only [genericToSpecT, Category.assoc]
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem genericToTriple_snd
    (W : WeierstrassCurve K) [W.IsElliptic] :
    genericToTriple W ≫
        pullback.snd (projectivePairStructureMap W) (structureMap W) =
      Spec.map (CommRingCat.ofHom
          ((toF W).comp (thirdToT W)).toRingHom) ≫
        coveringChartMap W true := by
  calc
    _ = genericToU W ≫
        (uMap W ≫ pullback.snd
          (projectivePairStructureMap W) (structureMap W)) :=
      Category.assoc _ _ _
    _ = genericToU W ≫
        (uSnd W ≫ coveringChartMap W true) := by rw [uMap_snd]
    _ = (genericToU W ≫ uSnd W) ≫ coveringChartMap W true :=
      (Category.assoc _ _ _).symm
    _ = ((genericToSpecT W ≫ (uIsoSpec W).inv) ≫ uSnd W) ≫
        coveringChartMap W true := rfl
    _ = (genericToSpecT W ≫ ((uIsoSpec W).inv ≫ uSnd W)) ≫
        coveringChartMap W true := by
          exact congrArg (fun q ↦ q ≫ coveringChartMap W true)
            (Category.assoc _ _ _)
    _ = (genericToSpecT W ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight
              (R := K) (A := B W) (B := A W)).toRingHom)) ≫
        coveringChartMap W true := by rw [uIsoSpec_inv_snd]
    _ = _ := by
      simp only [genericToSpecT, Category.assoc]
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem genericTripleOver_left_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (genericTripleOver W).left = genericToTriple W := by
  apply pullback.hom_ext
  · have h := congrArg (fun q ↦ q.left)
        (lift_fst
          (lift (genericFirst W) (genericSecond W)) (genericThird W))
    simp only [Over.comp_left, Over.fst_left] at h
    exact h.trans ((congrArg (fun q ↦ q.left)
      (genericPair_eq_standardPairPoint W)).trans
        ((standardPairPointOver_left_eq W
          ((toF W).comp (twelveToT W))).trans
            (genericToTriple_fst W).symm))
  · have h := congrArg (fun q ↦ q.left)
        (lift_snd
          (lift (genericFirst W) (genericSecond W)) (genericThird W))
    simp only [Over.comp_left, Over.snd_left] at h
    exact h.trans (genericToTriple_snd W).symm

private instance genericTripleOver_dominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant (genericTripleOver W).left := by
  rw [genericTripleOver_left_eq]
  exact genericToTriple_dominant W

private noncomputable def standardPairOutputToField
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    projectivePairChartAdditionOutputRing W (true, true) true →ₐ[K] L := by
  change Localization.Away
      (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) →ₐ[K] L
  exact IsLocalization.Away.liftAlgHom
    (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) (f := φ) hZ.isUnit

private theorem standardPairOutputToField_algebraMap
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) (a : B W) :
    standardPairOutputToField W φ hZ
        (algebraMap (B W)
          (projectivePairChartAdditionOutputRing W
            (true, true) true) a) = φ a := by
  change IsLocalization.Away.liftAlgHom
      (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) hZ.isUnit
        (algebraMap (B W)
          (Localization.Away
            (projectivePairChartAdditionCoordinates W
              (true, true) (2 : Fin 3))) a) = φ a
  exact IsLocalization.Away.lift_eq
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)))
    (x := projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3))
    (g := φ.toRingHom) hZ.isUnit a

private theorem standardPairOutputToField_comp_algebraMap
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    (standardPairOutputToField W φ hZ).comp
        (IsScalarTower.toAlgHom K (B W)
          (projectivePairChartAdditionOutputRing W
            (true, true) true)) = φ := by
  apply DFunLike.ext _ _
  intro a
  exact standardPairOutputToField_algebraMap W φ hZ a

private theorem standardPairPoint_factor_output
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    Spec.map (CommRingCat.ofHom
        (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputOpen W
          (true, true) true =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectivePairChartIsoSpecTensor W (true, true)).inv := by
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, true)).hom).1
  rw [Category.assoc,
    projectivePairChartAdditionOutputOpen_comp_iso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((standardPairOutputToField W φ hZ).comp
        (IsScalarTower.toAlgHom K (B W)
          (projectivePairChartAdditionOutputRing W
            (true, true) true))).toRingHom) =
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  rw [standardPairOutputToField_comp_algebraMap]

private noncomputable def standardPairSumAlgHom
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) : A W →ₐ[K] L :=
  (standardPairOutputToField W φ hZ).comp
    (projectivePairChartAdditionOutputAlgHom W
      (true, true) true)

private theorem standardPairPoint_addition
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    standardPairPointOver W φ ≫ projectiveAdditionOver W =
      standardChartPointOver W (standardPairSumAlgHom W φ hZ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, projectiveAdditionOver_left]
  rw [standardPairPointOver_left_eq]
  change _ = Spec.map (CommRingCat.ofHom
      (standardPairSumAlgHom W φ hZ).toRingHom) ≫
    coveringChartMap W true
  calc
    _ = (Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
          projectivePairChartAdditionOutputOpen W
            (true, true) true) ≫
        projectivePairChartMap W (true, true) ≫
          projectiveAdditionMorphism W := by
            exact (Category.assoc _ _ _).trans (congrArg
              (fun q ↦ q ≫ (projectivePairChartMap W (true, true) ≫
                projectiveAdditionMorphism W))
              (standardPairPoint_factor_output W φ hZ).symm)
    _ = Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputOpen W
          (true, true) true ≫
          (projectivePairChartMap W (true, true) ≫
            projectiveAdditionMorphism W) := by simp only [Category.assoc]
    _ = Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputOpen W
          (true, true) true ≫ standardPairAdditionMorphism W := by
            rw [projectivePairStandardChart_comp_projectiveAdditionMorphism]
    _ = Spec.map (CommRingCat.ofHom
            (standardPairOutputToField W φ hZ).toRingHom) ≫
        projectivePairChartAdditionOutputMorphism W
          (true, true) true := by
            simpa only [Category.assoc] using congrArg
              (fun q ↦ Spec.map (CommRingCat.ofHom
                (standardPairOutputToField W φ hZ).toRingHom) ≫ q)
              (projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism W)
    _ = Spec.map (CommRingCat.ofHom
          (standardPairSumAlgHom W φ hZ).toRingHom) ≫
        coveringChartMap W true := by
      rw [projectivePairChartAdditionOutputMorphism]
      simp only [standardPairSumAlgHom]
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

private theorem standardPairOutputToField_unit
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    standardPairOutputToField W φ hZ
        (projectivePairChartAdditionOutputUnit W
          (true, true) true) =
      φ (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) := by
  rw [projectivePairChartAdditionOutputUnit]
  rw [(IsLocalization.Away.algebraMap_isUnit
    (projectivePairChartAdditionCoordinates W
      (true, true) (coveringCoordinate true))).unit_spec]
  exact standardPairOutputToField_algebraMap W φ hZ _

private theorem standardPairSumAlgHom_universalPoint
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) (j : Fin 3) :
    standardPairSumAlgHom W φ hZ
        (coveringChartUniversalPoint W true j) =
      (φ (projectivePairChartAdditionCoordinates W
          (true, true) (2 : Fin 3)))⁻¹ *
        φ (projectivePairChartAdditionCoordinates W
          (true, true) j) := by
  rw [standardPairSumAlgHom, AlgHom.comp_apply]
  rw [show coveringChartUniversalPoint W true j =
      Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (coveringCoordinate true) j) by rfl]
  rw [projectivePairChartAdditionOutputAlgHom_ratio]
  rw [projectivePairChartAdditionOutputPoint, map_mul,
    map_units_inv, standardPairOutputToField_unit,
    standardPairOutputToField_algebraMap]

private theorem chartOneX_linearIndependent
    (W : WeierstrassCurve K) :
    LinearIndependent K
      (![1, coveringChartUniversalPoint W true 0] : Fin 2 → A W) := by
  rw [LinearIndependent.pair_iff' (one_ne_zero : (1 : A W) ≠ 0)]
  intro a ha
  have hdenom := (standardPairCoordinateRingAlgEquiv W).injective.ne
    (secantDenominator_ne_zero W)
  rw [map_zero, standardPairCoordinateRingAlgEquiv_denominator] at hdenom
  apply hdenom
  simp only [projectivePairChartFirstUniversalPoint,
    projectivePairChartSecondUniversalPoint]
  rw [← ha]
  simp [Algebra.smul_def]

private theorem chartOneX_linearIndepOn
    (W : WeierstrassCurve K) :
    LinearIndepOn K id
      ({1, coveringChartUniversalPoint W true 0} : Set (A W)) := by
  have h := (chartOneX_linearIndependent W).linearIndepOn_id
  rw [show Set.range
      (![1, coveringChartUniversalPoint W true 0] : Fin 2 → A W) =
        {1, coveringChartUniversalPoint W true 0} by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · intro hz
        rcases hz with rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩] at h
  exact h

private noncomputable def chartOneXBasis
    (W : WeierstrassCurve K) :=
  Module.Basis.extend (chartOneX_linearIndepOn W)

private noncomputable def chartOneIndex
    (W : WeierstrassCurve K) :
    (chartOneX_linearIndepOn W).extend (Set.subset_univ _) :=
  ⟨1, Module.Basis.subset_extend (chartOneX_linearIndepOn W) (by simp)⟩

private noncomputable def chartXIndex
    (W : WeierstrassCurve K) :
    (chartOneX_linearIndepOn W).extend (Set.subset_univ _) :=
  ⟨coveringChartUniversalPoint W true 0,
    Module.Basis.subset_extend (chartOneX_linearIndepOn W) (by simp)⟩

private theorem chartOneIndex_ne_chartXIndex
    (W : WeierstrassCurve K) :
    chartOneIndex W ≠ chartXIndex W := by
  intro h
  have hv := congrArg Subtype.val h
  have hinj := (chartOneX_linearIndependent W).injective
  apply (show (0 : Fin 2) ≠ 1 by decide)
  apply hinj
  simpa [chartOneIndex, chartXIndex] using hv

private noncomputable def chartXCoefficient
    (W : WeierstrassCurve K) : A W →ₗ[K] K :=
  (chartOneXBasis W).coord (chartXIndex W)

private theorem chartXCoefficient_one
    (W : WeierstrassCurve K) :
    chartXCoefficient W 1 = 0 := by
  classical
  change ((chartOneXBasis W).repr 1) (chartXIndex W) = 0
  have hb : chartOneXBasis W (chartOneIndex W) = (1 : A W) :=
    Module.Basis.extend_apply_self
      (chartOneX_linearIndepOn W) (chartOneIndex W)
  calc
    _ = ((chartOneXBasis W).repr
        (chartOneXBasis W (chartOneIndex W))) (chartXIndex W) := by
          exact congrArg
            (fun z : A W ↦ ((chartOneXBasis W).repr z) (chartXIndex W)) hb.symm
    _ = 0 := by
      rw [Module.Basis.repr_self_apply]
      simp [chartOneIndex_ne_chartXIndex W]

private theorem chartXCoefficient_X
    (W : WeierstrassCurve K) :
    chartXCoefficient W (coveringChartUniversalPoint W true 0) = 1 := by
  classical
  change ((chartOneXBasis W).repr
    (coveringChartUniversalPoint W true 0)) (chartXIndex W) = 1
  have hb : chartOneXBasis W (chartXIndex W) =
      coveringChartUniversalPoint W true 0 :=
    Module.Basis.extend_apply_self
      (chartOneX_linearIndepOn W) (chartXIndex W)
  calc
    _ = ((chartOneXBasis W).repr
        (chartOneXBasis W (chartXIndex W))) (chartXIndex W) := by
          exact congrArg
            (fun z : A W ↦ ((chartOneXBasis W).repr z) (chartXIndex W)) hb.symm
    _ = 1 := by rw [Module.Basis.repr_self_apply]; simp

private noncomputable def tripleTensorAssoc
    (W : WeierstrassCurve K) :
    T W ≃ₐ[K] TensorProduct K (A W) (B W) :=
  Algebra.TensorProduct.assoc K K K (A W) (A W) (A W)

private theorem tripleTensorAssoc_comp_twentyThreeToT
    (W : WeierstrassCurve K) :
    (tripleTensorAssoc W).toAlgHom.comp (twentyThreeToT W) =
      Algebra.TensorProduct.includeRight
        (R := K) (A := A W) (B := B W) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [tripleTensorAssoc, twentyThreeToT, secondToT, thirdToT,
    Algebra.TensorProduct.includeLeft_apply]

private theorem twelveToT_injective
    (W : WeierstrassCurve K) : Function.Injective (twelveToT W) := by
  letI : Module.Free K (B W) := Module.Free.of_divisionRing K (B W)
  letI : Module.Flat K (B W) := Module.Flat.of_free
  have hA : Function.Injective (algebraMap K (A W)) :=
    RingHom.injective (algebraMap K (A W))
  exact Algebra.TensorProduct.includeLeft_injective
    (R := K) (S := K) (A := B W) (B := A W) hA

private theorem twentyThreeToT_injective
    (W : WeierstrassCurve K) : Function.Injective (twentyThreeToT W) := by
  letI : Module.Free K (B W) := Module.Free.of_divisionRing K (B W)
  letI : Module.Flat K (B W) := Module.Flat.of_free
  have hA : Function.Injective (algebraMap K (A W)) :=
    RingHom.injective (algebraMap K (A W))
  have hright : Function.Injective
      (Algebra.TensorProduct.includeRight
        (R := K) (A := A W) (B := B W)) :=
    Algebra.TensorProduct.includeRight_injective hA
  intro x y hxy
  apply hright
  rw [← tripleTensorAssoc_comp_twentyThreeToT W]
  exact congrArg (tripleTensorAssoc W) hxy

private theorem toF_injective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective (toF W) :=
  IsFractionRing.injective (T W) (F W)

private theorem twelveToF_injective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective ((toF W).comp (twelveToT W)) :=
  (toF_injective W).comp (twelveToT_injective W)

private theorem twentyThreeToF_injective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective ((toF W).comp (twentyThreeToT W)) :=
  (toF_injective W).comp (twentyThreeToT_injective W)

private noncomputable def contractThird
    (W : WeierstrassCurve K) : T W →ₗ[K] B W :=
  (TensorProduct.rid K (B W)).toLinearMap.comp
    (LinearMap.lTensor (B W) (chartXCoefficient W))

@[simp]
private theorem contractThird_tmul
    (W : WeierstrassCurve K) (b : B W) (a : A W) :
    contractThird W (b ⊗ₜ[K] a) = chartXCoefficient W a • b := by
  simp [contractThird]

private theorem leftOuterCrossDifference_ne_zero
    (W : WeierstrassCurve K) (X Z : B W) (hZ : Z ≠ 0) :
    twelveToT W X -
        thirdToT W (coveringChartUniversalPoint W true 0) * twelveToT W Z ≠ 0 := by
  intro h
  simp only [twelveToT, thirdToT,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h
  have hc :
      contractThird W (X ⊗ₜ[K] (1 : A W)) -
          contractThird W
            (Z ⊗ₜ[K] coveringChartUniversalPoint W true 0) = 0 := by
    calc
      _ = contractThird W
          (X ⊗ₜ[K] (1 : A W) -
            Z ⊗ₜ[K] coveringChartUniversalPoint W true 0) :=
        ((contractThird W).map_sub
          (X ⊗ₜ[K] (1 : A W))
          (Z ⊗ₜ[K] coveringChartUniversalPoint W true 0)).symm
      _ = contractThird W 0 := congrArg (contractThird W) h
      _ = 0 := (contractThird W).map_zero
  rw [contractThird_tmul, contractThird_tmul,
    chartXCoefficient_one, chartXCoefficient_X,
    zero_smul, one_smul] at hc
  apply hZ
  exact neg_eq_zero.mp (by simpa only [zero_sub] using hc)

private noncomputable def contractFirstAssociated
    (W : WeierstrassCurve K) :
    TensorProduct K (A W) (B W) →ₗ[K] B W :=
  (TensorProduct.lid K (B W)).toLinearMap.comp
    (LinearMap.rTensor (B W) (chartXCoefficient W))

@[simp]
private theorem contractFirstAssociated_tmul
    (W : WeierstrassCurve K) (a : A W) (b : B W) :
    contractFirstAssociated W (a ⊗ₜ[K] b) =
      chartXCoefficient W a • b := by
  simp [contractFirstAssociated]

private theorem tripleTensorAssoc_twentyThreeToT
    (W : WeierstrassCurve K) (z : B W) :
    tripleTensorAssoc W (twentyThreeToT W z) =
      Algebra.TensorProduct.includeRight
        (R := K) (A := A W) (B := B W) z := by
  exact DFunLike.congr_fun (tripleTensorAssoc_comp_twentyThreeToT W) z

private theorem tripleTensorAssoc_firstToT
    (W : WeierstrassCurve K) (a : A W) :
    tripleTensorAssoc W (firstToT W a) =
      Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := A W) (B := B W) a := by
  simp [tripleTensorAssoc, firstToT,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.one_def]

private theorem rightOuterCrossDifference_ne_zero
    (W : WeierstrassCurve K) (X Z : B W) (hZ : Z ≠ 0) :
    firstToT W (coveringChartUniversalPoint W true 0) *
        twentyThreeToT W Z - twentyThreeToT W X ≠ 0 := by
  intro h
  have ha :
      tripleTensorAssoc W
          (firstToT W (coveringChartUniversalPoint W true 0)) *
          tripleTensorAssoc W (twentyThreeToT W Z) -
        tripleTensorAssoc W (twentyThreeToT W X) = 0 := by
    calc
      _ = tripleTensorAssoc W
          (firstToT W (coveringChartUniversalPoint W true 0) *
            twentyThreeToT W Z) -
          tripleTensorAssoc W (twentyThreeToT W X) := by
            exact congrArg
              (fun q : TensorProduct K (A W) (B W) ↦
                q - tripleTensorAssoc W (twentyThreeToT W X))
              ((tripleTensorAssoc W).map_mul
                (firstToT W (coveringChartUniversalPoint W true 0))
                (twentyThreeToT W Z)).symm
      _ = tripleTensorAssoc W
          (firstToT W (coveringChartUniversalPoint W true 0) *
            twentyThreeToT W Z - twentyThreeToT W X) :=
        ((tripleTensorAssoc W).map_sub
          (firstToT W (coveringChartUniversalPoint W true 0) *
            twentyThreeToT W Z) (twentyThreeToT W X)).symm
      _ = tripleTensorAssoc W 0 := congrArg (tripleTensorAssoc W) h
      _ = 0 := (tripleTensorAssoc W).map_zero
  rw [
    tripleTensorAssoc_firstToT,
    tripleTensorAssoc_twentyThreeToT W Z,
    tripleTensorAssoc_twentyThreeToT W X] at ha
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at ha
  have hc : contractFirstAssociated W
        (coveringChartUniversalPoint W true 0 ⊗ₜ[K] Z) -
      contractFirstAssociated W ((1 : A W) ⊗ₜ[K] X) = 0 := by
    calc
      _ = contractFirstAssociated W
          (coveringChartUniversalPoint W true 0 ⊗ₜ[K] Z -
            (1 : A W) ⊗ₜ[K] X) :=
        ((contractFirstAssociated W).map_sub
          (coveringChartUniversalPoint W true 0 ⊗ₜ[K] Z)
          ((1 : A W) ⊗ₜ[K] X)).symm
      _ = contractFirstAssociated W 0 := congrArg (contractFirstAssociated W) ha
      _ = 0 := (contractFirstAssociated W).map_zero
  rw [contractFirstAssociated_tmul,
    contractFirstAssociated_tmul, chartXCoefficient_X,
    chartXCoefficient_one, one_smul, zero_smul, sub_zero] at hc
  exact hZ hc

private theorem standardPairRawZ_eval
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    φ (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) =
      (φ (projectivePairChartFirstUniversalPoint W (true, true) 0) -
        φ (projectivePairChartSecondUniversalPoint W (true, true) 0)) ^ 3 := by
  rw [projectivePairChartAdditionCoordinates_standard_Z, map_pow,
    standardPairCoordinateRingAlgEquiv_denominator, map_sub]

private noncomputable def pairTwelveToF
    (W : WeierstrassCurve K) [W.IsElliptic] : B W →ₐ[K] F W :=
  (toF W).comp (twelveToT W)

private theorem pairTwelveRawZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairTwelveToF W (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0 := by
  have h := (twelveToF_injective W).ne
    (standardPairRawOutputZ_ne_zero W)
  simpa only [pairTwelveToF, map_zero] using h

private noncomputable def pairTwentyThreeToF
    (W : WeierstrassCurve K) [W.IsElliptic] : B W →ₐ[K] F W :=
  (toF W).comp (twentyThreeToT W)

private theorem pairTwentyThreeRawZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairTwentyThreeToF W (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0 := by
  have h := (twentyThreeToF_injective W).ne
    (standardPairRawOutputZ_ne_zero W)
  simpa only [pairTwentyThreeToF, map_zero] using h

private noncomputable def sumTwelveToF
    (W : WeierstrassCurve K) [W.IsElliptic] : A W →ₐ[K] F W :=
  standardPairSumAlgHom W (pairTwelveToF W)
    (pairTwelveRawZ_ne_zero W)

private noncomputable def sumTwentyThreeToF
    (W : WeierstrassCurve K) [W.IsElliptic] : A W →ₐ[K] F W :=
  standardPairSumAlgHom W (pairTwentyThreeToF W)
    (pairTwentyThreeRawZ_ne_zero W)

private noncomputable def leftOuterPairToF
    (W : WeierstrassCurve K) [W.IsElliptic] : B W →ₐ[K] F W :=
  Algebra.TensorProduct.productMap (sumTwelveToF W)
    ((toF W).comp (thirdToT W))

private noncomputable def rightOuterPairToF
    (W : WeierstrassCurve K) [W.IsElliptic] : B W →ₐ[K] F W :=
  Algebra.TensorProduct.productMap ((toF W).comp (firstToT W))
    (sumTwentyThreeToF W)

private theorem inv_mul_sub_ne_zero_of_cross
    {L : Type u} [Field L] {z x t : L}
    (hz : z ≠ 0) (hcross : x - t * z ≠ 0) :
    z⁻¹ * x - t ≠ 0 := by
  intro h
  apply hcross
  rw [sub_eq_zero]
  have heq : z⁻¹ * x = t := sub_eq_zero.mp h
  calc
    x = z * (z⁻¹ * x) := by field_simp
    _ = z * t := congrArg (fun q ↦ z * q) heq
    _ = t * z := mul_comm _ _

private theorem sub_inv_mul_ne_zero_of_cross
    {L : Type u} [Field L] {z x t : L}
    (hz : z ≠ 0) (hcross : t * z - x ≠ 0) :
    t - z⁻¹ * x ≠ 0 := by
  intro h
  apply hcross
  rw [sub_eq_zero]
  have heq : t = z⁻¹ * x := sub_eq_zero.mp h
  calc
    t * z = (z⁻¹ * x) * z := congrArg (fun q ↦ q * z) heq
    _ = x := by field_simp

private theorem leftOuterRawZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    leftOuterPairToF W (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0 := by
  rw [standardPairRawZ_eval]
  apply pow_ne_zero
  simp only [leftOuterPairToF,
    projectivePairChartFirstUniversalPoint,
    projectivePairChartSecondUniversalPoint,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_apply_tmul,
    map_one, mul_one, one_mul]
  rw [sumTwelveToF, standardPairSumAlgHom_universalPoint]
  let rawX := projectivePairChartAdditionCoordinates W
    (true, true) (0 : Fin 3)
  let rawZ := projectivePairChartAdditionCoordinates W
    (true, true) (2 : Fin 3)
  have hcrossT := leftOuterCrossDifference_ne_zero W rawX rawZ
    (standardPairRawOutputZ_ne_zero W)
  have hcrossF :
      toF W (twelveToT W rawX) -
          toF W (thirdToT W
            (coveringChartUniversalPoint W true 0)) *
            toF W (twelveToT W rawZ) ≠ 0 := by
    have h := (toF_injective W).ne hcrossT
    simpa only [map_sub, map_mul, map_zero] using h
  exact inv_mul_sub_ne_zero_of_cross
    (pairTwelveRawZ_ne_zero W) hcrossF

private theorem rightOuterRawZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    rightOuterPairToF W (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0 := by
  rw [standardPairRawZ_eval]
  apply pow_ne_zero
  simp only [rightOuterPairToF,
    projectivePairChartFirstUniversalPoint,
    projectivePairChartSecondUniversalPoint,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_apply_tmul,
    map_one, mul_one, one_mul]
  rw [sumTwentyThreeToF, standardPairSumAlgHom_universalPoint]
  let rawX := projectivePairChartAdditionCoordinates W
    (true, true) (0 : Fin 3)
  let rawZ := projectivePairChartAdditionCoordinates W
    (true, true) (2 : Fin 3)
  have hcrossT := rightOuterCrossDifference_ne_zero W rawX rawZ
    (standardPairRawOutputZ_ne_zero W)
  have hcrossF :
      toF W (firstToT W
          (coveringChartUniversalPoint W true 0)) *
          toF W (twentyThreeToT W rawZ) -
        toF W (twentyThreeToT W rawX) ≠ 0 := by
    have h := (toF_injective W).ne hcrossT
    simpa only [map_sub, map_mul, map_zero] using h
  exact sub_inv_mul_ne_zero_of_cross
    (pairTwentyThreeRawZ_ne_zero W) hcrossF

private noncomputable def chartCoordinatesOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : A W →ₐ[K] L) : Fin 3 → L :=
  φ ∘ coveringChartUniversalPoint W true

@[simp]
private theorem chartCoordinatesOver_Z
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : A W →ₐ[K] L) :
    chartCoordinatesOver W φ (2 : Fin 3) = 1 := by
  change φ (coveringChartUniversalPoint W true
    (coveringCoordinate true)) = 1
  rw [
    coveringChartUniversalPoint_normalized, map_one]

private theorem chartCoordinatesOver_equation
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : A W →ₐ[K] L) :
    (W.map (algebraMap K L)).toProjective.Equation
      (chartCoordinatesOver W φ) := by
  let f := φ.toRingHom
  have h := (coveringChartUniversalPoint_equation W true).map f
  have hf : f.comp (coveringChartStructureRingHom W true) =
      algebraMap K L := by
    ext a
    rw [← coveringChartCoordinateRing_algebraMap]
    exact φ.commutes a
  change ((W.map (coveringChartStructureRingHom W true)).map f).toProjective.Equation
    (f ∘ coveringChartUniversalPoint W true) at h
  rw [WeierstrassCurve.map_map, hf] at h
  exact h

private theorem chartCoordinatesOver_nonsingular
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : A W →ₐ[K] L) :
    (W.map (algebraMap K L)).toProjective.Nonsingular
      (chartCoordinatesOver W φ) := by
  apply projective_nonsingular_of_equation_of_ne_zero
  · intro h
    have hz := congrFun h (2 : Fin 3)
    simp at hz
  · exact chartCoordinatesOver_equation W φ

private noncomputable def pairFirstCoordinatesOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) : Fin 3 → L :=
  chartCoordinatesOver W
    (φ.comp (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A W) (B := A W)))

private noncomputable def pairSecondCoordinatesOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) : Fin 3 → L :=
  chartCoordinatesOver W
    (φ.comp (Algebra.TensorProduct.includeRight
      (R := K) (A := A W) (B := A W)))

private noncomputable def pairSumCoordinatesOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) : Fin 3 → L :=
  chartCoordinatesOver W (standardPairSumAlgHom W φ hZ)

private theorem standardPairRawCoordinate_eval
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) (j : Fin 3) :
    φ (projectivePairChartAdditionCoordinates W (true, true) j) =
      (W.map (algebraMap K L)).toProjective.addXYZ
        (pairFirstCoordinatesOver W φ)
        (pairSecondCoordinatesOver W φ) j := by
  let f := φ.toRingHom
  let P := projectivePairChartFirstUniversalPoint W (true, true)
  let Q := projectivePairChartSecondUniversalPoint W (true, true)
  have hmap := congrFun
    (WeierstrassCurve.Projective.map_addXYZ
      (W' := projectivePairChartMappedCurve W (true, true))
      (P := P) (Q := Q) f) j
  have hcurve :
      (projectivePairChartMappedCurve W (true, true)).map f =
        W.map (algebraMap K L) := by
    rw [projectivePairChartMappedCurve, WeierstrassCurve.map_map]
    congr 1
    ext a
    exact φ.commutes a
  have hP : f ∘ P = pairFirstCoordinatesOver W φ := by
    funext k
    rfl
  have hQ : f ∘ Q = pairSecondCoordinatesOver W φ := by
    funext k
    rfl
  change
    ((projectivePairChartMappedCurve W (true, true)).map f).toProjective.addXYZ
        (f ∘ P) (f ∘ Q) j =
      (f ∘ (projectivePairChartMappedCurve W
        (true, true)).toProjective.addXYZ P Q) j at hmap
  rw [hcurve, hP, hQ] at hmap
  simpa [P, Q, f, projectivePairChartAdditionCoordinates] using hmap.symm

private noncomputable def chartProjectivePointOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : A W →ₐ[K] L) :
    (W.map (algebraMap K L)).toProjective.Point :=
  ⟨((W.map (algebraMap K L)).toProjective.nonsingularLift_iff
    (chartCoordinatesOver W φ)).mpr
      (chartCoordinatesOver_nonsingular W φ)⟩

private noncomputable def pairFirstProjectivePointOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L) :
    (W.map (algebraMap K L)).toProjective.Point :=
  chartProjectivePointOver W
    (φ.comp (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A W) (B := A W)))

private noncomputable def pairSecondProjectivePointOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L) :
    (W.map (algebraMap K L)).toProjective.Point :=
  chartProjectivePointOver W
    (φ.comp (Algebra.TensorProduct.includeRight
      (R := K) (A := A W) (B := A W)))

private noncomputable def pairSumProjectivePointOver
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    (W.map (algebraMap K L)).toProjective.Point :=
  chartProjectivePointOver W (standardPairSumAlgHom W φ hZ)

@[simp]
private theorem pairFirstCoordinatesOver_Z
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    pairFirstCoordinatesOver W φ (2 : Fin 3) = 1 :=
  chartCoordinatesOver_Z W _

@[simp]
private theorem pairSecondCoordinatesOver_Z
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    pairSecondCoordinatesOver W φ (2 : Fin 3) = 1 :=
  chartCoordinatesOver_Z W _

private theorem pairRawZ_eval
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L) :
    φ (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)) =
      (pairFirstCoordinatesOver W φ 0 -
        pairSecondCoordinatesOver W φ 0) ^ 3 := by
  simpa [pairFirstCoordinatesOver, pairSecondCoordinatesOver,
    chartCoordinatesOver,
    projectivePairChartFirstUniversalPoint,
    projectivePairChartSecondUniversalPoint] using
      standardPairRawZ_eval W φ

private theorem pairCoordinates_not_equiv
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    ¬ pairFirstCoordinatesOver W φ ≈ pairSecondCoordinatesOver W φ := by
  apply WeierstrassCurve.Projective.not_equiv_of_X_ne
  have hx : pairFirstCoordinatesOver W φ 0 ≠
      pairSecondCoordinatesOver W φ 0 := by
    intro h
    apply hZ
    rw [pairRawZ_eval, h, sub_self]
    norm_num
  simpa only [pairFirstCoordinatesOver_Z,
    pairSecondCoordinatesOver_Z, mul_one] using hx

private theorem pairSumCoordinatesOver_eq_smul_addXYZ
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    pairSumCoordinatesOver W φ hZ =
      (φ (projectivePairChartAdditionCoordinates W
        (true, true) (2 : Fin 3)))⁻¹ •
        (W.map (algebraMap K L)).toProjective.addXYZ
          (pairFirstCoordinatesOver W φ)
          (pairSecondCoordinatesOver W φ) := by
  funext j
  rw [pairSumCoordinatesOver, chartCoordinatesOver, Function.comp_apply,
    standardPairSumAlgHom_universalPoint]
  rw [standardPairRawCoordinate_eval W φ (2 : Fin 3),
    standardPairRawCoordinate_eval W φ j]
  rfl

private theorem pairSumProjectivePointOver_eq_add
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    pairSumProjectivePointOver W φ hZ =
      pairFirstProjectivePointOver W φ +
        pairSecondProjectivePointOver W φ := by
  apply WeierstrassCurve.Projective.Point.ext
  change (⟦pairSumCoordinatesOver W φ hZ⟧ :
      WeierstrassCurve.Projective.PointClass L) = _
  rw [WeierstrassCurve.Projective.Point.add_point]
  change (⟦pairSumCoordinatesOver W φ hZ⟧ :
      WeierstrassCurve.Projective.PointClass L) =
    (W.map (algebraMap K L)).toProjective.addMap
      ⟦pairFirstCoordinatesOver W φ⟧ ⟦pairSecondCoordinatesOver W φ⟧
  rw [WeierstrassCurve.Projective.addMap_eq]
  apply Quotient.eq.mpr
  rw [pairSumCoordinatesOver_eq_smul_addXYZ,
    WeierstrassCurve.Projective.add_of_not_equiv
      (pairCoordinates_not_equiv W φ hZ)]
  exact WeierstrassCurve.Projective.smul_equiv _
    (Ne.isUnit (inv_ne_zero hZ))

private theorem chartProjectivePointOver_congr
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {φ ψ : A W →ₐ[K] L} (h : φ = ψ) :
    chartProjectivePointOver W φ = chartProjectivePointOver W ψ := by
  subst h
  rfl

private theorem pairTwelveToF_left
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (pairTwelveToF W).comp (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A W) (B := A W)) =
      (toF W).comp (firstToT W) := by
  apply DFunLike.ext _ _
  intro a
  rfl

private theorem pairTwelveToF_right
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (pairTwelveToF W).comp (Algebra.TensorProduct.includeRight
      (R := K) (A := A W) (B := A W)) =
      (toF W).comp (secondToT W) := by
  apply DFunLike.ext _ _
  intro a
  rfl

private theorem pairTwentyThreeToF_left
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (pairTwentyThreeToF W).comp (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A W) (B := A W)) =
      (toF W).comp (secondToT W) := by
  apply DFunLike.ext _ _
  intro a
  simp [pairTwentyThreeToF, twentyThreeToT, AlgHom.comp_apply]

private theorem pairTwentyThreeToF_right
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (pairTwentyThreeToF W).comp (Algebra.TensorProduct.includeRight
      (R := K) (A := A W) (B := A W)) =
      (toF W).comp (thirdToT W) := by
  apply DFunLike.ext _ _
  intro a
  simp [pairTwentyThreeToF, twentyThreeToT, AlgHom.comp_apply]

private theorem leftOuterPairToF_left
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (leftOuterPairToF W).comp (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A W) (B := A W)) =
      sumTwelveToF W := by
  apply DFunLike.ext _ _
  intro a
  simp [leftOuterPairToF]

private theorem leftOuterPairToF_right
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (leftOuterPairToF W).comp (Algebra.TensorProduct.includeRight
      (R := K) (A := A W) (B := A W)) =
      (toF W).comp (thirdToT W) := by
  apply DFunLike.ext _ _
  intro a
  simp [leftOuterPairToF]

private theorem rightOuterPairToF_left
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (rightOuterPairToF W).comp (Algebra.TensorProduct.includeLeft
      (R := K) (S := K) (A := A W) (B := A W)) =
      (toF W).comp (firstToT W) := by
  apply DFunLike.ext _ _
  intro a
  simp [rightOuterPairToF]

private theorem rightOuterPairToF_right
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (rightOuterPairToF W).comp (Algebra.TensorProduct.includeRight
      (R := K) (A := A W) (B := A W)) =
      sumTwentyThreeToF W := by
  apply DFunLike.ext _ _
  intro a
  simp [rightOuterPairToF]

private theorem leftOuter_firstPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairFirstProjectivePointOver W (leftOuterPairToF W) =
      pairSumProjectivePointOver W (pairTwelveToF W)
        (pairTwelveRawZ_ne_zero W) := by
  apply chartProjectivePointOver_congr
  exact leftOuterPairToF_left W

private theorem leftOuter_secondPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairSecondProjectivePointOver W (leftOuterPairToF W) =
      pairSecondProjectivePointOver W (pairTwentyThreeToF W) := by
  apply chartProjectivePointOver_congr
  exact (leftOuterPairToF_right W).trans
    (pairTwentyThreeToF_right W).symm

private theorem rightOuter_firstPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairFirstProjectivePointOver W (rightOuterPairToF W) =
      pairFirstProjectivePointOver W (pairTwelveToF W) := by
  apply chartProjectivePointOver_congr
  exact (rightOuterPairToF_left W).trans (pairTwelveToF_left W).symm

private theorem rightOuter_secondPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairSecondProjectivePointOver W (rightOuterPairToF W) =
      pairSumProjectivePointOver W (pairTwentyThreeToF W)
        (pairTwentyThreeRawZ_ne_zero W) := by
  apply chartProjectivePointOver_congr
  exact rightOuterPairToF_right W

private theorem middlePoints_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairSecondProjectivePointOver W (pairTwelveToF W) =
      pairFirstProjectivePointOver W (pairTwentyThreeToF W) := by
  apply chartProjectivePointOver_congr
  exact (pairTwelveToF_right W).trans (pairTwentyThreeToF_left W).symm

@[simp]
private theorem pairSumCoordinatesOver_Z
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (φ : B W →ₐ[K] L)
    (hZ : φ (projectivePairChartAdditionCoordinates W
      (true, true) (2 : Fin 3)) ≠ 0) :
    pairSumCoordinatesOver W φ hZ (2 : Fin 3) = 1 :=
  chartCoordinatesOver_Z W _

private theorem outerSumProjectivePoints_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairSumProjectivePointOver W (leftOuterPairToF W)
        (leftOuterRawZ_ne_zero W) =
      pairSumProjectivePointOver W (rightOuterPairToF W)
        (rightOuterRawZ_ne_zero W) := by
  rw [pairSumProjectivePointOver_eq_add W (leftOuterPairToF W),
    pairSumProjectivePointOver_eq_add W (rightOuterPairToF W),
    leftOuter_firstPoint, leftOuter_secondPoint,
    rightOuter_firstPoint, rightOuter_secondPoint,
    pairSumProjectivePointOver_eq_add W (pairTwelveToF W),
    pairSumProjectivePointOver_eq_add W (pairTwentyThreeToF W),
    middlePoints_eq]
  exact add_assoc _ _ _

private theorem outerSumCoordinates_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pairSumCoordinatesOver W (leftOuterPairToF W)
        (leftOuterRawZ_ne_zero W) =
      pairSumCoordinatesOver W (rightOuterPairToF W)
        (rightOuterRawZ_ne_zero W) := by
  have hclass := congrArg
    (fun P => WeierstrassCurve.Projective.Point.point P)
    (outerSumProjectivePoints_eq W)
  change
    (⟦pairSumCoordinatesOver W (leftOuterPairToF W)
        (leftOuterRawZ_ne_zero W)⟧ :
      WeierstrassCurve.Projective.PointClass (F W)) =
    ⟦pairSumCoordinatesOver W (rightOuterPairToF W)
        (rightOuterRawZ_ne_zero W)⟧ at hclass
  apply (WeierstrassCurve.Projective.equiv_iff_eq_of_Z_eq
    (P := pairSumCoordinatesOver W (leftOuterPairToF W)
      (leftOuterRawZ_ne_zero W))
    (Q := pairSumCoordinatesOver W (rightOuterPairToF W)
      (rightOuterRawZ_ne_zero W)) (by simp) (by simp)).mp
  exact Quotient.eq.mp hclass

private theorem chartAlgHom_ext
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) {φ ψ : A W →ₐ[K] L}
    (h : chartCoordinatesOver W φ = chartCoordinatesOver W ψ) :
    φ = ψ := by
  apply AlgHom.ext
  intro x
  have hr : φ.toRingHom = ψ.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply chartRingHom_ext (K := K) (coveringCoordinate true)
    · ext a
      change φ (coveringChartStructureRingHom W true a) =
        ψ (coveringChartStructureRingHom W true a)
      rw [← coveringChartCoordinateRing_algebraMap,
        φ.commutes, ψ.commutes]
    · intro j
      change φ (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (coveringCoordinate true) j)) =
        ψ (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (coveringCoordinate true) j))
      exact congrFun h j
  exact DFunLike.congr_fun hr x

private theorem outerSumAlgHom_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardPairSumAlgHom W (leftOuterPairToF W)
        (leftOuterRawZ_ne_zero W) =
      standardPairSumAlgHom W (rightOuterPairToF W)
        (rightOuterRawZ_ne_zero W) := by
  apply chartAlgHom_ext W
  exact outerSumCoordinates_eq W

private theorem genericPairTwentyThree_eq_standardPairPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    lift (genericSecond W) (genericThird W) =
      standardPairPointOver W (pairTwentyThreeToF W) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [genericSecond, standardPairPointOver, lift_fst]
    rw [pairTwentyThreeToF_left]
  · simp only [genericThird, standardPairPointOver, lift_snd]
    rw [pairTwentyThreeToF_right]

private theorem leftOuterPair_eq_standardPairPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    lift
        (standardChartPointOver W (sumTwelveToF W))
        (genericThird W) =
      standardPairPointOver W (leftOuterPairToF W) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [standardPairPointOver, lift_fst]
    rw [leftOuterPairToF_left]
  · simp only [genericThird, standardPairPointOver, lift_snd]
    rw [leftOuterPairToF_right]

private theorem rightOuterPair_eq_standardPairPoint
    (W : WeierstrassCurve K) [W.IsElliptic] :
    lift
        (genericFirst W)
        (standardChartPointOver W (sumTwentyThreeToF W)) =
      standardPairPointOver W (rightOuterPairToF W) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [genericFirst, standardPairPointOver, lift_fst]
    rw [rightOuterPairToF_left]
  · simp only [standardPairPointOver, lift_snd]
    rw [rightOuterPairToF_right]

private theorem genericTriple_leftAssociated_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    genericTripleOver W ≫
        (projectiveAdditionOver W ▷ toOver W) ≫
          projectiveAdditionOver W =
      standardChartPointOver W
        (standardPairSumAlgHom W (leftOuterPairToF W)
          (leftOuterRawZ_ne_zero W)) := by
  rw [genericTripleOver, lift_whiskerRight_assoc,
    genericPair_eq_standardPairPoint]
  change lift
      (standardPairPointOver W (pairTwelveToF W) ≫
        projectiveAdditionOver W)
      (genericThird W) ≫ projectiveAdditionOver W = _
  rw [standardPairPoint_addition W (pairTwelveToF W)
    (pairTwelveRawZ_ne_zero W)]
  change lift
      (standardChartPointOver W (sumTwelveToF W))
      (genericThird W) ≫ projectiveAdditionOver W = _
  rw [leftOuterPair_eq_standardPairPoint,
    standardPairPoint_addition W (leftOuterPairToF W)
      (leftOuterRawZ_ne_zero W)]

private theorem genericTriple_rightAssociated_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    genericTripleOver W ≫
        (α_ (toOver W) (toOver W) (toOver W)).hom ≫
          (toOver W ◁ projectiveAdditionOver W) ≫
            projectiveAdditionOver W =
      standardChartPointOver W
        (standardPairSumAlgHom W (rightOuterPairToF W)
          (rightOuterRawZ_ne_zero W)) := by
  rw [genericTripleOver, lift_lift_associator_hom_assoc,
    lift_whiskerLeft_assoc,
    genericPairTwentyThree_eq_standardPairPoint]
  change lift (genericFirst W)
      (standardPairPointOver W (pairTwentyThreeToF W) ≫
        projectiveAdditionOver W) ≫ projectiveAdditionOver W = _
  rw [standardPairPoint_addition W (pairTwentyThreeToF W)
    (pairTwentyThreeRawZ_ne_zero W)]
  change lift (genericFirst W)
      (standardChartPointOver W (sumTwentyThreeToF W)) ≫
        projectiveAdditionOver W = _
  rw [rightOuterPair_eq_standardPairPoint,
    standardPairPoint_addition W (rightOuterPairToF W)
      (rightOuterRawZ_ne_zero W)]

private theorem genericTriple_addition_assoc
    (W : WeierstrassCurve K) [W.IsElliptic] :
    genericTripleOver W ≫
        (projectiveAdditionOver W ▷ toOver W) ≫
          projectiveAdditionOver W =
      genericTripleOver W ≫
        (α_ (toOver W) (toOver W) (toOver W)).hom ≫
          (toOver W ◁ projectiveAdditionOver W) ≫
            projectiveAdditionOver W := by
  rw [genericTriple_leftAssociated_addition,
    genericTriple_rightAssociated_addition, outerSumAlgHom_eq]

/-- The globally glued projective addition is associative in the slice over
the coefficient field. -/
theorem projectiveAdditionOver_assoc
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (projectiveAdditionOver W ▷ toOver W) ≫
        projectiveAdditionOver W =
      (α_ (toOver W) (toOver W) (toOver W)).hom ≫
        (toOver W ◁ projectiveAdditionOver W) ≫
          projectiveAdditionOver W := by
  let f : (toOver W ⊗ toOver W) ⊗ toOver W ⟶ toOver W :=
    (projectiveAdditionOver W ▷ toOver W) ≫
      projectiveAdditionOver W
  let g : (toOver W ⊗ toOver W) ⊗ toOver W ⟶ toOver W :=
    (α_ (toOver W) (toOver W) (toOver W)).hom ≫
      (toOver W ◁ projectiveAdditionOver W) ≫
        projectiveAdditionOver W
  change f = g
  apply Over.OverMorphism.ext
  letI : IsReduced (((toOver W ⊗ toOver W) ⊗ toOver W).left) := by
    change IsReduced (Triple W)
    infer_instance
  apply ext_of_isDominant_of_isSeparated
    (s := structureMap W) (ι := (genericTripleOver W).left)
  · exact f.w.trans g.w.symm
  · have h := congrArg (fun q => q.left)
      (genericTriple_addition_assoc W)
    exact h

/-- The canonical group-object structure on the projective Weierstrass cubic.
Its operations are exactly the globally checked addition, infinity section,
and projective negation morphisms. -/
noncomputable instance projectiveGrpObj
    (W : WeierstrassCurve K) [W.IsElliptic] : GrpObj (toOver W) where
  one := infinitySectionOver W
  mul := projectiveAdditionOver W
  inv := negationOver W
  one_mul := infinitySectionOver_projectiveAdditionOver_left_unit W
  mul_one := infinitySectionOver_projectiveAdditionOver_right_unit W
  mul_assoc := projectiveAdditionOver_assoc W
  left_inv := projectiveAdditionOver_negation_left_inv W
  right_inv := projectiveAdditionOver_negation_right_inv W

/-- The canonical projective Weierstrass group object is commutative. -/
noncomputable instance projectiveIsCommMonObj
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsCommMonObj (toOver W) where
  mul_comm := projectiveAdditionOver_comm W


end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
