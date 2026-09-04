/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductAtlas

/-!
# Coordinate rings for the projective Weierstrass product atlas

Each member of the four-chart cover of the projective Weierstrass pair is an
affine fibre product.  This file identifies it with the spectrum of the tensor
product of the two chart coordinate rings and packages the contravariant
coordinate-ring constructor for morphisms out of that member.

This is the design boundary between the already constructed projective atlas
and the remaining local addition formulas.  Those formulas should be supplied
as `K`-algebra maps into `projectivePairChartCoordinateRing`; the constructor
below turns such a formula into a scheme morphism.  The two input projections
are named downstream consumers which verify that this interface has the
expected geometric orientation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The scalar structure on a cubic chart is the one induced by its checked
structural ring homomorphism. -/
noncomputable instance coveringChartCoordinateRingAlgebra
    (W : WeierstrassCurve K) (b : Bool) :
    Algebra K (coveringChartCoordinateRing W b) :=
  (coveringChartStructureRingHom W b).toAlgebra

/-- The algebra map on a chart is definitionally its checked structural ring
homomorphism. -/
theorem coveringChartCoordinateRing_algebraMap
    (W : WeierstrassCurve K) (b : Bool) :
    algebraMap K (coveringChartCoordinateRing W b) =
      coveringChartStructureRingHom W b :=
  rfl

/-- The tensor-product coordinate ring of one member of the projective-pair
atlas. -/
abbrev projectivePairChartCoordinateRing (W : WeierstrassCurve K)
    (ij : Bool × Bool) :=
  TensorProduct K (coveringChartCoordinateRing W ij.1)
    (coveringChartCoordinateRing W ij.2)

/-- Every member of the projective-pair atlas is the spectrum of the tensor
product of its two chart coordinate rings. -/
noncomputable def projectivePairChartIsoSpecTensor
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartScheme W ij ≅
      Spec (.of (projectivePairChartCoordinateRing W ij)) :=
  pullback.congrHom
      (coveringChartMap_comp_structureMap W ij.1)
      (coveringChartMap_comp_structureMap W ij.2) ≪≫
    pullbackSpecIso K (coveringChartCoordinateRing W ij.1)
      (coveringChartCoordinateRing W ij.2)

/-- Under the affine presentation, the tensor-product left inclusion is the
first pullback projection. -/
@[reassoc]
theorem projectivePairChartIsoSpecTensor_hom_fst
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartIsoSpecTensor W ij).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := K)
            (A := coveringChartCoordinateRing W ij.1)
            (B := coveringChartCoordinateRing W ij.2))) =
      pullback.fst
        (coveringChartMap W ij.1 ≫ structureMap W)
        (coveringChartMap W ij.2 ≫ structureMap W) := by
  simp only [projectivePairChartIsoSpecTensor, Iso.trans_hom,
    Category.assoc, pullbackSpecIso_hom_fst,
    pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]

/-- Under the affine presentation, the tensor-product right inclusion is the
second pullback projection. -/
@[reassoc]
theorem projectivePairChartIsoSpecTensor_hom_snd
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartIsoSpecTensor W ij).hom ≫
        Spec.map (CommRingCat.ofHom
          (RingHomClass.toRingHom
            (Algebra.TensorProduct.includeRight
              (R := K)
              (A := coveringChartCoordinateRing W ij.1)
              (B := coveringChartCoordinateRing W ij.2)))) =
      pullback.snd
        (coveringChartMap W ij.1 ≫ structureMap W)
        (coveringChartMap W ij.2 ≫ structureMap W) := by
  simp only [projectivePairChartIsoSpecTensor, Iso.trans_hom,
    Category.assoc, pullbackSpecIso_hom_snd,
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

/-- The affine presentation respects the common structural morphism to
`Spec K`. -/
@[reassoc]
theorem projectivePairChartIsoSpecTensor_hom_base
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartIsoSpecTensor W ij).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (projectivePairChartCoordinateRing W ij))) =
      pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W ij.1)) := by
  simp only [projectivePairChartIsoSpecTensor, Iso.trans_hom,
    Category.assoc, pullbackSpecIso_hom_base,
    pullback.congrHom_hom, pullback.lift_fst_assoc, Category.id_comp]

/-- In particular, every member of the projective-pair atlas is affine. -/
instance projectivePairChartScheme_isAffine
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    IsAffine (projectivePairChartScheme W ij) :=
  IsAffine.of_isIso (projectivePairChartIsoSpecTensor W ij).hom

/-- Turn a `K`-algebra formula on a projective-pair chart into a morphism to a
chosen output chart of the projective cubic. -/
noncomputable def projectivePairChartMorphismOfCoordinateRingHom
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool)
    (φ : coveringChartCoordinateRing W out →ₐ[K]
      projectivePairChartCoordinateRing W ij) :
    projectivePairChartScheme W ij ⟶ scheme W :=
  (projectivePairChartIsoSpecTensor W ij).hom ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    coveringChartMap W out

/-- Every morphism produced by the coordinate-ring interface is a morphism
over `Spec K`. -/
@[reassoc]
theorem projectivePairChartMorphismOfCoordinateRingHom_comp_structureMap
    (W : WeierstrassCurve K) (ij : Bool × Bool) (out : Bool)
    (φ : coveringChartCoordinateRing W out →ₐ[K]
      projectivePairChartCoordinateRing W ij) :
    projectivePairChartMorphismOfCoordinateRingHom W ij out φ ≫
        structureMap W =
      pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W ij.1)) := by
  have hφ : φ.toRingHom.comp (coveringChartStructureRingHom W out) =
      algebraMap K (projectivePairChartCoordinateRing W ij) := by
    ext a
    exact φ.commutes a
  calc
    projectivePairChartMorphismOfCoordinateRingHom W ij out φ ≫
          structureMap W =
        (projectivePairChartIsoSpecTensor W ij).hom ≫
          Spec.map (CommRingCat.ofHom
            (φ.toRingHom.comp
              (coveringChartStructureRingHom W out))) := by
            simp only [projectivePairChartMorphismOfCoordinateRingHom,
              Category.assoc, coveringChartMap_comp_structureMap,
              ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    _ = (projectivePairChartIsoSpecTensor W ij).hom ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (projectivePairChartCoordinateRing W ij))) := by
            rw [hφ]
    _ = pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W ij.1)) :=
      projectivePairChartIsoSpecTensor_hom_base W ij

/-- The first input point, reconstructed through the coordinate-ring
interface. -/
noncomputable def projectivePairChartFirstInput
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartScheme W ij ⟶ scheme W :=
  projectivePairChartMorphismOfCoordinateRingHom W ij ij.1
    Algebra.TensorProduct.includeLeft

/-- The coordinate-ring reconstruction of the first input is the first
pullback projection followed by its chart map. -/
theorem projectivePairChartFirstInput_eq
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartFirstInput W ij =
      pullback.fst
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        coveringChartMap W ij.1 := by
  rw [projectivePairChartFirstInput,
    projectivePairChartMorphismOfCoordinateRingHom,
    show (Algebra.TensorProduct.includeLeft
      (R := K)
      (A := coveringChartCoordinateRing W ij.1)
      (B := coveringChartCoordinateRing W ij.2)).toRingHom =
        Algebra.TensorProduct.includeLeftRingHom by rfl,
    projectivePairChartIsoSpecTensor_hom_fst_assoc]

/-- The second input point, reconstructed through the coordinate-ring
interface. -/
noncomputable def projectivePairChartSecondInput
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartScheme W ij ⟶ scheme W :=
  projectivePairChartMorphismOfCoordinateRingHom W ij ij.2
    Algebra.TensorProduct.includeRight

/-- The coordinate-ring reconstruction of the second input is the second
pullback projection followed by its chart map. -/
theorem projectivePairChartSecondInput_eq
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartSecondInput W ij =
      pullback.snd
          (coveringChartMap W ij.1 ≫ structureMap W)
          (coveringChartMap W ij.2 ≫ structureMap W) ≫
        coveringChartMap W ij.2 := by
  rw [projectivePairChartSecondInput,
    projectivePairChartMorphismOfCoordinateRingHom,
    AlgHom.toRingHom_eq_coe,
    projectivePairChartIsoSpecTensor_hom_snd_assoc]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
