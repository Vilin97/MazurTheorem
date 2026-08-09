/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.TensorProduct.Pi
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfCardinalityBound
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneBaseIso
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFiniteAffineFamily
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MuSchemePowerKernelComparison

/-!
# Effectivity of multiplicative cocycles on finite affine fppf families

This file passes in the direction deliberately left open by
`MultiplicativeFiniteAffineFamily`.  An arbitrary represented `G_m` cocycle on a finite affine
fppf family is assembled, through the finite-product tensor algebra, into faithfully-flat
descent data for the singleton spectrum of the product algebra.  Over a principal ideal domain,
effective rank-one descent then supplies a compatible gauge on every component.

The construction is applied below to finite affine refinements of arbitrary fppf covers of
`Spec ℤ`.  This proves the actual represented global `H¹(G_m)` vanishing needed by the integral
Kummer sequence; no descent or Picard hypothesis is exposed to callers.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
namespace FiniteAffineFamilyEffectivity

open AffineCommGroupScheme
open CategoryTheory.PresheafOfGroups
open FiniteAffineFamily
open FiniteFlatCommGroupScheme
open MultiplicativeKummer

private local instance flatIsZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Flat) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @Flat) (Q := RingHom.Flat)

private local instance locallyOfFinitePresentationIsZariskiLocalAtSource :
    IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)

private local instance fppfPropertyIsZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Flat ⊓ @LocallyOfFinitePresentation) :=
  MorphismProperty.IsLocalAtSource.inf _ _

variable {A : Type u} [CommRing A]
variable {I : Type u} [Fintype I]
variable (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]

private noncomputable def tensorPiLeft (C : Type u) [CommRing C] [Algebra A C] :
    (ProductAlgebra B) ⊗[A] C ≃ₐ[A] ∀ i, B i ⊗[A] C := by
  classical
  exact (Algebra.TensorProduct.comm A (ProductAlgebra B) C).trans <|
    (Algebra.TensorProduct.piRight A A C B).trans <|
      AlgEquiv.piCongrRight fun i ↦ Algebra.TensorProduct.comm A C (B i)

/-- The product-overlap algebra is the product of all pairwise overlap algebras. -/
private noncomputable def productPairEquiv :
    (ProductAlgebra B) ⊗[A] (ProductAlgebra B) ≃ₐ[A]
      ∀ j, ∀ i, B i ⊗[A] B j := by
  classical
  exact (Algebra.TensorProduct.piRight A A (ProductAlgebra B) B).trans <|
    AlgEquiv.piCongrRight fun j ↦ tensorPiLeft (A := A) B (B j)

/-- The first projection from a heterogeneous affine pair overlap. -/
private noncomputable def pairLeft (i j : I) :
    testObject (R := A) (B i ⊗[A] B j) ⟶ testObject (R := A) (B i) :=
  testObjectMap Algebra.TensorProduct.includeLeft

/-- The second projection from a heterogeneous affine pair overlap. -/
private noncomputable def pairRight (i j : I) :
    testObject (R := A) (B i ⊗[A] B j) ⟶ testObject (R := A) (B j) :=
  testObjectMap Algebra.TensorProduct.includeRight

/-- The universal unit carried by a represented cocycle on the `(i,j)` overlap. -/
private noncomputable def overlapUnit
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (i j : I) : (B i ⊗[A] B j)ˣ :=
  multiplicativePointMulEquiv A (B i ⊗[A] B j)
    (c.ev i j (pairLeft (A := A) B i j) (pairRight (A := A) B i j))

private theorem testObjectMap_comp
    {C D E : Type u} [CommRing C] [CommRing D] [CommRing E]
    [Algebra A C] [Algebra A D] [Algebra A E]
    (f : C →ₐ[A] D) (g : D →ₐ[A] E) :
    testObjectMap g ≫ testObjectMap f = testObjectMap (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  rfl

private noncomputable def pairDiagonal (i : I) :
    testObject (R := A) (B i) ⟶ testObject (R := A) (B i ⊗[A] B i) :=
  testObjectMap (Algebra.TensorProduct.lmul' A)

omit [Fintype I] in
private theorem pairDiagonal_pairLeft (i : I) :
    pairDiagonal (A := A) B i ≫ pairLeft (A := A) B i i = 𝟙 _ := by
  rw [pairDiagonal, pairLeft, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id, Spec.map_inj]
  ext b
  simp

omit [Fintype I] in
private theorem pairDiagonal_pairRight (i : I) :
    pairDiagonal (A := A) B i ≫ pairRight (A := A) B i i = 𝟙 _ := by
  rw [pairDiagonal, pairRight, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id, Spec.map_inj]
  ext b
  simp

omit [Fintype I] in
private theorem overlapUnit_normalization
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (i : I) :
    Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom
      (overlapUnit (A := A) B c i i) = 1 := by
  letI : CommGroup ((multiplicative A).Point (B i)) :=
    AffineCommGroupScheme.pointCommGroup (multiplicative A) (B i)
  let x : (multiplicative A).Point (B i ⊗[A] B i) :=
    c.ev i i (pairLeft (A := A) B i i) (pairRight (A := A) B i i)
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := Algebra.TensorProduct.lmul' A) (x := x)
  change Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom
      (multiplicativePointMulEquiv A (B i ⊗[A] B i) x) = 1
  rw [← hnat]
  have hpre := c.ev_precomp i i (pairDiagonal (A := A) B i)
    (pairLeft (A := A) B i i) (pairRight (A := A) B i i)
  change pairDiagonal (A := A) B i ≫
      c.ev i i (pairLeft (A := A) B i i) (pairRight (A := A) B i i) =
    c.ev i i (pairDiagonal (A := A) B i ≫ pairLeft (A := A) B i i)
      (pairDiagonal (A := A) B i ≫ pairRight (A := A) B i i) at hpre
  rw [pairDiagonal_pairLeft (A := A), pairDiagonal_pairRight (A := A)] at hpre
  dsimp only [pairDiagonal] at hpre
  have hrefl := OneCocycle.ev_refl
    (pointPresheaf (multiplicativeScheme A)) (componentFamily B) c i
    (𝟙 (testObject (R := A) (B i)))
  change c.ev i i (𝟙 _) (𝟙 _) = (1 : (multiplicative A).Point (B i)) at hrefl
  change testObjectMap (Algebra.TensorProduct.lmul' A) ≫ x =
      c.ev i i (𝟙 _) (𝟙 _) at hpre
  rw [hpre, hrefl]
  exact map_one (multiplicativePointMulEquiv A (B i))

/-- The heterogeneous triple-overlap algebra for components `i`, `j`, and `k`. -/
private abbrev TripleAlgebra (i j k : I) := B i ⊗[A] (B j ⊗[A] B k)

private noncomputable def tripleFirst (i j k : I) :
    B i →ₐ[A] TripleAlgebra (A := A) B i j k :=
  Algebra.TensorProduct.includeLeft

private noncomputable def tripleSecond (i j k : I) :
    B j →ₐ[A] TripleAlgebra (A := A) B i j k :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft

private noncomputable def tripleThird (i j k : I) :
    B k →ₐ[A] TripleAlgebra (A := A) B i j k :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight

private noncomputable def pullTwelveMap (i j k : I) :
    B i ⊗[A] B j →ₐ[A] TripleAlgebra (A := A) B i j k :=
  Algebra.TensorProduct.productMap (tripleFirst (A := A) B i j k)
    (tripleSecond (A := A) B i j k)

private noncomputable def pullTwentyThreeMap (i j k : I) :
    B j ⊗[A] B k →ₐ[A] TripleAlgebra (A := A) B i j k :=
  Algebra.TensorProduct.includeRight

private noncomputable def pullThirteenMap (i j k : I) :
    B i ⊗[A] B k →ₐ[A] TripleAlgebra (A := A) B i j k :=
  Algebra.TensorProduct.productMap (tripleFirst (A := A) B i j k)
    (tripleThird (A := A) B i j k)

private noncomputable def tripleFirstObject (i j k : I) :
    testObject (R := A) (TripleAlgebra (A := A) B i j k) ⟶ testObject (R := A) (B i) :=
  testObjectMap (tripleFirst (A := A) B i j k)

private noncomputable def tripleSecondObject (i j k : I) :
    testObject (R := A) (TripleAlgebra (A := A) B i j k) ⟶ testObject (R := A) (B j) :=
  testObjectMap (tripleSecond (A := A) B i j k)

private noncomputable def tripleThirdObject (i j k : I) :
    testObject (R := A) (TripleAlgebra (A := A) B i j k) ⟶ testObject (R := A) (B k) :=
  testObjectMap (tripleThird (A := A) B i j k)

private noncomputable def pullTwelveObject (i j k : I) :
    testObject (R := A) (TripleAlgebra (A := A) B i j k) ⟶
      testObject (R := A) (B i ⊗[A] B j) :=
  testObjectMap (pullTwelveMap (A := A) B i j k)

private noncomputable def pullTwentyThreeObject (i j k : I) :
    testObject (R := A) (TripleAlgebra (A := A) B i j k) ⟶
      testObject (R := A) (B j ⊗[A] B k) :=
  testObjectMap (pullTwentyThreeMap (A := A) B i j k)

private noncomputable def pullThirteenObject (i j k : I) :
    testObject (R := A) (TripleAlgebra (A := A) B i j k) ⟶
      testObject (R := A) (B i ⊗[A] B k) :=
  testObjectMap (pullThirteenMap (A := A) B i j k)

omit [Fintype I] in
private theorem pullTwelve_pairLeft (i j k : I) :
    pullTwelveObject (A := A) B i j k ≫ pairLeft (A := A) B i j =
      tripleFirstObject (A := A) B i j k := by
  rw [pullTwelveObject, pairLeft, tripleFirstObject, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pullTwelveMap, tripleFirst, tripleSecond]

omit [Fintype I] in
private theorem pullTwelve_pairRight (i j k : I) :
    pullTwelveObject (A := A) B i j k ≫ pairRight (A := A) B i j =
      tripleSecondObject (A := A) B i j k := by
  rw [pullTwelveObject, pairRight, tripleSecondObject, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pullTwelveMap, tripleFirst, tripleSecond]

omit [Fintype I] in
private theorem pullTwentyThree_pairLeft (i j k : I) :
    pullTwentyThreeObject (A := A) B i j k ≫ pairLeft (A := A) B j k =
      tripleSecondObject (A := A) B i j k := by
  rw [pullTwentyThreeObject, pairLeft, tripleSecondObject, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pullTwentyThreeMap, tripleSecond]

omit [Fintype I] in
private theorem pullTwentyThree_pairRight (i j k : I) :
    pullTwentyThreeObject (A := A) B i j k ≫ pairRight (A := A) B j k =
      tripleThirdObject (A := A) B i j k := by
  rw [pullTwentyThreeObject, pairRight, tripleThirdObject, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pullTwentyThreeMap, tripleThird]

omit [Fintype I] in
private theorem pullThirteen_pairLeft (i j k : I) :
    pullThirteenObject (A := A) B i j k ≫ pairLeft (A := A) B i k =
      tripleFirstObject (A := A) B i j k := by
  rw [pullThirteenObject, pairLeft, tripleFirstObject, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pullThirteenMap, tripleFirst, tripleThird]

omit [Fintype I] in
private theorem pullThirteen_pairRight (i j k : I) :
    pullThirteenObject (A := A) B i j k ≫ pairRight (A := A) B i k =
      tripleThirdObject (A := A) B i j k := by
  rw [pullThirteenObject, pairRight, tripleThirdObject, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pullThirteenMap, tripleFirst, tripleThird]

omit [Fintype I] in
private theorem overlapUnit_pullTwelve
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (i j k : I) :
    Units.map (pullTwelveMap (A := A) B i j k).toMonoidHom
        (overlapUnit (A := A) B c i j) =
      multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k)
        (c.ev i j (tripleFirstObject (A := A) B i j k)
          (tripleSecondObject (A := A) B i j k)) := by
  let x : (multiplicative A).Point (B i ⊗[A] B j) :=
    c.ev i j (pairLeft (A := A) B i j) (pairRight (A := A) B i j)
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pullTwelveMap (A := A) B i j k) (x := x)
  change Units.map (pullTwelveMap (A := A) B i j k).toMonoidHom
      (multiplicativePointMulEquiv A (B i ⊗[A] B j) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp i j (pullTwelveObject (A := A) B i j k)
    (pairLeft (A := A) B i j) (pairRight (A := A) B i j)
  change pullTwelveObject (A := A) B i j k ≫ x =
    c.ev i j (pullTwelveObject (A := A) B i j k ≫ pairLeft (A := A) B i j)
      (pullTwelveObject (A := A) B i j k ≫ pairRight (A := A) B i j) at hpre
  rw [pullTwelve_pairLeft, pullTwelve_pairRight] at hpre
  dsimp only [pullTwelveObject] at hpre
  exact congrArg (multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k)) hpre

omit [Fintype I] in
private theorem overlapUnit_pullTwentyThree
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (i j k : I) :
    Units.map (pullTwentyThreeMap (A := A) B i j k).toMonoidHom
        (overlapUnit (A := A) B c j k) =
      multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k)
        (c.ev j k (tripleSecondObject (A := A) B i j k)
          (tripleThirdObject (A := A) B i j k)) := by
  let x : (multiplicative A).Point (B j ⊗[A] B k) :=
    c.ev j k (pairLeft (A := A) B j k) (pairRight (A := A) B j k)
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pullTwentyThreeMap (A := A) B i j k) (x := x)
  change Units.map (pullTwentyThreeMap (A := A) B i j k).toMonoidHom
      (multiplicativePointMulEquiv A (B j ⊗[A] B k) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp j k (pullTwentyThreeObject (A := A) B i j k)
    (pairLeft (A := A) B j k) (pairRight (A := A) B j k)
  change pullTwentyThreeObject (A := A) B i j k ≫ x =
    c.ev j k (pullTwentyThreeObject (A := A) B i j k ≫ pairLeft (A := A) B j k)
      (pullTwentyThreeObject (A := A) B i j k ≫ pairRight (A := A) B j k) at hpre
  rw [pullTwentyThree_pairLeft, pullTwentyThree_pairRight] at hpre
  dsimp only [pullTwentyThreeObject] at hpre
  exact congrArg (multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k)) hpre

omit [Fintype I] in
private theorem overlapUnit_pullThirteen
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (i j k : I) :
    Units.map (pullThirteenMap (A := A) B i j k).toMonoidHom
        (overlapUnit (A := A) B c i k) =
      multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k)
        (c.ev i k (tripleFirstObject (A := A) B i j k)
          (tripleThirdObject (A := A) B i j k)) := by
  let x : (multiplicative A).Point (B i ⊗[A] B k) :=
    c.ev i k (pairLeft (A := A) B i k) (pairRight (A := A) B i k)
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pullThirteenMap (A := A) B i j k) (x := x)
  change Units.map (pullThirteenMap (A := A) B i j k).toMonoidHom
      (multiplicativePointMulEquiv A (B i ⊗[A] B k) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp i k (pullThirteenObject (A := A) B i j k)
    (pairLeft (A := A) B i k) (pairRight (A := A) B i k)
  change pullThirteenObject (A := A) B i j k ≫ x =
    c.ev i k (pullThirteenObject (A := A) B i j k ≫ pairLeft (A := A) B i k)
      (pullThirteenObject (A := A) B i j k ≫ pairRight (A := A) B i k) at hpre
  rw [pullThirteen_pairLeft, pullThirteen_pairRight] at hpre
  dsimp only [pullThirteenObject] at hpre
  exact congrArg (multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k)) hpre

omit [Fintype I] in
private theorem overlapUnit_cocycle
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (i j k : I) :
    Units.map (pullTwelveMap (A := A) B i j k).toMonoidHom
          (overlapUnit (A := A) B c i j) *
        Units.map (pullTwentyThreeMap (A := A) B i j k).toMonoidHom
          (overlapUnit (A := A) B c j k) =
      Units.map (pullThirteenMap (A := A) B i j k).toMonoidHom
        (overlapUnit (A := A) B c i k) := by
  letI : CommGroup ((multiplicative A).Point (TripleAlgebra (A := A) B i j k)) :=
    AffineCommGroupScheme.pointCommGroup (multiplicative A)
      (TripleAlgebra (A := A) B i j k)
  let x₁₂ : (multiplicative A).Point (TripleAlgebra (A := A) B i j k) :=
    c.ev i j (tripleFirstObject (A := A) B i j k)
      (tripleSecondObject (A := A) B i j k)
  let x₂₃ : (multiplicative A).Point (TripleAlgebra (A := A) B i j k) :=
    c.ev j k (tripleSecondObject (A := A) B i j k)
      (tripleThirdObject (A := A) B i j k)
  let x₁₃ : (multiplicative A).Point (TripleAlgebra (A := A) B i j k) :=
    c.ev i k (tripleFirstObject (A := A) B i j k)
      (tripleThirdObject (A := A) B i j k)
  rw [overlapUnit_pullTwelve, overlapUnit_pullTwentyThree, overlapUnit_pullThirteen]
  change multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k) x₁₂ *
      multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k) x₂₃ =
    multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k) x₁₃
  rw [← map_mul]
  have htrans := c.ev_trans i j k (tripleFirstObject (A := A) B i j k)
    (tripleSecondObject (A := A) B i j k) (tripleThirdObject (A := A) B i j k)
  change x₁₂ * x₂₃ = x₁₃ at htrans
  exact congrArg
    (multiplicativePointMulEquiv A (TripleAlgebra (A := A) B i j k)) htrans

private noncomputable def pairEval (i j : I) :
    (ProductAlgebra B) ⊗[A] (ProductAlgebra B) →ₐ[A] B i ⊗[A] B j :=
  Algebra.TensorProduct.map (Pi.evalAlgHom A B i) (Pi.evalAlgHom A B j)

private theorem productPairEquiv_apply
    (x : (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) (i j : I) :
    productPairEquiv (A := A) B x j i = pairEval (A := A) B i j x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [productPairEquiv, tensorPiLeft, pairEval]
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

private noncomputable def nestedPiUnitsEquiv :
    (∀ j, ∀ i, B i ⊗[A] B j)ˣ ≃* ∀ j, ∀ i, (B i ⊗[A] B j)ˣ :=
  (MulEquiv.piUnits :
      (∀ j, ∀ i, B i ⊗[A] B j)ˣ ≃* ∀ j, (∀ i, B i ⊗[A] B j)ˣ).trans <|
    MulEquiv.piCongrRight fun j ↦
      (MulEquiv.piUnits : (∀ i, B i ⊗[A] B j)ˣ ≃* ∀ i, (B i ⊗[A] B j)ˣ)

private noncomputable def productPairUnitsEquiv :
    ((ProductAlgebra B) ⊗[A] (ProductAlgebra B))ˣ ≃*
      ∀ j, ∀ i, (B i ⊗[A] B j)ˣ :=
  (Units.mapEquiv (productPairEquiv (A := A) B).toMulEquiv).trans
    (nestedPiUnitsEquiv (A := A) B)

/-- Assemble all pairwise overlap units into the unit on the singleton product overlap. -/
private noncomputable def productOverlapUnit
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B)) :
    ((ProductAlgebra B) ⊗[A] (ProductAlgebra B))ˣ :=
  (productPairUnitsEquiv (A := A) B).symm fun j i ↦ overlapUnit (A := A) B c i j

private theorem productOverlapUnit_pairEval
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (i j : I) :
    Units.map (pairEval (A := A) B i j).toMonoidHom (productOverlapUnit (A := A) B c) =
      overlapUnit (A := A) B c i j := by
  apply Units.ext
  change pairEval (A := A) B i j (productOverlapUnit (A := A) B c :
    (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) =
      (overlapUnit (A := A) B c i j : _)
  rw [← productPairEquiv_apply]
  have h := congrArg (fun z ↦ z j i)
    ((productPairUnitsEquiv (A := A) B).apply_symm_apply
      (fun j i ↦ overlapUnit (A := A) B c i j))
  calc
    productPairEquiv (A := A) B
        (productOverlapUnit (A := A) B c :
          (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) j i =
      (((productPairUnitsEquiv (A := A) B)
        (productOverlapUnit (A := A) B c)) j i : B i ⊗[A] B j) := rfl
    _ = (overlapUnit (A := A) B c i j : _) := congrArg Units.val h

omit [Fintype I] in
private theorem eval_comp_productMultiplication (i : I) :
    (Pi.evalAlgHom A B i).comp
        (Algebra.TensorProduct.lmul' A :
          (ProductAlgebra B) ⊗[A] (ProductAlgebra B) →ₐ[A] ProductAlgebra B) =
      (Algebra.TensorProduct.lmul' A).comp (pairEval (A := A) B i i) := by
  ext x <;> simp [pairEval]

private noncomputable def productTripleEquiv :
    tripleRing (A := A) (B := ProductAlgebra B) ≃ₐ[A]
      ∀ k, ∀ j, ∀ i, TripleAlgebra (A := A) B i j k := by
  classical
  exact
    (Algebra.TensorProduct.congr (AlgEquiv.refl : ProductAlgebra B ≃ₐ[A] ProductAlgebra B)
      (productPairEquiv (A := A) B)).trans <|
    (Algebra.TensorProduct.piRight A A (ProductAlgebra B)
      (fun k ↦ ∀ j, B j ⊗[A] B k)).trans <|
    AlgEquiv.piCongrRight fun k ↦
      (Algebra.TensorProduct.piRight A A (ProductAlgebra B)
        (fun j ↦ B j ⊗[A] B k)).trans <|
      AlgEquiv.piCongrRight fun j ↦ tensorPiLeft (A := A) B (B j ⊗[A] B k)

private noncomputable def tripleEval (i j k : I) :
    tripleRing (A := A) (B := ProductAlgebra B) →ₐ[A]
      TripleAlgebra (A := A) B i j k :=
  Algebra.TensorProduct.map (Pi.evalAlgHom A B i)
    (Algebra.TensorProduct.map (Pi.evalAlgHom A B j) (Pi.evalAlgHom A B k))

private theorem productTripleEquiv_apply
    (x : tripleRing (A := A) (B := ProductAlgebra B)) (i j k : I) :
    productTripleEquiv (A := A) B x k j i = tripleEval (A := A) B i j k x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x yz =>
      induction yz using TensorProduct.induction_on with
      | zero => simp
      | tmul y z => simp [productTripleEquiv, productPairEquiv, tensorPiLeft, tripleEval]
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, hy, hz]
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

omit [Fintype I] in
private theorem tripleEval_comp_pairTwelve (i j k : I) :
    (tripleEval (A := A) B i j k).comp
        (pairTwelve (A := A) (B := ProductAlgebra B)) =
      (pullTwelveMap (A := A) B i j k).comp (pairEval (A := A) B i j) := by
  ext x <;>
  simp [tripleEval, pairEval, pullTwelveMap, tripleFirst, tripleSecond,
    pairTwelve, firstToTriple, secondToTriple]

omit [Fintype I] in
private theorem tripleEval_comp_pairTwentyThree (i j k : I) :
    (tripleEval (A := A) B i j k).comp
        (pairTwentyThree (A := A) (B := ProductAlgebra B)) =
      (pullTwentyThreeMap (A := A) B i j k).comp (pairEval (A := A) B j k) := by
  ext x <;>
  simp [tripleEval, pairEval, pullTwentyThreeMap, pairTwentyThree]

omit [Fintype I] in
private theorem tripleEval_comp_pairThirteen (i j k : I) :
    (tripleEval (A := A) B i j k).comp
        (pairThirteen (A := A) (B := ProductAlgebra B)) =
      (pullThirteenMap (A := A) B i j k).comp (pairEval (A := A) B i k) := by
  ext x <;>
  simp [tripleEval, pairEval, pullThirteenMap, tripleFirst, tripleThird,
    pairThirteen, firstToTriple, thirdToTriple]

private theorem productOverlapUnit_normalization
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B)) :
    Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom
      (productOverlapUnit (A := A) B c) = 1 := by
  apply Units.ext
  funext i
  have hpair := congrArg Units.val (productOverlapUnit_pairEval (A := A) B c i i)
  change pairEval (A := A) B i i (productOverlapUnit (A := A) B c :
      (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) =
    (overlapUnit (A := A) B c i i : B i ⊗[A] B i) at hpair
  have hnorm := congrArg Units.val (overlapUnit_normalization (A := A) B c i)
  change (Algebra.TensorProduct.lmul' A) (overlapUnit (A := A) B c i i :
      B i ⊗[A] B i) = 1 at hnorm
  change (Pi.evalAlgHom A B i)
      ((Algebra.TensorProduct.lmul' A)
        (productOverlapUnit (A := A) B c :
          (ProductAlgebra B) ⊗[A] (ProductAlgebra B))) = 1
  calc
    _ = (Algebra.TensorProduct.lmul' A)
        (pairEval (A := A) B i i (productOverlapUnit (A := A) B c :
          (ProductAlgebra B) ⊗[A] (ProductAlgebra B))) := by
      exact congrArg
        (fun f : (ProductAlgebra B) ⊗[A] (ProductAlgebra B) →ₐ[A] B i ↦
          f (productOverlapUnit (A := A) B c :
            (ProductAlgebra B) ⊗[A] (ProductAlgebra B)))
        (eval_comp_productMultiplication (A := A) B i)
    _ = (Algebra.TensorProduct.lmul' A)
        (overlapUnit (A := A) B c i i : B i ⊗[A] B i) := by
      rw [hpair]
    _ = 1 := hnorm

private theorem productOverlapUnit_cocycle
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B)) :
    Units.map (pairTwelve (A := A) (B := ProductAlgebra B)).toMonoidHom
          (productOverlapUnit (A := A) B c) *
        Units.map (pairTwentyThree (A := A) (B := ProductAlgebra B)).toMonoidHom
          (productOverlapUnit (A := A) B c) =
      Units.map (pairThirteen (A := A) (B := ProductAlgebra B)).toMonoidHom
        (productOverlapUnit (A := A) B c) := by
  apply Units.ext
  apply (productTripleEquiv (A := A) B).injective
  funext k j i
  rw [productTripleEquiv_apply, productTripleEquiv_apply]
  change tripleEval (A := A) B i j k
        (pairTwelve (A := A) (B := ProductAlgebra B)
            (productOverlapUnit (A := A) B c : _) *
          pairTwentyThree (A := A) (B := ProductAlgebra B)
            (productOverlapUnit (A := A) B c : _)) =
    tripleEval (A := A) B i j k
      (pairThirteen (A := A) (B := ProductAlgebra B)
        (productOverlapUnit (A := A) B c : _))
  rw [map_mul]
  change ((tripleEval (A := A) B i j k).comp
        (pairTwelve (A := A) (B := ProductAlgebra B)))
          (productOverlapUnit (A := A) B c : _) *
      ((tripleEval (A := A) B i j k).comp
        (pairTwentyThree (A := A) (B := ProductAlgebra B)))
          (productOverlapUnit (A := A) B c : _) =
    ((tripleEval (A := A) B i j k).comp
      (pairThirteen (A := A) (B := ProductAlgebra B)))
        (productOverlapUnit (A := A) B c : _)
  rw [tripleEval_comp_pairTwelve, tripleEval_comp_pairTwentyThree,
    tripleEval_comp_pairThirteen]
  change pullTwelveMap (A := A) B i j k
        (pairEval (A := A) B i j (productOverlapUnit (A := A) B c : _)) *
      pullTwentyThreeMap (A := A) B i j k
        (pairEval (A := A) B j k (productOverlapUnit (A := A) B c : _)) =
    pullThirteenMap (A := A) B i j k
      (pairEval (A := A) B i k (productOverlapUnit (A := A) B c : _))
  have hij := congrArg Units.val (productOverlapUnit_pairEval (A := A) B c i j)
  have hjk := congrArg Units.val (productOverlapUnit_pairEval (A := A) B c j k)
  have hik := congrArg Units.val (productOverlapUnit_pairEval (A := A) B c i k)
  change pairEval (A := A) B i j (productOverlapUnit (A := A) B c : _) =
    (overlapUnit (A := A) B c i j : _) at hij
  change pairEval (A := A) B j k (productOverlapUnit (A := A) B c : _) =
    (overlapUnit (A := A) B c j k : _) at hjk
  change pairEval (A := A) B i k (productOverlapUnit (A := A) B c : _) =
    (overlapUnit (A := A) B c i k : _) at hik
  rw [hij, hjk, hik]
  exact congrArg Units.val (overlapUnit_cocycle (A := A) B c i j k)

/-- The arbitrary finite-family represented cocycle assembled as singleton tensor descent data
on the product algebra. -/
private noncomputable def productMultiplicativeUnitCocycle
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B)) :
    MultiplicativeUnitCocycle (A := A) (B := ProductAlgebra B) where
  unit := productOverlapUnit (A := A) B c
  normalization := productOverlapUnit_normalization (A := A) B c
  cocycle := productOverlapUnit_cocycle (A := A) B c

private noncomputable def componentGaugeUnit
    (u : (ProductAlgebra B)ˣ) (i : I) : (B i)ˣ :=
  (MulEquiv.piUnits u) i

omit [Fintype I] in
private theorem pairEval_includeLeft (u : ProductAlgebra B) (i j : I) :
    pairEval (A := A) B i j
        ((Algebra.TensorProduct.includeLeft :
          ProductAlgebra B →ₐ[A]
            (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) u) =
      (Algebra.TensorProduct.includeLeft : B i →ₐ[A] B i ⊗[A] B j) (u i) := by
  simp [pairEval]

omit [Fintype I] in
private theorem pairEval_includeRight (u : ProductAlgebra B) (i j : I) :
    pairEval (A := A) B i j
        ((Algebra.TensorProduct.includeRight :
          ProductAlgebra B →ₐ[A]
            (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) u) =
      (Algebra.TensorProduct.includeRight : B j →ₐ[A] B i ⊗[A] B j) (u j) := by
  simp [pairEval]

private theorem componentGaugeUnit_overlap
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (u : (ProductAlgebra B)ˣ)
    (hu : Units.map
          (Algebra.TensorProduct.includeLeft :
            ProductAlgebra B →ₐ[A]
              (ProductAlgebra B) ⊗[A] (ProductAlgebra B)).toMonoidHom u *
          (productMultiplicativeUnitCocycle (A := A) B c).unit =
        Units.map
          (Algebra.TensorProduct.includeRight :
            ProductAlgebra B →ₐ[A]
              (ProductAlgebra B) ⊗[A] (ProductAlgebra B)).toMonoidHom u)
    (i j : I) :
    Units.map (Algebra.TensorProduct.includeLeft :
        B i →ₐ[A] B i ⊗[A] B j).toMonoidHom (componentGaugeUnit B u i) *
        overlapUnit (A := A) B c i j =
      Units.map (Algebra.TensorProduct.includeRight :
        B j →ₐ[A] B i ⊗[A] B j).toMonoidHom (componentGaugeUnit B u j) := by
  apply Units.ext
  have huval := congrArg Units.val hu
  have hp := congrArg (pairEval (A := A) B i j) huval
  change pairEval (A := A) B i j
      ((Algebra.TensorProduct.includeLeft :
        ProductAlgebra B →ₐ[A]
          (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) (u : ProductAlgebra B) *
        (productOverlapUnit (A := A) B c :
          (ProductAlgebra B) ⊗[A] (ProductAlgebra B))) =
    pairEval (A := A) B i j
      ((Algebra.TensorProduct.includeRight :
        ProductAlgebra B →ₐ[A]
          (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) (u : ProductAlgebra B)) at hp
  rw [map_mul, pairEval_includeLeft, pairEval_includeRight] at hp
  have hpair := congrArg Units.val (productOverlapUnit_pairEval (A := A) B c i j)
  change pairEval (A := A) B i j (productOverlapUnit (A := A) B c :
      (ProductAlgebra B) ⊗[A] (ProductAlgebra B)) =
    (overlapUnit (A := A) B c i j : B i ⊗[A] B j) at hpair
  rw [hpair] at hp
  exact hp

private abbrev componentUnderlyingMap {i : I} {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) : T.left ⟶ Spec (.of (B i)) :=
  a.left

omit [Fintype I] in
private theorem componentPairCondition {i j : I} {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    componentUnderlyingMap (A := A) B a ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (B i))) =
      componentUnderlyingMap (A := A) B b ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (B j))) := by
  simpa [componentUnderlyingMap, componentFamily, testObject] using a.w.trans b.w.symm

private noncomputable def componentPairLiftUnderlying {i j : I}
    {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    T.left ⟶ Spec (.of (B i ⊗[A] B j)) :=
  pullback.lift (componentUnderlyingMap (A := A) B a)
      (componentUnderlyingMap (A := A) B b) (componentPairCondition (A := A) B a b) ≫
    (pullbackSpecIso A (B i) (B j)).hom

omit [Fintype I] in
private theorem componentPairLiftUnderlying_base {i j : I}
    {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    componentPairLiftUnderlying (A := A) B a b ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (B i ⊗[A] B j))) = T.hom := by
  rw [componentPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_base,
    ← Category.assoc, pullback.lift_fst]
  simpa [componentUnderlyingMap, componentFamily, testObject] using a.w

omit [Fintype I] in
private theorem componentPairLiftUnderlying_fst {i j : I}
    {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    componentPairLiftUnderlying (A := A) B a b ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      componentUnderlyingMap (A := A) B a := by
  rw [componentPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_fst,
    pullback.lift_fst]

omit [Fintype I] in
private theorem componentPairLiftUnderlying_snd {i j : I}
    {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    componentPairLiftUnderlying (A := A) B a b ≫
        Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight (R := A) (A := B i) (B := B j)) :
            B j →+* B i ⊗[A] B j)) =
      componentUnderlyingMap (A := A) B b := by
  rw [componentPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_snd,
    pullback.lift_snd]

private noncomputable def componentPairLift {i j : I} {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    T ⟶ testObject (R := A) (B i ⊗[A] B j) :=
  Over.homMk (componentPairLiftUnderlying (A := A) B a b)
    (componentPairLiftUnderlying_base (A := A) B a b)

omit [Fintype I] in
private theorem componentPairLift_pairLeft {i j : I} {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    componentPairLift (A := A) B a b ≫ pairLeft (A := A) B i j = a := by
  apply Over.OverMorphism.ext
  exact componentPairLiftUnderlying_fst (A := A) B a b

omit [Fintype I] in
private theorem componentPairLift_pairRight {i j : I} {T : Over (Spec (.of A))}
    (a : T ⟶ componentFamily B i) (b : T ⟶ componentFamily B j) :
    componentPairLift (A := A) B a b ≫ pairRight (A := A) B i j = b := by
  apply Over.OverMorphism.ext
  exact componentPairLiftUnderlying_snd (A := A) B a b

omit [Fintype I] in
/-- Over a principal ideal domain, every represented multiplicative cocycle on a finite affine
family whose product algebra is faithfully flat is an actual coboundary on that same family. -/
theorem finiteAffineFamilyMultiplicativeOneCocycle_isCohomologous_one
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A)) (componentFamily B))
    (hf : (algebraMap A (ProductAlgebra B)).FaithfullyFlat)
    [Finite I] [IsDomain A] [IsPrincipalIdealRing A] : c.IsCohomologous 1 := by
  letI : Fintype I := Fintype.ofFinite I
  letI : Nontrivial (ProductAlgebra B) := hf.injective.nontrivial
  obtain ⟨u, hu⟩ :=
    (productMultiplicativeUnitCocycle (A := A) B c).exists_coboundaryUnit hf
  let g : ∀ i, (multiplicativeScheme A).Point (componentFamily B i) :=
    fun i ↦ (multiplicativePointMulEquiv A (B i)).symm (componentGaugeUnit B u i)
  have hg (i : I) : multiplicativePointMulEquiv A (B i) (g i) =
      componentGaugeUnit B u i :=
    (multiplicativePointMulEquiv A (B i)).apply_symm_apply (componentGaugeUnit B u i)
  have hoverlap (i j : I) :
      (show (multiplicativeScheme A).Point
          (testObject (R := A) (B i ⊗[A] B j)) from
        pairLeft (A := A) B i j ≫ g i) *
          (show (multiplicativeScheme A).Point
              (testObject (R := A) (B i ⊗[A] B j)) from
            c.ev i j (pairLeft (A := A) B i j) (pairRight (A := A) B i j)) =
        (show (multiplicativeScheme A).Point
          (testObject (R := A) (B i ⊗[A] B j)) from
            pairRight (A := A) B i j ≫ g j) := by
    apply (multiplicativePointMulEquiv A (B i ⊗[A] B j)).injective
    rw [map_mul, pairLeft, pairRight,
      multiplicativePointMulEquiv_testObjectMap,
      multiplicativePointMulEquiv_testObjectMap, hg, hg]
    change Units.map _ (componentGaugeUnit B u i) *
        overlapUnit (A := A) B c i j =
      Units.map _ (componentGaugeUnit B u j)
    exact componentGaugeUnit_overlap (A := A) B c u hu i j
  refine ⟨g, ?_⟩
  intro i j T a b
  dsimp only [OneCocycle.one_toOneCochain, OneCochain.one_ev]
  rw [one_mul]
  let y : (multiplicativeScheme A).Point T := c.ev i j a b
  change (show (multiplicativeScheme A).Point T from a ≫ g i) * y =
    (show (multiplicativeScheme A).Point T from b ≫ g j)
  let q := componentPairLift (A := A) B a b
  have hq := congrArg (fun z ↦ q ≫ z) (hoverlap i j)
  have hc := c.ev_precomp i j q
    (pairLeft (A := A) B i j) (pairRight (A := A) B i j)
  rw [componentPairLift_pairLeft, componentPairLift_pairRight] at hc
  change q ≫ c.ev i j (pairLeft (A := A) B i j) (pairRight (A := A) B i j) = y at hc
  rw [MonObj.comp_mul] at hq
  change ((q ≫ pairLeft (A := A) B i j) ≫ g i) *
      (q ≫ c.ev i j (pairLeft (A := A) B i j) (pairRight (A := A) B i j)) =
    (q ≫ pairRight (A := A) B i j) ≫ g j at hq
  rw [show q = componentPairLift (A := A) B a b by rfl,
    componentPairLift_pairLeft, componentPairLift_pairRight, hc] at hq
  exact hq

/-- Represented fppf `H¹(G_m)` vanishes over every principal ideal domain.  An arbitrary fppf
cover is first refined by a finite affine family; the preceding theorem then effects its actual
Čech cocycle on that family. -/
theorem multiplicativeFppfHOne_pid_eq_one (A : Type u) [CommRing A]
    [IsDomain A] [IsPrincipalIdealRing A]
    (z : (multiplicativeScheme A).FppfHOne.{u}) : z = 1 := by
  letI : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  induction z using Quot.inductionOn with
  | _ representative =>
      rcases representative with ⟨𝒰, value⟩
      induction value using Quot.inductionOn with
      | _ c =>
          letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
            QuasiCompactCover.of_isOpenMap fun i ↦ by
              have hi := 𝒰.map_prop i
              letI : Flat (𝒰.f i) := hi.1
              letI : LocallyOfFinitePresentation (𝒰.f i) := hi.2
              exact (𝒰.f i).isOpenMap
          obtain ⟨𝒱, r, hfinite, _⟩ :=
            QuasiCompactCover.exists_hom 𝒰
          letI : Finite 𝒱.I₀ := hfinite
          letI : Fintype 𝒱.I₀ := Fintype.ofFinite 𝒱.I₀
          let B : 𝒱.I₀ → Type u := fun i ↦ 𝒱.X i
          letI : ∀ i, CommRing (B i) := fun i ↦ inferInstanceAs (CommRing (𝒱.X i))
          letI : ∀ i, Algebra A (B i) :=
            fun i ↦ (Spec.preimage (𝒱.f i)).hom.toAlgebra
          have hSpec (i : 𝒱.I₀) :
              Spec.map (CommRingCat.ofHom (algebraMap A (B i))) = 𝒱.f i := by
            change Spec.map (Spec.preimage (𝒱.f i)) = 𝒱.f i
            exact Spec.map_preimage (𝒱.f i)
          let 𝒲 : Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (.of A)) :=
            Scheme.Cover.mkOfCovers 𝒱.I₀ (fun i ↦ Spec (.of (B i)))
              (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap A (B i))))
              (fun x ↦ by
                obtain ⟨y, hy⟩ := 𝒱.covers x
                refine ⟨𝒱.idx x, y, ?_⟩
                rw [hSpec]
                exact hy)
              (fun i ↦ by
                rw [hSpec]
                exact 𝒱.map_prop i)
          let s : 𝒲.Hom 𝒰 :=
            { s₀ := r.s₀
              h₀ := r.h₀
              w₀ := fun (i : 𝒱.I₀) ↦ by
                change r.h₀ i ≫ 𝒰.f (r.s₀ i) =
                  Spec.map (CommRingCat.ofHom (algebraMap A (B i)))
                rw [hSpec]
                exact r.w₀ i }
          let c' := (Scheme.Cover.Hom.toOverFamilyRefinement s).pullbackOneCocycle c
          change OneCocycle (pointPresheaf (multiplicativeScheme A))
            (componentFamily B) at c'
          have hB :
              (componentPrecover B).presieve₀ ∈
                Scheme.fppfPrecoverage (Spec (.of A)) := by
            exact 𝒲.mem₀
          let fP : Spec (.of (ProductAlgebra B)) ⟶ Spec (.of A) :=
            Spec.map (CommRingCat.ofHom (algebraMap A (ProductAlgebra B)))
          have hfP := (productCover B hB).map_prop PUnit.unit
          letI : Flat fP := hfP.1
          letI : Surjective fP := ⟨fun x ↦ by
            obtain ⟨i, y, hy⟩ := (productCover B hB).exists_eq x
            exact ⟨y, hy⟩⟩
          have hf : (algebraMap A (ProductAlgebra B)).FaithfullyFlat := by
            exact (flat_and_surjective_SpecMap_iff
              (CommRingCat.ofHom (algebraMap A (ProductAlgebra B)))).mp
                ⟨inferInstance, inferInstance⟩
          have hc' : c'.class = 1 :=
            (finiteAffineFamilyMultiplicativeOneCocycle_isCohomologous_one B c' hf).class_eq
          calc
            Scheme.FppfHOne.mk 𝒰 c.class =
                Scheme.FppfHOne.mk 𝒲
                  (Scheme.Cover.Hom.pullbackHOne
                    (pointPresheaf (multiplicativeScheme A)) s c.class) :=
              (Scheme.FppfHOne.class_pullback 𝒰 𝒲 s c.class).symm
            _ = Scheme.FppfHOne.mk 𝒲 c'.class := rfl
            _ = Scheme.FppfHOne.mk 𝒲 1 := congrArg _ hc'
            _ = 1 := Scheme.FppfHOne.mk_one 𝒲

/-- The represented multiplicative fppf `H¹` of `Spec ℤ` has only its neutral class. -/
theorem multiplicativeFppfHOne_int_eq_one
    (z : (multiplicativeScheme ℤ).FppfHOne.{0}) : z = 1 :=
  multiplicativeFppfHOne_pid_eq_one ℤ z

/-- The represented multiplicative fppf `H¹` of `Spec ℤ` is a subsingleton. -/
instance multiplicativeFppfHOne_int_subsingleton :
    Subsingleton (multiplicativeScheme ℤ).FppfHOne.{0} :=
  ⟨fun x y ↦ (multiplicativeFppfHOne_int_eq_one x).trans
    (multiplicativeFppfHOne_int_eq_one y).symm⟩

/-- If ambient represented `H¹(G_m)` vanishes, checked Kummer exactness identifies the full
power-kernel `H¹` with units modulo powers. -/
noncomputable def powerKernelFppfHOneMulEquivUnitKummerClasses_of_multiplicative_subsingleton
    (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) (hn : n ≠ 0)
    [Subsingleton (multiplicativeScheme R).FppfHOne.{u}] :
    (powerKernel R n).FppfHOne.{u} ≃* UnitKummerClasses R n := by
  let f : (powerKernel R n).FppfHOne.{u} →*
      (fppfHOneMap (powerKernelPresentation R n).inclusion).ker :=
    (MonoidHom.id (powerKernel R n).FppfHOne.{u}).codRestrict
      (fppfHOneMap (powerKernelPresentation R n).inclusion).ker
      (fun z ↦ MonoidHom.mem_ker.mpr (Subsingleton.elim _ _))
  let e : (powerKernel R n).FppfHOne.{u} ≃*
      (fppfHOneMap (powerKernelPresentation R n).inclusion).ker :=
    MulEquiv.ofBijective f
      ⟨(fun _ _ h ↦ congrArg Subtype.val h),
        (fun z ↦ ⟨z.1, Subtype.ext rfl⟩)⟩
  exact e.trans (unitKummerBoundaryMulEquivKernel (R := R) n hn).symm

/-- For an odd exponent, every integral unit is already an actual power, so the integral unit
Kummer quotient is trivial. -/
theorem unitKummerClasses_int_eq_one_of_odd (n : ℕ) (hn : Odd n)
    (x : UnitKummerClasses ℤ n) : x = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom n : ℤˣ →* ℤˣ).range x
  apply (QuotientGroup.eq_one_iff u).mpr
  apply MonoidHom.mem_range.mpr
  refine ⟨u, ?_⟩
  change u ^ n = u
  rcases Int.units_eq_one_or u with hu | hu
  · rw [hu]
    simp
  · rw [hu]
    apply Units.ext
    change (-1 : ℤ) ^ n = -1
    exact hn.neg_one_pow

/-- The full represented fppf `H¹` of the integral power kernel is trivial for odd exponent. -/
theorem powerKernelFppfHOne_int_eq_one_of_odd (n : ℕ) (hn : Odd n)
    (z : (powerKernel ℤ n).FppfHOne.{0}) : z = 1 := by
  have hn0 : n ≠ 0 := fun h ↦ by subst n; simp at hn
  let e :=
    powerKernelFppfHOneMulEquivUnitKummerClasses_of_multiplicative_subsingleton
      ℤ n hn0
  apply e.injective
  rw [map_one]
  exact unitKummerClasses_int_eq_one_of_odd n hn (e z)

/-- The repository's actual integral `μₙ` model has trivial represented fppf `H¹` for every
odd exponent. -/
theorem muSchemeFppfHOne_int_eq_one_of_odd (n : ℕ) [NeZero n] (hn : Odd n)
    (z : (muScheme ℤ n).FppfHOne.{0}) : z = 1 := by
  let e : (muScheme ℤ n).FppfHOne.{0} ≃* (powerKernel ℤ n).FppfHOne.{0} :=
    CommGroupScheme.fppfHOneMulEquivOfIso (muSchemePowerKernelIso ℤ n)
  apply e.injective
  calc
    e z = 1 := powerKernelFppfHOne_int_eq_one_of_odd n hn (e z)
    _ = e 1 := (map_one e).symm

/-- Genuine five-primary integral `μ₅` fppf `H¹` vanishing endpoint. -/
theorem muSchemeFppfHOne_int_five_eq_one
    (z : (muScheme ℤ 5).FppfHOne.{0}) : z = 1 :=
  muSchemeFppfHOne_int_eq_one_of_odd 5 (by decide) z

/-- Genuine eleven-primary integral `μ₁₁` fppf `H¹` vanishing endpoint. -/
theorem muSchemeFppfHOne_int_eleven_eq_one
    (z : (muScheme ℤ 11).FppfHOne.{0}) : z = 1 :=
  muSchemeFppfHOne_int_eq_one_of_odd 11 (by decide) z

/-- Exact `p`-length zero data for integral `μₚ` when `p` is an odd prime. -/
noncomputable def muSchemeFppfHOne_int_odd_prime_certifiedData
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    FinitePGroup.CertifiedData p (muScheme ℤ p).FppfHOne.{0} := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Subsingleton (muScheme ℤ p).FppfHOne.{0} :=
    ⟨fun x y ↦ (muSchemeFppfHOne_int_eq_one_of_odd p hodd x).trans
      (muSchemeFppfHOne_int_eq_one_of_odd p hodd y).symm⟩
  letI : Finite (muScheme ℤ p).FppfHOne.{0} := Finite.of_subsingleton
  exact
    { finite := inferInstance
      length := 0
      card_eq := by
        rw [pow_zero]
        exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩ }

/-- Five-primary integral `μ₅` exact H¹ certificate, for use as an Euler-length-zero endpoint. -/
noncomputable def muSchemeFppfHOne_int_five_certifiedData :
    FinitePGroup.CertifiedData 5 (muScheme ℤ 5).FppfHOne.{0} :=
  muSchemeFppfHOne_int_odd_prime_certifiedData 5 (by decide) (by decide)

/-- Eleven-primary integral `μ₁₁` exact H¹ certificate, for use as an Euler-length-zero
endpoint. -/
noncomputable def muSchemeFppfHOne_int_eleven_certifiedData :
    FinitePGroup.CertifiedData 11 (muScheme ℤ 11).FppfHOne.{0} :=
  muSchemeFppfHOne_int_odd_prime_certifiedData 11 (by decide) (by decide)

@[simp]
theorem muSchemeFppfHOne_int_five_certifiedData_length :
    muSchemeFppfHOne_int_five_certifiedData.length = 0 :=
  rfl

@[simp]
theorem muSchemeFppfHOne_int_eleven_certifiedData_length :
    muSchemeFppfHOne_int_eleven_certifiedData.length = 0 :=
  rfl

end FiniteAffineFamilyEffectivity
end AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
