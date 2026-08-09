/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfHOne
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic

/-!
# Degree-one fppf Hilbert 90 for the additive group over a field

This file realizes the additive group `G_a` as an affine commutative group scheme and proves
that its represented degree-one fppf cohomology over a field is trivial.  On a singleton affine
chart `Spec B -> Spec K`, an additive cocycle is an element `c` of `B tensor_K B` satisfying

`c_12 + c_23 = c_13`.

A `K`-linear retraction `lambda : B -> K` of the structure map exists because `K` is a field.
Applying `lambda` to the first tensor factor gives

`b tensor 1 + c = 1 tensor b`,

which is the required explicit Cech gauge.  An arbitrary fppf cover of `Spec K` is then refined
by one nonempty affine chart, exactly as required by the global quotient definition of fppf
`H^1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite WithConv
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

namespace AffineCommGroupScheme

/-- The affine additive group with symmetric-algebra Hopf coordinates. -/
abbrev additive (R : Type u) [CommRing R] : AffineCommGroupScheme R :=
  Opposite.op
    ⟨CommHopfAlgCat.of R (SymmetricAlgebra R R), by
      change Coalgebra.IsCocomm R (SymmetricAlgebra R R)
      infer_instance⟩

/-- The additive group as an actual commutative group object over `Spec R`. -/
abbrev additiveScheme (R : Type u) [CommRing R] :
    CommGroupScheme (Spec (.of R)) :=
  (additive R).toCommGroupScheme

/-- Affine points of the geometric additive group are elements of the value algebra, written
multiplicatively to match the internal commutative-group API. -/
def additivePointMulEquiv (R : Type u) [CommRing R]
    (B : Type u) [CommRing B] [Algebra R B] :
    (additiveScheme R).Point (testObject (R := R) B) ≃* Multiplicative B :=
  ((additive R).pointMulEquiv B).trans
    (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := R) (A := B))

/-- Reading an additive-group point commutes with extension of its value algebra. -/
theorem additivePointMulEquiv_testObjectMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (x : (additive R).Point A) :
    additivePointMulEquiv R B (testObjectMap f ≫ x) =
      Multiplicative.ofAdd
        (f (Multiplicative.toAdd (additivePointMulEquiv R A x))) := by
  change TauCeti.AdditiveGroup.gaPointsMulEquiv
      ((additive R).pointMulEquiv B (testObjectMap f ≫ x)) =
    Multiplicative.ofAdd
      (f (Multiplicative.toAdd
        (TauCeti.AdditiveGroup.gaPointsMulEquiv ((additive R).pointMulEquiv A x))))
  rw [pointMulEquiv_apply, pointMulEquiv_apply, pointToAlgHom_testObjectMap]
  exact TauCeti.AdditiveGroup.gaPointsMulEquiv_mapValue f
    (toConv ((additive R).pointToAlgHom A x))

end AffineCommGroupScheme

namespace CommGroupScheme.AdditiveCocycleDescent

open AffineCommGroupScheme
open CategoryTheory.PresheafOfGroups

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]

/-! ## The standard singleton affine overlaps -/

/-- A represented additive-group cocycle on the singleton affine family `Spec B -> Spec K`. -/
abbrev RepresentedAdditiveOneCocycle :=
  OneCocycle (pointPresheaf (additiveScheme K))
    (fun _ : Unit ↦ testObject (R := K) B)

/-- The first projection from the affine pair overlap. -/
noncomputable def singletonPairLeft :
    testObject (R := K) (B ⊗[K] B) ⟶ testObject (R := K) B :=
  testObjectMap Algebra.TensorProduct.includeLeft

/-- The second projection from the affine pair overlap. -/
noncomputable def singletonPairRight :
    testObject (R := K) (B ⊗[K] B) ⟶ testObject (R := K) B :=
  testObjectMap Algebra.TensorProduct.includeRight

/-- The right-associated triple overlap algebra. -/
abbrev tripleRing := B ⊗[K] (B ⊗[K] B)

/-- Embed `B` as the first factor of the triple overlap. -/
noncomputable def firstToTriple : B →ₐ[K] tripleRing (K := K) (B := B) :=
  Algebra.TensorProduct.includeLeft

/-- Embed `B` as the second factor of the triple overlap. -/
noncomputable def secondToTriple : B →ₐ[K] tripleRing (K := K) (B := B) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft

/-- Embed `B` as the third factor of the triple overlap. -/
noncomputable def thirdToTriple : B →ₐ[K] tripleRing (K := K) (B := B) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight

/-- Pull a pair-overlap value to factors one and two. -/
noncomputable def pairTwelve : B ⊗[K] B →ₐ[K] tripleRing (K := K) (B := B) :=
  Algebra.TensorProduct.productMap firstToTriple secondToTriple

/-- Pull a pair-overlap value to factors two and three. -/
noncomputable def pairTwentyThree :
    B ⊗[K] B →ₐ[K] tripleRing (K := K) (B := B) :=
  Algebra.TensorProduct.includeRight

/-- Pull a pair-overlap value to factors one and three. -/
noncomputable def pairThirteen : B ⊗[K] B →ₐ[K] tripleRing (K := K) (B := B) :=
  Algebra.TensorProduct.productMap firstToTriple thirdToTriple

private noncomputable def singletonTripleFirst :
    testObject (R := K) (tripleRing (K := K) (B := B)) ⟶
      testObject (R := K) B :=
  testObjectMap (firstToTriple (K := K) (B := B))

private noncomputable def singletonTripleSecond :
    testObject (R := K) (tripleRing (K := K) (B := B)) ⟶
      testObject (R := K) B :=
  testObjectMap (secondToTriple (K := K) (B := B))

private noncomputable def singletonTripleThird :
    testObject (R := K) (tripleRing (K := K) (B := B)) ⟶
      testObject (R := K) B :=
  testObjectMap (thirdToTriple (K := K) (B := B))

private noncomputable def singletonPullTwelve :
    testObject (R := K) (tripleRing (K := K) (B := B)) ⟶
      testObject (R := K) (B ⊗[K] B) :=
  testObjectMap (pairTwelve (K := K) (B := B))

private noncomputable def singletonPullTwentyThree :
    testObject (R := K) (tripleRing (K := K) (B := B)) ⟶
      testObject (R := K) (B ⊗[K] B) :=
  testObjectMap (pairTwentyThree (K := K) (B := B))

private noncomputable def singletonPullThirteen :
    testObject (R := K) (tripleRing (K := K) (B := B)) ⟶
      testObject (R := K) (B ⊗[K] B) :=
  testObjectMap (pairThirteen (K := K) (B := B))

private theorem testObjectMap_comp
    {C D E : Type u} [CommRing C] [CommRing D] [CommRing E]
    [Algebra K C] [Algebra K D] [Algebra K E]
    (f : C →ₐ[K] D) (g : D →ₐ[K] E) :
    testObjectMap g ≫ testObjectMap f = testObjectMap (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  rfl

private theorem pairTwelve_comp_left :
    singletonPullTwelve (K := K) (B := B) ≫ singletonPairLeft =
      singletonTripleFirst := by
  rw [singletonPullTwelve, singletonPairLeft, singletonTripleFirst, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwelve, firstToTriple, secondToTriple]

private theorem pairTwelve_comp_right :
    singletonPullTwelve (K := K) (B := B) ≫ singletonPairRight =
      singletonTripleSecond := by
  rw [singletonPullTwelve, singletonPairRight, singletonTripleSecond, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwelve, firstToTriple, secondToTriple]

private theorem pairTwentyThree_comp_left :
    singletonPullTwentyThree (K := K) (B := B) ≫ singletonPairLeft =
      singletonTripleSecond := by
  rw [singletonPullTwentyThree, singletonPairLeft, singletonTripleSecond,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwentyThree, secondToTriple]

private theorem pairTwentyThree_comp_right :
    singletonPullTwentyThree (K := K) (B := B) ≫ singletonPairRight =
      singletonTripleThird := by
  rw [singletonPullTwentyThree, singletonPairRight, singletonTripleThird,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwentyThree, thirdToTriple]

private theorem pairThirteen_comp_left :
    singletonPullThirteen (K := K) (B := B) ≫ singletonPairLeft =
      singletonTripleFirst := by
  rw [singletonPullThirteen, singletonPairLeft, singletonTripleFirst, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairThirteen, firstToTriple, thirdToTriple]

private theorem pairThirteen_comp_right :
    singletonPullThirteen (K := K) (B := B) ≫ singletonPairRight =
      singletonTripleThird := by
  rw [singletonPullThirteen, singletonPairRight, singletonTripleThird, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairThirteen, firstToTriple, thirdToTriple]

/-- The value of a represented singleton cocycle on the standard pair overlap. -/
noncomputable def representedOverlapValue
    (c : RepresentedAdditiveOneCocycle (K := K) (B := B)) : B ⊗[K] B :=
  Multiplicative.toAdd
    (additivePointMulEquiv K (B ⊗[K] B)
      (c.ev () () singletonPairLeft singletonPairRight))

private theorem representedOverlapValue_twelve
    (c : RepresentedAdditiveOneCocycle (K := K) (B := B)) :
    Multiplicative.ofAdd
        (pairTwelve (K := K) (B := B) (representedOverlapValue c)) =
      additivePointMulEquiv K (tripleRing (K := K) (B := B))
        (c.ev () () singletonTripleFirst singletonTripleSecond) := by
  let x : (additive K).Point (B ⊗[K] B) :=
    c.ev () () singletonPairLeft singletonPairRight
  have hnat := additivePointMulEquiv_testObjectMap
    (R := K) (f := pairTwelve (K := K) (B := B)) (x := x)
  change Multiplicative.ofAdd
      (pairTwelve (K := K) (B := B)
        (Multiplicative.toAdd (additivePointMulEquiv K (B ⊗[K] B) x))) = _
  rw [← hnat]
  have h := c.ev_precomp () () singletonPullTwelve
    (singletonPairLeft (K := K) (B := B))
    (singletonPairRight (K := K) (B := B))
  rw [pairTwelve_comp_left, pairTwelve_comp_right] at h
  change singletonPullTwelve (K := K) (B := B) ≫ x =
    c.ev () () singletonTripleFirst singletonTripleSecond at h
  dsimp only [singletonPullTwelve] at h
  exact congrArg (additivePointMulEquiv K (tripleRing (K := K) (B := B))) h

private theorem representedOverlapValue_twentyThree
    (c : RepresentedAdditiveOneCocycle (K := K) (B := B)) :
    Multiplicative.ofAdd
        (pairTwentyThree (K := K) (B := B) (representedOverlapValue c)) =
      additivePointMulEquiv K (tripleRing (K := K) (B := B))
        (c.ev () () singletonTripleSecond singletonTripleThird) := by
  let x : (additive K).Point (B ⊗[K] B) :=
    c.ev () () singletonPairLeft singletonPairRight
  have hnat := additivePointMulEquiv_testObjectMap
    (R := K) (f := pairTwentyThree (K := K) (B := B)) (x := x)
  change Multiplicative.ofAdd
      (pairTwentyThree (K := K) (B := B)
        (Multiplicative.toAdd (additivePointMulEquiv K (B ⊗[K] B) x))) = _
  rw [← hnat]
  have h := c.ev_precomp () () singletonPullTwentyThree
    (singletonPairLeft (K := K) (B := B))
    (singletonPairRight (K := K) (B := B))
  rw [pairTwentyThree_comp_left, pairTwentyThree_comp_right] at h
  change singletonPullTwentyThree (K := K) (B := B) ≫ x =
    c.ev () () singletonTripleSecond singletonTripleThird at h
  dsimp only [singletonPullTwentyThree] at h
  exact congrArg (additivePointMulEquiv K (tripleRing (K := K) (B := B))) h

private theorem representedOverlapValue_thirteen
    (c : RepresentedAdditiveOneCocycle (K := K) (B := B)) :
    Multiplicative.ofAdd
        (pairThirteen (K := K) (B := B) (representedOverlapValue c)) =
      additivePointMulEquiv K (tripleRing (K := K) (B := B))
        (c.ev () () singletonTripleFirst singletonTripleThird) := by
  let x : (additive K).Point (B ⊗[K] B) :=
    c.ev () () singletonPairLeft singletonPairRight
  have hnat := additivePointMulEquiv_testObjectMap
    (R := K) (f := pairThirteen (K := K) (B := B)) (x := x)
  change Multiplicative.ofAdd
      (pairThirteen (K := K) (B := B)
        (Multiplicative.toAdd (additivePointMulEquiv K (B ⊗[K] B) x))) = _
  rw [← hnat]
  have h := c.ev_precomp () () singletonPullThirteen
    (singletonPairLeft (K := K) (B := B))
    (singletonPairRight (K := K) (B := B))
  rw [pairThirteen_comp_left, pairThirteen_comp_right] at h
  change singletonPullThirteen (K := K) (B := B) ≫ x =
    c.ev () () singletonTripleFirst singletonTripleThird at h
  dsimp only [singletonPullThirteen] at h
  exact congrArg (additivePointMulEquiv K (tripleRing (K := K) (B := B))) h

/-- The standard overlap value satisfies the additive cocycle identity in the triple tensor
product. -/
theorem representedOverlapValue_cocycle
    (c : RepresentedAdditiveOneCocycle (K := K) (B := B)) :
    pairTwelve (K := K) (B := B) (representedOverlapValue c) +
        pairTwentyThree (K := K) (B := B) (representedOverlapValue c) =
      pairThirteen (K := K) (B := B) (representedOverlapValue c) := by
  let x12 : (additive K).Point (tripleRing (K := K) (B := B)) :=
    c.ev () () singletonTripleFirst singletonTripleSecond
  let x23 : (additive K).Point (tripleRing (K := K) (B := B)) :=
    c.ev () () singletonTripleSecond singletonTripleThird
  let x13 : (additive K).Point (tripleRing (K := K) (B := B)) :=
    c.ev () () singletonTripleFirst singletonTripleThird
  apply Multiplicative.ofAdd.injective
  rw [ofAdd_add, representedOverlapValue_twelve, representedOverlapValue_twentyThree,
    representedOverlapValue_thirteen]
  change additivePointMulEquiv K (tripleRing (K := K) (B := B)) x12 *
      additivePointMulEquiv K (tripleRing (K := K) (B := B)) x23 =
    additivePointMulEquiv K (tripleRing (K := K) (B := B)) x13
  rw [← map_mul]
  have h := c.ev_trans () () ()
    (singletonTripleFirst (K := K) (B := B))
    (singletonTripleSecond (K := K) (B := B))
    (singletonTripleThird (K := K) (B := B))
  change x12 * x23 = x13 at h
  exact congrArg (additivePointMulEquiv K (tripleRing (K := K) (B := B))) h

/-! ## Linear contraction of the cocycle identity -/

private noncomputable def contractPair (lambda : B →ₗ[K] K) :
    B ⊗[K] B →ₗ[K] B :=
  (Algebra.TensorProduct.lid K B).toLinearMap.comp
    (TensorProduct.map lambda LinearMap.id)

private noncomputable def contractTriple (lambda : B →ₗ[K] K) :
    tripleRing (K := K) (B := B) →ₗ[K] B ⊗[K] B :=
  (Algebra.TensorProduct.lid K (B ⊗[K] B)).toLinearMap.comp
    (TensorProduct.map lambda LinearMap.id)

@[simp]
private theorem contractPair_tmul (lambda : B →ₗ[K] K) (x y : B) :
    contractPair lambda (x ⊗ₜ[K] y) = lambda x • y := by
  simp [contractPair]

@[simp]
private theorem contractTriple_tmul (lambda : B →ₗ[K] K)
    (x : B) (y : B ⊗[K] B) :
    contractTriple lambda (x ⊗ₜ[K] y) = lambda x • y := by
  simp [contractTriple]

@[simp]
private theorem pairTwelve_tmul (x y : B) :
    pairTwelve (K := K) (B := B) (x ⊗ₜ[K] y) =
      x ⊗ₜ[K] (y ⊗ₜ[K] (1 : B)) := by
  simp [pairTwelve, firstToTriple, secondToTriple]

@[simp]
private theorem pairTwentyThree_apply (z : B ⊗[K] B) :
    pairTwentyThree (K := K) (B := B) z = (1 : B) ⊗ₜ[K] z := by
  exact Algebra.TensorProduct.includeRight_apply z

@[simp]
private theorem pairThirteen_tmul (x y : B) :
    pairThirteen (K := K) (B := B) (x ⊗ₜ[K] y) =
      x ⊗ₜ[K] ((1 : B) ⊗ₜ[K] y) := by
  simp [pairThirteen, firstToTriple, thirdToTriple]

private theorem contractTriple_pairTwelve (lambda : B →ₗ[K] K)
    (z : B ⊗[K] B) :
    contractTriple lambda (pairTwelve (K := K) (B := B) z) =
      (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B)
        (contractPair lambda z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [pairTwelve_tmul, contractTriple_tmul, contractPair_tmul,
        Algebra.TensorProduct.includeLeft_apply]
      rw [TensorProduct.smul_tmul']

private theorem contractTriple_pairTwentyThree
    (lambda : B →ₗ[K] K) (hlambda : lambda 1 = 1)
    (z : B ⊗[K] B) :
    contractTriple lambda (pairTwentyThree (K := K) (B := B) z) = z := by
  rw [pairTwentyThree_apply, contractTriple_tmul, hlambda, one_smul]

private theorem contractTriple_pairThirteen (lambda : B →ₗ[K] K)
    (z : B ⊗[K] B) :
    contractTriple lambda (pairThirteen (K := K) (B := B) z) =
      (Algebra.TensorProduct.includeRight : B →ₐ[K] B ⊗[K] B)
        (contractPair lambda z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [pairThirteen_tmul, contractTriple_tmul, contractPair_tmul,
        Algebra.TensorProduct.includeRight_apply]
      rw [TensorProduct.tmul_smul]

private noncomputable def algebraRetraction (K B : Type u)
    [Field K] [CommRing B] [Algebra K B] [Nontrivial B] : B →ₗ[K] K :=
  (Algebra.linearMap K B).leftInverse

private theorem algebraRetraction_algebraMap (K B : Type u)
    [Field K] [CommRing B] [Algebra K B] [Nontrivial B] (r : K) :
    algebraRetraction K B (algebraMap K B r) = r := by
  have hinj : LinearMap.ker (Algebra.linearMap K B) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective K B)
  exact LinearMap.leftInverse_apply_of_inj hinj r

private theorem algebraRetraction_one (K B : Type u)
    [Field K] [CommRing B] [Algebra K B] [Nontrivial B] :
    algebraRetraction K B 1 = 1 := by
  simpa using algebraRetraction_algebraMap K B 1

/-- The additive singleton cocycle identity has an explicit coboundary gauge. -/
theorem representedOverlapValue_exists_gauge
    [Nontrivial B]
    (c : RepresentedAdditiveOneCocycle (K := K) (B := B)) :
    ∃ b : B,
      (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B) b +
          representedOverlapValue c =
        (Algebra.TensorProduct.includeRight : B →ₐ[K] B ⊗[K] B) b := by
  let lambda : B →ₗ[K] K := algebraRetraction K B
  let b : B := contractPair lambda (representedOverlapValue c)
  have h := congrArg (contractTriple lambda) (representedOverlapValue_cocycle c)
  rw [map_add, contractTriple_pairTwelve,
    contractTriple_pairTwentyThree lambda (algebraRetraction_one K B),
    contractTriple_pairThirteen] at h
  exact ⟨b, h⟩

/-! ## From the tensor gauge to a represented Cech gauge -/

private abbrev singletonUnderlyingMap {T : Over (Spec (.of K))}
    (a : T ⟶ testObject (R := K) B) : T.left ⟶ Spec (.of B) :=
  a.left

private theorem singletonPairCondition {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) :
    singletonUnderlyingMap a ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      singletonUnderlyingMap b ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  simpa [singletonUnderlyingMap, testObject] using a.w.trans b.w.symm

private noncomputable def singletonPairLiftUnderlying {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) : T.left ⟶ Spec (.of (B ⊗[K] B)) :=
  pullback.lift (singletonUnderlyingMap a) (singletonUnderlyingMap b)
      (singletonPairCondition a b) ≫
    (pullbackSpecIso K B B).hom

private theorem singletonPairLiftUnderlying_base {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) :
    singletonPairLiftUnderlying a b ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (B ⊗[K] B))) = T.hom := by
  rw [singletonPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_base,
    ← Category.assoc, pullback.lift_fst]
  simpa [singletonUnderlyingMap, testObject] using a.w

private theorem singletonPairLiftUnderlying_fst {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) :
    singletonPairLiftUnderlying a b ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      singletonUnderlyingMap a := by
  rw [singletonPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_fst,
    pullback.lift_fst]

private theorem singletonPairLiftUnderlying_snd {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) :
    singletonPairLiftUnderlying a b ≫
        Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight (R := K) (A := B) (B := B)) :
            B →+* B ⊗[K] B)) =
      singletonUnderlyingMap b := by
  rw [singletonPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_snd,
    pullback.lift_snd]

private noncomputable def singletonPairLift {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) :
    T ⟶ testObject (R := K) (B ⊗[K] B) :=
  Over.homMk (singletonPairLiftUnderlying a b)
    (singletonPairLiftUnderlying_base a b)

private theorem singletonPairLift_pairLeft {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) :
    singletonPairLift a b ≫ singletonPairLeft = a := by
  apply Over.OverMorphism.ext
  exact singletonPairLiftUnderlying_fst a b

private theorem singletonPairLift_pairRight {T : Over (Spec (.of K))}
    (a b : T ⟶ testObject (R := K) B) :
    singletonPairLift a b ≫ singletonPairRight = b := by
  apply Over.OverMorphism.ext
  exact singletonPairLiftUnderlying_snd a b

/-- Every represented additive cocycle on a singleton affine family over a field is an actual
coboundary. -/
theorem representedAdditiveOneCocycle_isCohomologous_one
    [Nontrivial B]
    (c : RepresentedAdditiveOneCocycle (K := K) (B := B)) :
    c.IsCohomologous 1 := by
  obtain ⟨b, hb⟩ := representedOverlapValue_exists_gauge c
  let g : (additiveScheme K).Point (testObject (R := K) B) :=
    (additivePointMulEquiv K B).symm (Multiplicative.ofAdd b)
  let x : (additiveScheme K).Point (testObject (R := K) (B ⊗[K] B)) :=
    c.ev () () singletonPairLeft singletonPairRight
  have hg : additivePointMulEquiv K B g = Multiplicative.ofAdd b :=
    (additivePointMulEquiv K B).apply_symm_apply (Multiplicative.ofAdd b)
  have hx : Multiplicative.toAdd (additivePointMulEquiv K (B ⊗[K] B) x) =
      representedOverlapValue c := rfl
  have hoverlap :
      singletonPairLeft (K := K) (B := B) ≫ g * x =
        singletonPairRight (K := K) (B := B) ≫ g := by
    apply (additivePointMulEquiv K (B ⊗[K] B)).injective
    rw [map_mul, singletonPairLeft, singletonPairRight,
      additivePointMulEquiv_testObjectMap,
      additivePointMulEquiv_testObjectMap, hg]
    apply Multiplicative.toAdd.injective
    simpa only [toAdd_mul, toAdd_ofAdd, hx] using hb
  refine ⟨fun _ ↦ g, ?_⟩
  rintro ⟨⟩ ⟨⟩ T a b'
  dsimp only [OneCocycle.one_toOneCochain, OneCochain.one_ev]
  rw [one_mul]
  let y : (additiveScheme K).Point T := c.ev () () a b'
  change (a ≫ g) * y = b' ≫ g
  let q := singletonPairLift a b'
  have hq := congrArg (fun z ↦ q ≫ z) hoverlap
  have hc := c.ev_precomp () () q
    (singletonPairLeft (K := K) (B := B))
    (singletonPairRight (K := K) (B := B))
  rw [singletonPairLift_pairLeft, singletonPairLift_pairRight] at hc
  change q ≫ x = y at hc
  rw [MonObj.comp_mul] at hq
  change ((q ≫ singletonPairLeft) ≫ g) * (q ≫ x) =
    (q ≫ singletonPairRight) ≫ g at hq
  rw [show q = singletonPairLift a b' by rfl, singletonPairLift_pairLeft,
    singletonPairLift_pairRight, hc] at hq
  exact hq

/-- The singleton calculation is unchanged for any nonempty subsingleton index type. -/
theorem constantRepresentedAdditiveOneCocycle_isCohomologous_one
    {I : Type u} [Nonempty I] [Subsingleton I] [Nontrivial B]
    (c : OneCocycle (pointPresheaf (additiveScheme K))
      (fun _ : I ↦ testObject (R := K) B)) :
    c.IsCohomologous 1 := by
  letI : Inhabited I := Classical.inhabited_of_nonempty ‹Nonempty I›
  let r : FamilyRefinement (fun _ : Unit ↦ testObject (R := K) B)
      (fun _ : I ↦ testObject (R := K) B) :=
    { index := fun _ ↦ default
      map := fun _ ↦ 𝟙 _ }
  let c₀ := r.pullbackOneCocycle c
  change RepresentedAdditiveOneCocycle (K := K) (B := B) at c₀
  have hc₀ := representedAdditiveOneCocycle_isCohomologous_one c₀
  let s : FamilyRefinement (fun _ : I ↦ testObject (R := K) B)
      (fun _ : Unit ↦ testObject (R := K) B) :=
    { index := fun _ ↦ ()
      map := fun _ ↦ 𝟙 _ }
  have hs := s.pullback_isCohomologous hc₀
  have heq : s.pullbackOneCocycle c₀ = c := by
    apply FamilyRefinement.oneCocycle_ext
    apply OneCochain.ext
    funext i j T a b
    have hi : i = default := Subsingleton.elim _ _
    have hj : j = default := Subsingleton.elim _ _
    subst i
    subst j
    simp only [c₀, r, s, FamilyRefinement.pullbackOneCocycle,
      FamilyRefinement.pullbackOneCochain, Category.comp_id]
  rw [heq, FamilyRefinement.pullbackOneCocycle_one] at hs
  exact hs

/-! ## Arbitrary fppf covers -/

/-- Degree-one fppf Hilbert 90 for the represented additive group over a field. -/
theorem additiveFppfHOne_eq_one (K : Type u) [Field K]
    (z : (additiveScheme K).FppfHOne.{u}) : z = 1 := by
  letI : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  induction z using Quot.inductionOn with
  | _ representative =>
      rcases representative with ⟨𝒰, value⟩
      induction value using Quot.inductionOn with
      | _ c =>
          let x₀ : Spec (.of K) := default
          let i : 𝒰.I₀ := 𝒰.idx x₀
          have hi : x₀ ∈ Set.range (𝒰.f i) := 𝒰.covers x₀
          obtain ⟨y, hy⟩ := hi
          let j := (𝒰.X i).affineCover.idx y
          have hj : y ∈ Set.range ((𝒰.X i).affineCover.f j) :=
            (𝒰.X i).affineCover.covers y
          obtain ⟨w, hw⟩ := hj
          let U := (𝒰.X i).affineCover.X j
          let B := Γ(U, ⊤)
          let e : U ≅ Spec (.of B) := U.isoSpec
          let s : Spec (.of B) ⟶ 𝒰.X i := e.inv ≫ (𝒰.X i).affineCover.f j
          let h : Spec (.of B) ⟶ Spec (.of K) := s ≫ 𝒰.f i
          letI : Algebra K B := (Spec.preimage h).hom.toAlgebra
          have hSpec :
              Spec.map (CommRingCat.ofHom (algebraMap K B)) = h := by
            change Spec.map (Spec.preimage h) = h
            exact Spec.map_preimage h
          let wB : Spec (.of B) := e.hom w
          letI : Nonempty (Spec (.of B)) := ⟨wB⟩
          have hBnonempty : Nonempty (PrimeSpectrum B) := ⟨wB⟩
          letI : Nontrivial B :=
            PrimeSpectrum.nonempty_iff_nontrivial.mp hBnonempty
          have h𝒰 := 𝒰.map_prop i
          letI : Flat (𝒰.f i) := h𝒰.1
          letI : LocallyOfFinitePresentation (𝒰.f i) := h𝒰.2
          letI : Flat s := inferInstance
          letI : LocallyOfFinitePresentation s := inferInstance
          letI : Flat h := inferInstance
          letI : LocallyOfFinitePresentation h := inferInstance
          letI : Surjective h := inferInstance
          let f : Spec (.of B) ⟶ Spec (.of K) :=
            Spec.map (CommRingCat.ofHom (algebraMap K B))
          letI : Flat f := by
            dsimp only [f]
            rw [hSpec]
            infer_instance
          letI : LocallyOfFinitePresentation f := by
            dsimp only [f]
            rw [hSpec]
            infer_instance
          letI : Surjective f := by
            dsimp only [f]
            rw [hSpec]
            infer_instance
          let 𝒱 : Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (.of K)) :=
            Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ ↦ Spec (.of B)) (fun _ ↦ f)
              (fun x ↦ ⟨PUnit.unit, wB, Subsingleton.elim _ _⟩)
              (fun _ ↦ ⟨inferInstance, inferInstance⟩)
          let r : 𝒱.Hom 𝒰 :=
            { s₀ := fun _ ↦ i
              h₀ := fun _ ↦ s
              w₀ := fun _ ↦ by
                change s ≫ 𝒰.f i = f
                exact hSpec.symm }
          let c' := (Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle c
          change OneCocycle (pointPresheaf (additiveScheme K))
            (fun _ : PUnit.{u + 1} ↦ testObject (R := K) B) at c'
          have hc' : c'.class = 1 :=
            (constantRepresentedAdditiveOneCocycle_isCohomologous_one c').class_eq
          calc
            Scheme.FppfHOne.mk 𝒰 c.class =
                Scheme.FppfHOne.mk 𝒱
                  (Scheme.Cover.Hom.pullbackHOne
                    (pointPresheaf (additiveScheme K)) r c.class) :=
              (Scheme.FppfHOne.class_pullback 𝒰 𝒱 r c.class).symm
            _ = Scheme.FppfHOne.mk 𝒱 c'.class := rfl
            _ = Scheme.FppfHOne.mk 𝒱 1 := congrArg _ hc'
            _ = 1 := Scheme.FppfHOne.mk_one 𝒱

/-- The represented additive fppf `H^1` over a field has exactly one class. -/
instance additiveFppfHOne_subsingleton (K : Type u) [Field K] :
    Subsingleton (additiveScheme K).FppfHOne.{u} :=
  ⟨fun x y ↦ (additiveFppfHOne_eq_one K x).trans
    (additiveFppfHOne_eq_one K y).symm⟩

end CommGroupScheme.AdditiveCocycleDescent

end AlgebraicGeometry
