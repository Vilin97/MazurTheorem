import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeCocycleDescent

open CategoryTheory ModuleCat TensorProduct
open AlgebraicGeometry
open AlgebraicGeometry.AffineCommGroupScheme
open AlgebraicGeometry.CommGroupScheme
open AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
open CategoryTheory.PresheafOfGroups

universe u

noncomputable section

namespace ScratchRepresentedMultiplicativeCocycle

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

abbrev RepresentedOneCocycle :=
  OneCocycle
    (pointPresheaf (multiplicativeScheme A))
    (fun _ : Unit ↦ testObject (R := A) B)

noncomputable def pairLeft :
    testObject (R := A) (B ⊗[A] B) ⟶ testObject (R := A) B :=
  testObjectMap (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)

noncomputable def pairRight :
    testObject (R := A) (B ⊗[A] B) ⟶ testObject (R := A) B :=
  testObjectMap (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)

noncomputable def overlapUnit (c : RepresentedOneCocycle (A := A) (B := B)) :
    (B ⊗[A] B)ˣ :=
  multiplicativePointMulEquiv A (B ⊗[A] B)
    (c.ev () () pairLeft pairRight)

theorem testObjectMap_comp
    {C D E : Type u} [CommRing C] [CommRing D] [CommRing E]
    [Algebra A C] [Algebra A D] [Algebra A E]
    (f : C →ₐ[A] D) (g : D →ₐ[A] E) :
    testObjectMap g ≫ testObjectMap f = testObjectMap (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  rfl

noncomputable def diagonal :
    testObject (R := A) B ⟶ testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (Algebra.TensorProduct.lmul' A)

theorem diagonal_pairLeft :
    diagonal (A := A) (B := B) ≫ pairLeft = 𝟙 _ := by
  rw [diagonal, pairLeft, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id, Spec.map_inj]
  ext b
  simp

theorem diagonal_pairRight :
    diagonal (A := A) (B := B) ≫ pairRight = 𝟙 _ := by
  rw [diagonal, pairRight, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id, Spec.map_inj]
  ext b
  simp

theorem overlapUnit_normalization
    (c : RepresentedOneCocycle (A := A) (B := B)) :
    Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom (overlapUnit c) = 1 := by
  letI : CommGroup ((multiplicative A).Point B) :=
    AffineCommGroupScheme.pointCommGroup (multiplicative A) B
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (pairLeft (A := A) (B := B))
      (pairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := Algebra.TensorProduct.lmul' A)
    (x := x)
  change Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = 1
  rw [← hnat]
  have hpre := c.ev_precomp () () (diagonal (A := A) (B := B))
    (pairLeft (A := A) (B := B)) (pairRight (A := A) (B := B))
  change diagonal (A := A) (B := B) ≫
      c.ev () () (pairLeft (A := A) (B := B)) (pairRight (A := A) (B := B)) =
    c.ev () ()
      (diagonal (A := A) (B := B) ≫ pairLeft (A := A) (B := B))
      (diagonal (A := A) (B := B) ≫ pairRight (A := A) (B := B)) at hpre
  rw [diagonal_pairLeft, diagonal_pairRight] at hpre
  dsimp only [diagonal] at hpre
  have hrefl := OneCocycle.ev_refl
    (pointPresheaf (multiplicativeScheme A))
    (fun _ : Unit ↦ testObject (R := A) B) c ()
    (𝟙 (testObject (R := A) B))
  change c.ev () () (𝟙 _) (𝟙 _) = (1 : (multiplicative A).Point B) at hrefl
  change testObjectMap (Algebra.TensorProduct.lmul' A) ≫ x =
      c.ev () () (𝟙 _) (𝟙 _) at hpre
  rw [hpre, hrefl]
  exact map_one (multiplicativePointMulEquiv A B)

noncomputable def tripleFirst :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) B :=
  testObjectMap (firstToTriple (A := A) (B := B))

noncomputable def tripleSecond :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) B :=
  testObjectMap (secondToTriple (A := A) (B := B))

noncomputable def tripleThird :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) B :=
  testObjectMap (thirdToTriple (A := A) (B := B))

noncomputable def pullTwelve :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (pairTwelve (A := A) (B := B))

noncomputable def pullTwentyThree :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (pairTwentyThree (A := A) (B := B))

noncomputable def pullThirteen :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (pairThirteen (A := A) (B := B))

theorem pullTwelve_pairLeft :
    pullTwelve (A := A) (B := B) ≫ pairLeft = tripleFirst := by
  rw [pullTwelve, pairLeft, tripleFirst, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwelve, firstToTriple, secondToTriple]

theorem pullTwelve_pairRight :
    pullTwelve (A := A) (B := B) ≫ pairRight = tripleSecond := by
  rw [pullTwelve, pairRight, tripleSecond, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwelve, firstToTriple, secondToTriple]

theorem pullTwentyThree_pairLeft :
    pullTwentyThree (A := A) (B := B) ≫ pairLeft = tripleSecond := by
  rw [pullTwentyThree, pairLeft, tripleSecond, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwentyThree, secondToTriple]

theorem pullTwentyThree_pairRight :
    pullTwentyThree (A := A) (B := B) ≫ pairRight = tripleThird := by
  rw [pullTwentyThree, pairRight, tripleThird, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwentyThree, thirdToTriple]

theorem pullThirteen_pairLeft :
    pullThirteen (A := A) (B := B) ≫ pairLeft = tripleFirst := by
  rw [pullThirteen, pairLeft, tripleFirst, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairThirteen, firstToTriple, thirdToTriple]

theorem pullThirteen_pairRight :
    pullThirteen (A := A) (B := B) ≫ pairRight = tripleThird := by
  rw [pullThirteen, pairRight, tripleThird, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairThirteen, firstToTriple, thirdToTriple]

theorem overlapUnit_pairTwelve
    (c : RepresentedOneCocycle (A := A) (B := B)) :
    Units.map (pairTwelve (A := A) (B := B)).toMonoidHom (overlapUnit c) =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))
        (c.ev () () (tripleFirst (A := A) (B := B))
          (tripleSecond (A := A) (B := B))) := by
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (pairLeft (A := A) (B := B))
      (pairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pairTwelve (A := A) (B := B)) (x := x)
  change Units.map (pairTwelve (A := A) (B := B)).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp () () (pullTwelve (A := A) (B := B))
    (pairLeft (A := A) (B := B)) (pairRight (A := A) (B := B))
  change pullTwelve (A := A) (B := B) ≫ x =
    c.ev () ()
      (pullTwelve (A := A) (B := B) ≫ pairLeft (A := A) (B := B))
      (pullTwelve (A := A) (B := B) ≫ pairRight (A := A) (B := B)) at hpre
  rw [pullTwelve_pairLeft, pullTwelve_pairRight] at hpre
  dsimp only [pullTwelve] at hpre
  exact congrArg (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))) hpre

theorem overlapUnit_pairTwentyThree
    (c : RepresentedOneCocycle (A := A) (B := B)) :
    Units.map (pairTwentyThree (A := A) (B := B)).toMonoidHom (overlapUnit c) =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))
        (c.ev () () (tripleSecond (A := A) (B := B))
          (tripleThird (A := A) (B := B))) := by
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (pairLeft (A := A) (B := B))
      (pairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pairTwentyThree (A := A) (B := B)) (x := x)
  change Units.map (pairTwentyThree (A := A) (B := B)).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp () () (pullTwentyThree (A := A) (B := B))
    (pairLeft (A := A) (B := B)) (pairRight (A := A) (B := B))
  change pullTwentyThree (A := A) (B := B) ≫ x =
    c.ev () ()
      (pullTwentyThree (A := A) (B := B) ≫ pairLeft (A := A) (B := B))
      (pullTwentyThree (A := A) (B := B) ≫ pairRight (A := A) (B := B)) at hpre
  rw [pullTwentyThree_pairLeft, pullTwentyThree_pairRight] at hpre
  dsimp only [pullTwentyThree] at hpre
  exact congrArg (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))) hpre

theorem overlapUnit_pairThirteen
    (c : RepresentedOneCocycle (A := A) (B := B)) :
    Units.map (pairThirteen (A := A) (B := B)).toMonoidHom (overlapUnit c) =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))
        (c.ev () () (tripleFirst (A := A) (B := B))
          (tripleThird (A := A) (B := B))) := by
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (pairLeft (A := A) (B := B))
      (pairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pairThirteen (A := A) (B := B)) (x := x)
  change Units.map (pairThirteen (A := A) (B := B)).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp () () (pullThirteen (A := A) (B := B))
    (pairLeft (A := A) (B := B)) (pairRight (A := A) (B := B))
  change pullThirteen (A := A) (B := B) ≫ x =
    c.ev () ()
      (pullThirteen (A := A) (B := B) ≫ pairLeft (A := A) (B := B))
      (pullThirteen (A := A) (B := B) ≫ pairRight (A := A) (B := B)) at hpre
  rw [pullThirteen_pairLeft, pullThirteen_pairRight] at hpre
  dsimp only [pullThirteen] at hpre
  exact congrArg (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))) hpre

noncomputable def toMultiplicativeUnitCocycle
    (c : RepresentedOneCocycle (A := A) (B := B)) :
    MultiplicativeUnitCocycle (A := A) (B := B) where
  unit := overlapUnit c
  normalization := overlapUnit_normalization c
  cocycle := by
    letI : CommGroup ((multiplicative A).Point (tripleRing (A := A) (B := B))) :=
      AffineCommGroupScheme.pointCommGroup (multiplicative A)
        (tripleRing (A := A) (B := B))
    let x₁₂ : (multiplicative A).Point (tripleRing (A := A) (B := B)) :=
      c.ev () () (tripleFirst (A := A) (B := B))
        (tripleSecond (A := A) (B := B))
    let x₂₃ : (multiplicative A).Point (tripleRing (A := A) (B := B)) :=
      c.ev () () (tripleSecond (A := A) (B := B))
        (tripleThird (A := A) (B := B))
    let x₁₃ : (multiplicative A).Point (tripleRing (A := A) (B := B)) :=
      c.ev () () (tripleFirst (A := A) (B := B))
        (tripleThird (A := A) (B := B))
    rw [overlapUnit_pairTwelve, overlapUnit_pairTwentyThree,
      overlapUnit_pairThirteen]
    change multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)) x₁₂ *
        multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)) x₂₃ =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)) x₁₃
    rw [← map_mul]
    have htrans := c.ev_trans () () ()
      (tripleFirst (A := A) (B := B))
      (tripleSecond (A := A) (B := B))
      (tripleThird (A := A) (B := B))
    change x₁₂ * x₂₃ = x₁₃ at htrans
    exact congrArg
      (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)))
      htrans

noncomputable def representedDescendedModule
    (c : RepresentedOneCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) : ModuleCat A :=
  (toMultiplicativeUnitCocycle c).descendedModule hf

noncomputable def representedBaseChangeIso
    (c : RepresentedOneCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) :
    (extendScalars (algebraMap A B)).obj (representedDescendedModule c hf) ≅
      ModuleCat.of B B :=
  (toMultiplicativeUnitCocycle c).baseChangeIso hf

noncomputable def representedPrimeAwayLinearEquivBase
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    {B : Type} [CommRing B]
    [Algebra (Localization.Away (ℓ : ℤ)) B] [Nontrivial B]
    (c : RepresentedOneCocycle
      (A := Localization.Away (ℓ : ℤ)) (B := B))
    (hf : (algebraMap (Localization.Away (ℓ : ℤ)) B).FaithfullyFlat) :
    representedDescendedModule c hf ≃ₗ[Localization.Away (ℓ : ℤ)]
      Localization.Away (ℓ : ℤ) :=
  (toMultiplicativeUnitCocycle c).primeAwayLinearEquivBase ℓ hℓ hf

end ScratchRepresentedMultiplicativeCocycle
