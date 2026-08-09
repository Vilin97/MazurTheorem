/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtalePrimeGroupSchemeClassification

/-!
# Finite-etale prime-order group schemes over the integers are constant

The arithmetic splitting of finite-etale integer algebras is compatible with the Hopf group
law when the product coordinates are indexed by the actual convolution group of integral
points.  Consequently a finite-etale finite-flat commutative group scheme over `Spec ℤ` of
prime constant order `p` is isomorphic to the constant group scheme on
`Multiplicative (ZMod p)`.

This is a global integral classification.  It does not classify finite-flat models over a
ramified discrete valuation ring and does not supply any missing Raynaud extension theorem,
Neron comparison, or fppf-`H¹` vanishing statement.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

namespace IntegralEtaleHopf

/-- The integral points of a Hopf algebra, equipped with convolution. -/
abbrev IntegralPoints (B : Type) [CommRing B] [Algebra ℤ B] :=
  WithConv (B →ₐ[ℤ] ℤ)

/-- Joint evaluation at all integral convolution points. -/
def evaluationAlgHom
    (B : Type) [CommRing B] [Algebra ℤ B] :
    B →ₐ[ℤ] ConstantCoordinates ℤ (IntegralPoints B) where
  toFun b := ULift.up (fun x ↦ x.ofConv b)
  map_one' := by
    apply ULift.down_injective
    funext x
    exact map_one x.ofConv
  map_mul' b c := by
    apply ULift.down_injective
    funext x
    exact map_mul x.ofConv b c
  map_zero' := by
    apply ULift.down_injective
    funext x
    exact map_zero x.ofConv
  map_add' b c := by
    apply ULift.down_injective
    funext x
    exact map_add x.ofConv b c
  commutes' z := by
    apply ULift.down_injective
    funext x
    exact x.ofConv.commutes z

@[simp]
theorem evaluationAlgHom_down_apply
    (B : Type) [CommRing B] [Algebra ℤ B]
    (b : B) (x : IntegralPoints B) :
    (evaluationAlgHom B b).down x = x.ofConv b :=
  rfl

/-- If an integer algebra is split as a finite product, joint evaluation at all of its integral
points is an algebra equivalence with the corresponding function algebra. -/
def evaluationAlgEquivOfPi
    (B : Type) [CommRing B] [Algebra ℤ B] (n : ℕ)
    (split : B ≃ₐ[ℤ] (Fin n → ℤ)) :
    B ≃ₐ[ℤ] ConstantCoordinates ℤ (IntegralPoints B) := by
  apply AlgEquiv.ofBijective (evaluationAlgHom B)
  constructor
  · intro b c h
    apply split.injective
    funext i
    let phi : B →ₐ[ℤ] ℤ :=
      (Pi.evalAlgHom ℤ (fun _ : Fin n ↦ ℤ) i).comp split.toAlgHom
    have hi := congrArg
      (fun q : ConstantCoordinates ℤ (IntegralPoints B) ↦
        q.down (WithConv.toConv phi)) h
    simpa [phi] using hi
  · intro f
    let phi : Fin n → (B →ₐ[ℤ] ℤ) := fun i ↦
      (Pi.evalAlgHom ℤ (fun _ : Fin n ↦ ℤ) i).comp split.toAlgHom
    let y : Fin n → ℤ := fun i ↦ f.down (WithConv.toConv (phi i))
    refine ⟨split.symm y, ?_⟩
    apply ULift.down_injective
    funext x
    obtain ⟨i, hi⟩ :=
      AlgHom.eq_piEvalAlgHom (x.ofConv.comp split.symm.toAlgHom)
    have hx : x.ofConv = phi i := by
      apply AlgHom.ext
      intro b
      have hb := DFunLike.congr_fun hi (split b)
      simpa [phi] using hb
    have hxconv : x = WithConv.toConv (phi i) := by
      apply WithConv.ofConv_injective
      exact hx
    change x.ofConv (split.symm y) = f.down x
    rw [hxconv]
    simp [phi, y]

@[simp]
theorem evaluationAlgEquivOfPi_down_apply
    (B : Type) [CommRing B] [Algebra ℤ B] (n : ℕ)
    (split : B ≃ₐ[ℤ] (Fin n → ℤ))
    (b : B) (x : IntegralPoints B) :
    (evaluationAlgEquivOfPi B n split b).down x = x.ofConv b :=
  rfl

/-- The convolution points of a split integer algebra are indexed by its product coordinates. -/
def integralPointsEquivFinOfPi
    (B : Type) [CommRing B] [Algebra ℤ B] (n : ℕ)
    (split : B ≃ₐ[ℤ] (Fin n → ℤ)) :
    IntegralPoints B ≃ Fin n :=
  (WithConv.equiv (B →ₐ[ℤ] ℤ)).trans
    (ConstantPrimeEtale.algHomEquivFinOfAlgEquiv B n split)

/-- Joint evaluation preserves the counit and comultiplication because convolution is defined
from those same Hopf operations. -/
def evaluationBialgEquivOfPi
    (A : AffineFiniteFlatCommGroupScheme ℤ)
    [Fintype (IntegralPoints A.coordinates)] (n : ℕ)
    (split : A.coordinates ≃ₐ[ℤ] (Fin n → ℤ)) :
    A.coordinates ≃ₐc[ℤ]
      ConstantCoordinates ℤ (IntegralPoints A.coordinates) := by
  letI : Module ℤ A.coordinates := Algebra.toModule
  letI : Module ℤ
      (ConstantCoordinates ℤ (IntegralPoints A.coordinates)) := Algebra.toModule
  let e := evaluationAlgEquivOfPi A.coordinates n split
  have ht (b : A.coordinates) (x y : IntegralPoints A.coordinates) :
      ConstantCoordinates.tensorEval
          (R := ℤ) (G := IntegralPoints A.coordinates)
          (TensorProduct.map (evaluationAlgHom A.coordinates).toLinearMap
            (evaluationAlgHom A.coordinates).toLinearMap
              (Coalgebra.comul (R := ℤ) b)) (x, y) =
        (x * y).ofConv b := by
    rw [AlgHom.convMul_apply]
    generalize Coalgebra.comul (R := ℤ) b = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
    | tmul b c =>
        simp [ConstantCoordinates.tensorEval_tmul,
          Algebra.TensorProduct.lift_tmul]
  let c : A.coordinates ≃ₗc[ℤ]
      ConstantCoordinates ℤ (IntegralPoints A.coordinates) :=
    { e.toLinearEquiv with
      counit_comp := by
        apply LinearMap.ext
        intro b
        change (e b).down (1 : IntegralPoints A.coordinates) =
          Coalgebra.counit (R := ℤ) b
        rw [evaluationAlgEquivOfPi_down_apply]
        rw [AlgHom.convOne_apply]
        simp
      map_comp_comul := by
        apply LinearMap.ext
        intro b
        apply (ConstantCoordinates.tensorEval
          (R := ℤ) (G := IntegralPoints A.coordinates)).injective
        funext q
        rcases q with ⟨x, y⟩
        change ConstantCoordinates.tensorEval
            (R := ℤ) (G := IntegralPoints A.coordinates)
            (TensorProduct.map e.toLinearMap e.toLinearMap
              (Coalgebra.comul (R := ℤ) b)) (x, y) =
          ConstantCoordinates.tensorEval
            (R := ℤ) (G := IntegralPoints A.coordinates)
            (Coalgebra.comul (R := ℤ) (e b)) (x, y)
        change ConstantCoordinates.tensorEval
            (R := ℤ) (G := IntegralPoints A.coordinates)
            (TensorProduct.map (evaluationAlgHom A.coordinates).toLinearMap
              (evaluationAlgHom A.coordinates).toLinearMap
                (Coalgebra.comul (R := ℤ) b)) (x, y) = _
        rw [ht]
        change (x * y).ofConv b =
          ConstantCoordinates.tensorEval
            (R := ℤ) (G := IntegralPoints A.coordinates)
              (ConstantCoordinates.comulAlgHom (R := ℤ)
                (G := IntegralPoints A.coordinates) (e b)) (x, y)
        rw [ConstantCoordinates.tensorEval_comulAlgHom]
        exact (evaluationAlgEquivOfPi_down_apply _ _ _ _ _).symm }
  exact BialgEquiv.mk c e.map_mul

end IntegralEtaleHopf

/-- A finite-etale finite-flat commutative group scheme over `Spec ℤ` of prime constant order
is the constant group scheme on the cyclic group of that order.  The isomorphism is built from
actual affine Hopf coordinates and canonical joint evaluation on their convolution points. -/
noncomputable def finiteEtalePrimeIsoConstantInt
    (Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hEtale : Etale Q.structureMap)
    (horder : Q.HasConstantOrder p) :
    Q ≅ constantScheme ℤ (Multiplicative (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let hrealize := exists_affineFiniteFlat_realization Q
  let A := hrealize.choose
  let e : Q ≅ A.realize := hrealize.choose_spec.some
  letI hFiniteAlg :
      @Module.Finite ℤ A.coordinates _ _ Algebra.toModule := A.property.1
  letI hFlatAlg :
      @Module.Flat ℤ A.coordinates _ _ Algebra.toModule := A.property.2
  have hModule : (Algebra.toModule : Module ℤ A.coordinates) =
      AddCommGroup.toIntModule A.coordinates := Subsingleton.elim _ _
  letI : Module.Finite ℤ A.coordinates := hModule ▸ hFiniteAlg
  letI : Module.Flat ℤ A.coordinates := hModule ▸ hFlatAlg
  letI : Module.IsTorsionFree ℤ A.coordinates := Module.Flat.isTorsionFree
  letI : Module.Free ℤ A.coordinates := Module.free_of_finite_type_torsion_free'
  have hAEtale : Etale A.realize.structureMap :=
    etale_structureMap_of_iso e.symm hEtale
  letI hEtaleAlg : Algebra.Etale ℤ A.coordinates := by
    change Etale
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ A.coordinates))) at hAEtale
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at hAEtale
    exact RingHom.etale_algebraMap.mp hAEtale
  have hAlgebra : (inferInstance : Algebra ℤ A.coordinates) =
      Ring.toIntAlgebra A.coordinates := Subsingleton.elim _ _
  letI : @Algebra.Etale ℤ A.coordinates _ _ (Ring.toIntAlgebra A.coordinates) :=
    hAlgebra ▸ hEtaleAlg
  have hAOrder : A.realize.HasConstantOrder p := by
    change A.realize.orderAt = Function.const (Spec (.of ℤ)) p
    rw [← orderAt_eq_of_iso e]
    exact horder
  let s : Spec (.of ℤ) := Classical.choice inferInstance
  have hs : A.realize.orderAt s = p := by
    simpa [HasConstantOrder] using congrFun hAOrder s
  have hrank : Module.finrank ℤ A.coordinates = p := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap ℤ A.coordinates))).finrank s = p at hs
    have hstalkAlg :
        @Module.rankAtStalk ℤ A.coordinates _ _ Algebra.toModule s = p :=
      (Scheme.Hom.finrank_SpecMap_algebraMap ℤ A.coordinates s).symm.trans hs
    have hstalk : Module.rankAtStalk A.coordinates s = p := hModule ▸ hstalkAlg
    exact (congrFun
      (Module.rankAtStalk_eq_finrank_of_free (R := ℤ) (M := A.coordinates)) s).symm.trans
        hstalk
  let splitCanonical := ConstantPrimeEtale.intAlgEquivPiFin A.coordinates
  let split : @AlgEquiv ℤ A.coordinates
      (Fin (Module.finrank ℤ A.coordinates) → ℤ) _ _ _
      (inferInstance : Algebra ℤ A.coordinates)
      (inferInstance : Algebra ℤ (Fin (Module.finrank ℤ A.coordinates) → ℤ)) := by
    exact hAlgebra.symm ▸ splitCanonical
  let H := IntegralEtaleHopf.IntegralPoints A.coordinates
  let pointEquiv : H ≃ Fin (Module.finrank ℤ A.coordinates) :=
    IntegralEtaleHopf.integralPointsEquivFinOfPi A.coordinates _ split
  letI : Fintype H :=
    Fintype.ofEquiv (Fin (Module.finrank ℤ A.coordinates)) pointEquiv.symm
  let coordinateBialgEquiv :=
    IntegralEtaleHopf.evaluationBialgEquivOfPi A _ split
  let affineIso : A.obj ≅ (constant ℤ H).obj :=
    AffineCommGroupScheme.isoOfCoordinateBialgEquiv coordinateBialgEquiv
  let realizedIso : A.realize ≅ constantScheme ℤ H :=
    ObjectProperty.isoMk (finiteFlatCommGroupSchemeProperty (Spec (.of ℤ)))
      ((AffineCommGroupScheme.realizationFunctor ℤ).mapIso affineIso)
  have hcardH : Nat.card H = p := by
    calc
      Nat.card H = Nat.card (Fin (Module.finrank ℤ A.coordinates)) :=
        Nat.card_congr pointEquiv
      _ = Module.finrank ℤ A.coordinates := Nat.card_fin _
      _ = p := hrank
  have hcardZMod : Nat.card (Multiplicative (ZMod p)) = p := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let groupIso : H ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcardH hcardZMod
  exact e ≪≫ realizedIso ≪≫ constantSchemeIsoOfMulEquiv ℤ groupIso

/-- The actual admissible constant-factor presentation obtained from finite etaleness and prime
constant order over the integers. -/
noncomputable def admissibleSimpleFactorOfFiniteEtalePrimeInt
    {p : ℕ} [NeZero p]
    (Q : FiniteFlatCommGroupScheme (Spec (.of ℤ)))
    (hp : p.Prime) (hEtale : Etale Q.structureMap)
    (horder : Q.HasConstantOrder p) :
    AdmissibleSimpleFactor ℤ p Q :=
  .constant (finiteEtalePrimeIsoConstantInt Q p hp hEtale horder)

end AlgebraicGeometry.FiniteFlatCommGroupScheme
