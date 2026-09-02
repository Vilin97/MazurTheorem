/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Pi
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtaleIntAlgebraClassification
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFiniteAffineFamily

/-!
# Effective descent for constant-prime fppf torsors over the integers

This file constructs the finite-etale torsor algebra attached to an arbitrary represented
constant-group Cech cocycle over `Spec Z`.  The arithmetic classification of finite-etale
integer algebras then supplies a section, which is converted back into an actual zero-cochain
trivializing the original global class.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct
open WithConv

universe u

noncomputable section

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

open AffineCommGroupScheme
open CategoryTheory.PresheafOfGroups

variable {R : Type u} [CommRing R]
variable {G : Type u} [CommGroup G] [Fintype G]

/-- Translation of the constant function algebra by an actual (possibly locally varying)
represented point. -/
private noncomputable def pointTranslation
    (q : ConstantCoordinates R G →ₐ[R] R) :
    ConstantCoordinates R G →ₐ[R] ConstantCoordinates R G :=
  (Algebra.TensorProduct.lift
      ((Algebra.ofId R (ConstantCoordinates R G)).comp q)
      (.id R (ConstantCoordinates R G))
      (fun _ _ ↦ Commute.all _ _)).comp
    (ConstantCoordinates.comulAlgHom (R := R) (G := G))

private theorem character_comp_pointTranslation
    (q s : ConstantCoordinates R G →ₐ[R] R) :
    s.comp (pointTranslation q) = (toConv q * toConv s).ofConv := by
  apply AlgHom.ext
  intro f
  rw [AlgHom.comp_apply, pointTranslation, AlgHom.comp_apply, AlgHom.convMul_apply]
  change
    s
        ((Algebra.TensorProduct.lift
          ((Algebra.ofId R (ConstantCoordinates R G)).comp q)
          (.id R (ConstantCoordinates R G))
          (fun (x y : ConstantCoordinates R G) ↦ Commute.all _ _))
            (ConstantCoordinates.comulAlgHom (R := R) (G := G) f)) =
      (Algebra.TensorProduct.lift q
          s
          (fun (x y : ConstantCoordinates R G) ↦ Commute.all _ _))
        (ConstantCoordinates.comulAlgHom (R := R) (G := G) f)
  generalize ConstantCoordinates.comulAlgHom (R := R) (G := G) f = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.lift_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem evaluation_comp_pointTranslation
    (q : ConstantCoordinates R G →ₐ[R] R) (g : G) :
    (ConstantCoordinates.evaluation (R := R) g).comp (pointTranslation q) =
      (toConv q * toConv (ConstantCoordinates.evaluation (R := R) g)).ofConv :=
  character_comp_pointTranslation q _

private theorem pointTranslation_comp
    (q r : ConstantCoordinates R G →ₐ[R] R) :
    (pointTranslation q).comp (pointTranslation r) =
      pointTranslation (toConv r * toConv q).ofConv := by
  apply AlgHom.ext
  intro f
  apply ULift.down_injective
  funext g
  let e := ConstantCoordinates.evaluation (R := R) g
  calc
    ((pointTranslation q).comp (pointTranslation r) f).down g =
        ((e.comp (pointTranslation q)).comp (pointTranslation r)) f := rfl
    _ = (((toConv q * toConv e).ofConv).comp (pointTranslation r)) f := by
      rw [evaluation_comp_pointTranslation]
    _ = (toConv r * (toConv q * toConv e)).ofConv f := by
      rw [character_comp_pointTranslation]
    _ = ((toConv r * toConv q) * toConv e).ofConv f := by
      rw [mul_assoc]
    _ = (e.comp (pointTranslation (toConv r * toConv q).ofConv)) f := by
      rw [character_comp_pointTranslation]
    _ = (pointTranslation (toConv r * toConv q).ofConv f).down g := rfl

private theorem pointTranslation_one :
    pointTranslation (1 : WithConv (ConstantCoordinates R G →ₐ[R] R)).ofConv =
      AlgHom.id R (ConstantCoordinates R G) := by
  apply AlgHom.ext
  intro f
  apply ULift.down_injective
  funext g
  let e := ConstantCoordinates.evaluation (R := R) g
  calc
    (pointTranslation (1 : WithConv (ConstantCoordinates R G →ₐ[R] R)).ofConv f).down g =
        (e.comp
          (pointTranslation (1 : WithConv (ConstantCoordinates R G →ₐ[R] R)).ofConv)) f :=
      rfl
    _ = ((1 : WithConv (ConstantCoordinates R G →ₐ[R] R)) * toConv e).ofConv f := by
      rw [character_comp_pointTranslation]
    _ = e f := by rw [one_mul]
    _ = ((AlgHom.id R (ConstantCoordinates R G)) f).down g := rfl

/-- Translation by a represented point is an actual algebra automorphism even when the point
is a locally varying idempotent partition rather than a distinguished constant point. -/
private noncomputable def pointTranslationAlgEquiv
    (q : ConstantCoordinates R G →ₐ[R] R) :
    ConstantCoordinates R G ≃ₐ[R] ConstantCoordinates R G where
  toFun := pointTranslation q
  invFun := pointTranslation (toConv q)⁻¹.ofConv
  left_inv f := by
    have h := DFunLike.congr_fun
      (pointTranslation_comp (toConv q)⁻¹.ofConv q) f
    rw [mul_inv_cancel, pointTranslation_one] at h
    exact h
  right_inv f := by
    have h := DFunLike.congr_fun
      (pointTranslation_comp q (toConv q)⁻¹.ofConv) f
    rw [inv_mul_cancel, pointTranslation_one] at h
    exact h
  map_mul' x y := (pointTranslation q).map_mul x y
  map_add' x y := (pointTranslation q).map_add x y
  commutes' r := (pointTranslation q).commutes r

@[simp]
private theorem pointTranslationAlgEquiv_apply
    (q : ConstantCoordinates R G →ₐ[R] R)
    (x : ConstantCoordinates R G) :
    pointTranslationAlgEquiv q x = pointTranslation q x :=
  rfl

/-- Apply a scalar map pointwise to the coordinates of a finite constant scheme. -/
private def mapConstantCoordinates
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (f : B →ₐ[A] C) :
    ConstantCoordinates B G →ₐ[A] ConstantCoordinates C G where
  toFun x := ULift.up fun g ↦ f (x.down g)
  map_one' := by
    apply ULift.down_injective
    funext g
    exact f.map_one
  map_mul' x y := by
    apply ULift.down_injective
    funext g
    exact f.map_mul _ _
  map_zero' := by
    apply ULift.down_injective
    funext g
    exact f.map_zero
  map_add' x y := by
    apply ULift.down_injective
    funext g
    exact f.map_add _ _
  commutes' a := by
    apply ULift.down_injective
    funext g
    exact f.commutes a

omit [CommGroup G] [Fintype G] in
@[simp]
private theorem mapConstantCoordinates_down_apply
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (f : B →ₐ[A] C)
    (x : ConstantCoordinates B G) (g : G) :
    (mapConstantCoordinates (G := G) f x).down g = f (x.down g) :=
  rfl

/-- Regard an `A`-valued represented point after scalar extension as the corresponding
point of the named constant scheme over the value algebra. -/
private noncomputable def baseChangedConstantCharacter
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : ConstantCoordinates A G →ₐ[A] C) :
    ConstantCoordinates C G →ₐ[C] C :=
  (Algebra.TensorProduct.lift (.id C C) q
      (fun _ _ ↦ Commute.all _ _)).comp
    (constantBaseChangeAlgEquiv (R := A) (K := C) G).symm.toAlgHom

/-- The convolution-group form of scalar extension, transported from the tensor-product Hopf
algebra to the named constant-coordinate algebra. -/
private noncomputable def constantBaseChangePointsMulEquiv
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] :
    WithConv (ConstantCoordinates A G →ₐ[A] C) ≃*
      WithConv (ConstantCoordinates C G →ₐ[C] C) :=
  (TauCeti.AlgHom.baseChangePointsMulEquiv
      (k := A) (K := C) (A := ConstantCoordinates A G) (R := C)).trans
    (TauCeti.AlgHom.mapDomainMulEquiv (A := C)
      (constantBaseChangeBialgEquiv (R := A) (K := C) G)).symm

@[simp]
private theorem constantBaseChangePointsMulEquiv_ofConv
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : ConstantCoordinates A G →ₐ[A] C) :
    (constantBaseChangePointsMulEquiv (G := G) (A := A) (C := C)
      (toConv q)).ofConv = baseChangedConstantCharacter (G := G) q := by
  rfl

@[simp]
private theorem constantBaseChangePointsMulEquiv_apply_tmul
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : WithConv (ConstantCoordinates A G →ₐ[A] C))
    (c : C) (x : ConstantCoordinates A G) :
    (constantBaseChangePointsMulEquiv (G := G) (A := A) (C := C) q).ofConv
        (constantBaseChangeAlgEquiv (R := A) (K := C) G (c ⊗ₜ[A] x)) =
      c * q.ofConv x := by
  change (AlgHom.liftEquiv A C (ConstantCoordinates A G) C q.ofConv)
      ((constantBaseChangeAlgEquiv (R := A) (K := C) G).symm
        (constantBaseChangeAlgEquiv (R := A) (K := C) G (c ⊗ₜ[A] x))) = _
  rw [AlgEquiv.symm_apply_apply]
  simp [AlgHom.liftEquiv_tmul, Algebra.smul_def]

/-- Evaluation at `g`, with its values extended from the base to an `A`-algebra. -/
private def constantEvaluationOverBase
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (g : G) :
    ConstantCoordinates A G →ₐ[A] C :=
  (Algebra.ofId A C).comp (ConstantCoordinates.evaluation (R := A) g)

@[simp]
private theorem constantBaseChangePointsMulEquiv_evaluation
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] (g : G) :
    constantBaseChangePointsMulEquiv (G := G) (A := A) (C := C)
        (toConv (constantEvaluationOverBase (G := G) (A := A) (C := C) g)) =
      toConv (ConstantCoordinates.evaluation (R := C) g) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  let e := constantBaseChangeAlgEquiv (R := A) (K := C) G
  let z := e.symm x
  have hx : x = e z := (e.apply_symm_apply x).symm
  rw [hx]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul c y =>
      rw [constantBaseChangePointsMulEquiv_apply_tmul,
        ConstantCoordinates.evaluation_apply,
        constantBaseChangeAlgEquiv_tmul]
      simp [constantEvaluationOverBase, Algebra.smul_def, mul_comm]

private theorem mapConstantCoordinates_constantBaseChangeAlgEquiv_tmul
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (f : C →ₐ[A] D)
    (c : C) (x : ConstantCoordinates A G) :
    mapConstantCoordinates (G := G) f
        (constantBaseChangeAlgEquiv (R := A) (K := C) G (c ⊗ₜ[A] x)) =
      constantBaseChangeAlgEquiv (R := A) (K := D) G (f c ⊗ₜ[A] x) := by
  apply ULift.down_injective
  funext g
  simp [mapConstantCoordinates_down_apply,
    constantBaseChangeAlgEquiv_tmul, map_mul]

/-- Scalar extension of represented constant points is natural in the value algebra. -/
private theorem baseChangedConstantCharacter_natural
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (f : C →ₐ[A] D)
    (q : ConstantCoordinates A G →ₐ[A] C)
    (x : ConstantCoordinates C G) :
    baseChangedConstantCharacter (G := G) (f.comp q)
        (mapConstantCoordinates (G := G) f x) =
      f (baseChangedConstantCharacter (G := G) q x) := by
  let e := constantBaseChangeAlgEquiv (R := A) (K := C) G
  let z := e.symm x
  have hx : x = e z := by
    exact (e.apply_symm_apply x).symm
  rw [hx]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul c y =>
      rw [mapConstantCoordinates_constantBaseChangeAlgEquiv_tmul]
      simp [baseChangedConstantCharacter, e,
        Algebra.TensorProduct.lift_tmul, map_mul]

private theorem map_convolution_constantEvaluationOverBase
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (f : C →ₐ[A] D)
    (q : ConstantCoordinates A G →ₐ[A] C)
    (g : G) (x : ConstantCoordinates A G) :
    f ((toConv q *
        toConv (constantEvaluationOverBase (G := G) (A := A) (C := C) g)).ofConv x) =
      (toConv (f.comp q) *
        toConv (constantEvaluationOverBase (G := G) (A := A) (C := D) g)).ofConv x := by
  have h := congrArg (fun r : WithConv (ConstantCoordinates A G →ₐ[A] D) ↦
      r.ofConv x)
    (map_mul (TauCeti.AlgHom.mapValue (H := ConstantCoordinates A G) f)
      (toConv q)
      (toConv (constantEvaluationOverBase (G := G) (A := A) (C := C) g)))
  have heval :
      f.comp (constantEvaluationOverBase (G := G) (A := A) (C := C) g) =
        constantEvaluationOverBase (G := G) (A := A) (C := D) g := by
    apply AlgHom.ext
    intro y
    change f (algebraMap A C (y.down g)) = algebraMap A D (y.down g)
    exact f.commutes (y.down g)
  simpa [TauCeti.AlgHom.mapValue_apply, heval] using h

/-- Translation of constant coordinates commutes with post-composition in the value algebra. -/
private theorem pointTranslation_baseChanged_natural
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (f : C →ₐ[A] D)
    (q : ConstantCoordinates A G →ₐ[A] C)
    (x : ConstantCoordinates C G) :
    mapConstantCoordinates (G := G) f
        (pointTranslation (baseChangedConstantCharacter (G := G) q) x) =
      pointTranslation (baseChangedConstantCharacter (G := G) (f.comp q))
        (mapConstantCoordinates (G := G) f x) := by
  apply ULift.down_injective
  funext g
  rw [mapConstantCoordinates_down_apply]
  change f (((ConstantCoordinates.evaluation (R := C) g).comp
    (pointTranslation (baseChangedConstantCharacter (G := G) q))) x) = _
  rw [evaluation_comp_pointTranslation]
  rw [← constantBaseChangePointsMulEquiv_ofConv (G := G) (A := A) (C := C)]
  rw [← constantBaseChangePointsMulEquiv_evaluation (G := G) (A := A) (C := C)]
  rw [← map_mul]
  let e := constantBaseChangeAlgEquiv (R := A) (K := C) G
  let z := e.symm x
  have hx : x = e z := (e.apply_symm_apply x).symm
  rw [hx]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa [map_add] using congrArg₂ (fun a b ↦ a + b) hz hw
  | tmul c y =>
      rw [constantBaseChangePointsMulEquiv_apply_tmul,
        mapConstantCoordinates_constantBaseChangeAlgEquiv_tmul]
      change f (c * _) =
        ((ConstantCoordinates.evaluation (R := D) g).comp
          (pointTranslation (baseChangedConstantCharacter (G := G) (f.comp q)))
            (constantBaseChangeAlgEquiv (R := A) (K := D) G (f c ⊗ₜ[A] y)))
      rw [evaluation_comp_pointTranslation]
      change f (c * _) =
        (((constantBaseChangePointsMulEquiv (G := G) (A := A) (C := D)
            (toConv (f.comp q))) *
          toConv (ConstantCoordinates.evaluation (R := D) g)).ofConv
            (constantBaseChangeAlgEquiv (R := A) (K := D) G (f c ⊗ₜ[A] y)))
      rw [← constantBaseChangePointsMulEquiv_evaluation
        (G := G) (A := A) (C := D), ← map_mul,
        constantBaseChangePointsMulEquiv_apply_tmul]
      rw [map_mul, map_convolution_constantEvaluationOverBase]

private abbrev PairAlgebra
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  B ⊗[A] B

/-- The right-associated threefold overlap algebra. -/
private abbrev TripleAlgebra
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  B ⊗[A] PairAlgebra A B

private noncomputable def firstToTriple
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] TripleAlgebra A B :=
  Algebra.TensorProduct.includeLeft

private noncomputable def secondToTriple
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] TripleAlgebra A B :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft

private noncomputable def thirdToTriple
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    B →ₐ[A] TripleAlgebra A B :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight

/-- Pull the pair overlap to factors one and two. -/
private noncomputable def pairTwelve
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    PairAlgebra A B →ₐ[A] TripleAlgebra A B :=
  Algebra.TensorProduct.productMap firstToTriple secondToTriple

/-- Pull the pair overlap to factors two and three. -/
private noncomputable def pairTwentyThree
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    PairAlgebra A B →ₐ[A] TripleAlgebra A B :=
  Algebra.TensorProduct.includeRight

/-- Pull the pair overlap to factors one and three. -/
private noncomputable def pairThirteen
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    PairAlgebra A B →ₐ[A] TripleAlgebra A B :=
  Algebra.TensorProduct.productMap firstToTriple thirdToTriple

@[simp]
private theorem pairTwelve_tmul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (x y : B) :
    pairTwelve (A := A) (B := B) (x ⊗ₜ[A] y) =
      x ⊗ₜ[A] (y ⊗ₜ[A] (1 : B)) := by
  simp [pairTwelve, firstToTriple, secondToTriple]

@[simp]
private theorem pairTwentyThree_tmul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (x y : B) :
    pairTwentyThree (A := A) (B := B) (x ⊗ₜ[A] y) =
      (1 : B) ⊗ₜ[A] (x ⊗ₜ[A] y) := by
  simp [pairTwentyThree]

@[simp]
private theorem pairThirteen_tmul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (x y : B) :
    pairThirteen (A := A) (B := B) (x ⊗ₜ[A] y) =
      x ⊗ₜ[A] ((1 : B) ⊗ₜ[A] y) := by
  simp [pairThirteen, firstToTriple, thirdToTriple]

/-- The untwisted first pullback of the local constant-coordinate algebra. -/
private def constantDescentLeft
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    ConstantCoordinates B G →ₐ[A]
      ConstantCoordinates (PairAlgebra A B) G :=
  mapConstantCoordinates (G := G) Algebra.TensorProduct.includeLeft

/-- The second pullback, translated by the actual overlap point. -/
private noncomputable def constantDescentRight
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) :
    ConstantCoordinates B G →ₐ[A]
      ConstantCoordinates (PairAlgebra A B) G :=
  ((pointTranslationAlgEquiv (baseChangedConstantCharacter q)).toAlgHom.restrictScalars A).comp
    (mapConstantCoordinates (G := G) Algebra.TensorProduct.includeRight)

/-- The affine algebra obtained by equalizing the two cocycle-twisted pullbacks. -/
private abbrev constantTorsorAlgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) :=
  AlgHom.equalizer (constantDescentLeft (G := G) (A := A) (B := B))
    (constantDescentRight (G := G) q)

/-- Pulling the locally constant coordinate algebra one more time to the left-hand copy of the
cover gives the constant coordinate algebra on the pair overlap. -/
private noncomputable def outerConstantBaseChangeEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] ConstantCoordinates B G ≃ₐ[B]
      ConstantCoordinates (PairAlgebra A B) G := by
  classical
  exact (Algebra.TensorProduct.congr
      (AlgEquiv.refl : B ≃ₐ[B] B)
      (ULift.algEquiv (R := A) : ConstantCoordinates B G ≃ₐ[A] (G → B))).trans <|
    (Algebra.TensorProduct.piRight A B B (fun _ : G ↦ B)).trans <|
      (ULift.algEquiv (R := B)).symm

@[simp]
private theorem outerConstantBaseChangeEquiv_tmul_down_apply
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (x : ConstantCoordinates B G) (g : G) :
    (outerConstantBaseChangeEquiv (G := G) (A := A) (B := B) (b ⊗ₜ[A] x)).down g =
      (Algebra.TensorProduct.includeLeft (R := A) (S := B) (A := B) (B := B)) b *
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)) (x.down g) := by
  simp [outerConstantBaseChangeEquiv, ConstantCoordinates,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

/-- The analogous coordinatewise comparison on the right-associated triple overlap. -/
private noncomputable def outerConstantTripleBaseChangeEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] ConstantCoordinates (PairAlgebra A B) G ≃ₐ[B]
      ConstantCoordinates
        (B ⊗[A] PairAlgebra A B) G := by
  classical
  exact (Algebra.TensorProduct.congr
      (AlgEquiv.refl : B ≃ₐ[B] B)
      (ULift.algEquiv (R := A) :
        ConstantCoordinates (PairAlgebra A B) G ≃ₐ[A]
          (G → PairAlgebra A B))).trans <|
    (Algebra.TensorProduct.piRight A B B
      (fun _ : G ↦ PairAlgebra A B)).trans <|
      (ULift.algEquiv (R := B)).symm

@[simp]
private theorem outerConstantTripleBaseChangeEquiv_tmul_down_apply
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (x : ConstantCoordinates (PairAlgebra A B) G) (g : G) :
    (outerConstantTripleBaseChangeEquiv (G := G) (A := A) (B := B)
      (b ⊗ₜ[A] x)).down g =
        (Algebra.TensorProduct.includeLeft
          (R := A) (S := B) (A := B) (B := PairAlgebra A B)) b *
          (Algebra.TensorProduct.includeRight
            (R := A) (A := B) (B := PairAlgebra A B)) (x.down g) := by
  simp [outerConstantTripleBaseChangeEquiv, ConstantCoordinates,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

private noncomputable def tensorDescentLeft
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] ConstantCoordinates B G →ₐ[B]
      B ⊗[A] ConstantCoordinates (PairAlgebra A B) G :=
  Algebra.TensorProduct.map (AlgHom.id B B)
    (constantDescentLeft (G := G) (A := A) (B := B))

private noncomputable def tensorDescentRight
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) :
    B ⊗[A] ConstantCoordinates B G →ₐ[B]
      B ⊗[A] ConstantCoordinates (PairAlgebra A B) G :=
  Algebra.TensorProduct.map (AlgHom.id B B)
    (constantDescentRight (G := G) q)

private theorem outerConstantBaseChange_tensorDescentLeft
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (z : B ⊗[A] ConstantCoordinates B G) :
    outerConstantTripleBaseChangeEquiv (G := G) (A := A) (B := B)
        (tensorDescentLeft (G := G) (A := A) (B := B) z) =
      mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B))
        (outerConstantBaseChangeEquiv (G := G) (A := A) (B := B) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add, hz, hw]
  | tmul b x =>
      apply ULift.down_injective
      funext g
      simp [tensorDescentLeft, constantDescentLeft,
        mapConstantCoordinates_down_apply, pairTwelve, firstToTriple, secondToTriple]

private theorem outerConstantBaseChange_tensorDescentRight
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (z : B ⊗[A] ConstantCoordinates B G) :
    outerConstantTripleBaseChangeEquiv (G := G) (A := A) (B := B)
        (tensorDescentRight (G := G) q z) =
      pointTranslation
          (baseChangedConstantCharacter (G := G)
            ((pairTwentyThree (A := A) (B := B)).comp q))
        (mapConstantCoordinates (G := G) (pairThirteen (A := A) (B := B))
          (outerConstantBaseChangeEquiv (G := G) (A := A) (B := B) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa [map_add] using congrArg₂ (fun a b ↦ a + b) hz hw
  | tmul b x =>
      let E := TripleAlgebra A B
      let H := ConstantCoordinates E G
      have hinput :
          mapConstantCoordinates (G := G) (pairThirteen (A := A) (B := B))
              (outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)
                (b ⊗ₜ[A] x)) =
            algebraMap E H (firstToTriple (A := A) (B := B) b) *
              mapConstantCoordinates (G := G) (pairTwentyThree (A := A) (B := B))
                (mapConstantCoordinates (G := G)
                  (Algebra.TensorProduct.includeRight :
                    B →ₐ[A] PairAlgebra A B) x) := by
        apply ULift.down_injective
        funext h
        simp [E, H, mapConstantCoordinates_down_apply,
          pairTwentyThree, pairThirteen, firstToTriple, thirdToTriple]
      have hnat := pointTranslation_baseChanged_natural
        (G := G) (f := pairTwentyThree (A := A) (B := B)) q
        (mapConstantCoordinates (G := G)
          (Algebra.TensorProduct.includeRight :
            B →ₐ[A] PairAlgebra A B) x)
      apply ULift.down_injective
      funext g
      have hnatg := congrArg (fun y ↦ y.down g) hnat
      simp [tensorDescentRight, constantDescentRight,
        mapConstantCoordinates_down_apply] at hnatg ⊢
      rw [hinput, map_mul]
      dsimp only [E, H]
      have hscalar :=
        (pointTranslation
          (baseChangedConstantCharacter (G := G)
            ((pairTwentyThree (A := A) (B := B)).comp q))).commutes
              (firstToTriple (A := A) (B := B) b)
      rw [hscalar]
      change b ⊗ₜ[A]
          ((pointTranslation (baseChangedConstantCharacter (G := G) q)
            (mapConstantCoordinates (G := G)
              (Algebra.TensorProduct.includeRight :
                B →ₐ[A] PairAlgebra A B) x)).down g) =
        firstToTriple (A := A) (B := B) b * _
      rw [← hnatg]
      simp [firstToTriple, pairTwentyThree]

/-- The usual Cech cocycle law, written in the represented convolution group on the
threefold overlap. -/
private def IsConstantCechCocycle
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) : Prop :=
  toConv ((pairTwelve (A := A) (B := B)).comp q) *
      toConv ((pairTwentyThree (A := A) (B := B)).comp q) =
    toConv ((pairThirteen (A := A) (B := B)).comp q)

/-- After pulling the torsor back to its cover, inverse translation by the cocycle
identifies it with the constant algebra. -/
private noncomputable def constantLocalSplit
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) :
    ConstantCoordinates B G →ₐ[B]
      ConstantCoordinates (PairAlgebra A B) G :=
  ((pointTranslationAlgEquiv
      (toConv (baseChangedConstantCharacter (G := G) q))⁻¹.ofConv).toAlgHom.restrictScalars B).comp
    (mapConstantCoordinates (G := G)
      (Algebra.TensorProduct.includeLeft :
        B →ₐ[B] PairAlgebra A B))

/-- Multiplication on the overlap recovers the constant coordinate after translating back
by the cocycle. -/
private noncomputable def constantLocalRecover
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) :
    ConstantCoordinates (PairAlgebra A B) G →ₐ[B]
      ConstantCoordinates B G :=
  (mapConstantCoordinates (G := G)
      (Algebra.TensorProduct.lmul'' A : PairAlgebra A B →ₐ[B] B)).comp
    ((pointTranslationAlgEquiv
      (baseChangedConstantCharacter (G := G) q)).toAlgHom.restrictScalars B)

private theorem constantLocalRecover_split
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (x : ConstantCoordinates B G) :
    constantLocalRecover (G := G) q (constantLocalSplit (G := G) q x) = x := by
  let qB := baseChangedConstantCharacter (G := G) q
  have hcancel := pointTranslation_comp qB (toConv qB)⁻¹.ofConv
  rw [inv_mul_cancel, pointTranslation_one] at hcancel
  apply ULift.down_injective
  funext g
  simp only [constantLocalRecover, constantLocalSplit, AlgHom.comp_apply,
    mapConstantCoordinates_down_apply]
  change (Algebra.TensorProduct.lmul'' A)
      ((pointTranslation qB
        (pointTranslation (toConv qB)⁻¹.ofConv
          (mapConstantCoordinates (G := G)
            (Algebra.TensorProduct.includeLeft :
              B →ₐ[B] PairAlgebra A B) x))).down g) = x.down g
  rw [← AlgHom.comp_apply, hcancel]
  simp only [AlgHom.id_apply, mapConstantCoordinates_down_apply]
  change x.down g * 1 = x.down g
  exact mul_one _

private theorem baseChangedConstantCharacter_inv
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (q : ConstantCoordinates A G →ₐ[A] C) :
    baseChangedConstantCharacter (G := G) (toConv q)⁻¹.ofConv =
      (toConv (baseChangedConstantCharacter (G := G) q))⁻¹.ofConv := by
  change
    (constantBaseChangePointsMulEquiv (G := G) (A := A) (C := C)
      ((toConv q)⁻¹)).ofConv =
      ((constantBaseChangePointsMulEquiv (G := G) (A := A) (C := C)
        (toConv q))⁻¹).ofConv
  rw [map_inv]

private theorem mapValue_constantCharacter_inv
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (f : C →ₐ[A] D)
    (q : ConstantCoordinates A G →ₐ[A] C) :
    f.comp (toConv q)⁻¹.ofConv = (toConv (f.comp q))⁻¹.ofConv := by
  change ((TauCeti.AlgHom.mapValue (H := ConstantCoordinates A G) f)
      ((toConv q)⁻¹)).ofConv =
    ((TauCeti.AlgHom.mapValue (H := ConstantCoordinates A G) f)
      (toConv q))⁻¹.ofConv
  rw [map_inv]

private theorem baseChangedConstantCocycle_inverse_relation
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    (toConv (baseChangedConstantCharacter (G := G)
        ((pairThirteen (A := A) (B := B)).comp q)))⁻¹ *
        toConv (baseChangedConstantCharacter (G := G)
          ((pairTwentyThree (A := A) (B := B)).comp q)) =
      (toConv (baseChangedConstantCharacter (G := G)
        ((pairTwelve (A := A) (B := B)).comp q)))⁻¹ := by
  let e := constantBaseChangePointsMulEquiv (G := G) (A := A)
    (C := TripleAlgebra A B)
  have hqE := congrArg e hq
  rw [map_mul] at hqE
  change
    toConv (baseChangedConstantCharacter (G := G)
        ((pairTwelve (A := A) (B := B)).comp q)) *
      toConv (baseChangedConstantCharacter (G := G)
        ((pairTwentyThree (A := A) (B := B)).comp q)) =
      toConv (baseChangedConstantCharacter (G := G)
        ((pairThirteen (A := A) (B := B)).comp q)) at hqE
  rw [← hqE, mul_inv_rev, mul_assoc,
    mul_comm ((toConv (baseChangedConstantCharacter (G := G)
      ((pairTwelve (A := A) (B := B)).comp q)))⁻¹),
    ← mul_assoc, inv_mul_cancel, one_mul]

private theorem mapConstantCoordinates_localLeft_pairTwelve_eq_pairThirteen
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (x : ConstantCoordinates B G) :
    mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B))
        (mapConstantCoordinates (G := G)
          (Algebra.TensorProduct.includeLeft :
            B →ₐ[B] PairAlgebra A B) x) =
      mapConstantCoordinates (G := G) (pairThirteen (A := A) (B := B))
        (mapConstantCoordinates (G := G)
          (Algebra.TensorProduct.includeLeft :
            B →ₐ[B] PairAlgebra A B) x) := by
  apply ULift.down_injective
  funext g
  simp [mapConstantCoordinates_down_apply, pairTwelve, pairThirteen,
    firstToTriple, secondToTriple, thirdToTriple]

private theorem constantLocalSplit_triple
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q)
    (x : ConstantCoordinates B G) :
    mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B))
        (constantLocalSplit (G := G) q x) =
      pointTranslation
          (baseChangedConstantCharacter (G := G)
            ((pairTwentyThree (A := A) (B := B)).comp q))
        (mapConstantCoordinates (G := G)
          (pairThirteen (A := A) (B := B))
          (constantLocalSplit (G := G) q x)) := by
  let qInv : ConstantCoordinates A G →ₐ[A] PairAlgebra A B :=
    (toConv q)⁻¹.ofConv
  let y : ConstantCoordinates (PairAlgebra A B) G :=
    mapConstantCoordinates (G := G)
      (Algebra.TensorProduct.includeLeft :
        B →ₐ[B] PairAlgebra A B) x
  have h12 := pointTranslation_baseChanged_natural
    (G := G) (f := pairTwelve (A := A) (B := B)) qInv y
  have h13 := pointTranslation_baseChanged_natural
    (G := G) (f := pairThirteen (A := A) (B := B)) qInv y
  have hcomp12 :
      (pairTwelve (A := A) (B := B)).comp qInv =
        (toConv ((pairTwelve (A := A) (B := B)).comp q))⁻¹.ofConv := by
    exact mapValue_constantCharacter_inv
      (G := G) (pairTwelve (A := A) (B := B)) q
  have hcomp13 :
      (pairThirteen (A := A) (B := B)).comp qInv =
        (toConv ((pairThirteen (A := A) (B := B)).comp q))⁻¹.ofConv := by
    exact mapValue_constantCharacter_inv
      (G := G) (pairThirteen (A := A) (B := B)) q
  rw [hcomp12, baseChangedConstantCharacter_inv] at h12
  rw [hcomp13, baseChangedConstantCharacter_inv] at h13
  change
    mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B))
        (pointTranslation
          (toConv (baseChangedConstantCharacter (G := G) q))⁻¹.ofConv y) =
      pointTranslation
          (baseChangedConstantCharacter (G := G)
            ((pairTwentyThree (A := A) (B := B)).comp q))
        (mapConstantCoordinates (G := G)
          (pairThirteen (A := A) (B := B))
          (pointTranslation
            (toConv (baseChangedConstantCharacter (G := G) q))⁻¹.ofConv y))
  rw [h12, h13]
  rw [baseChangedConstantCharacter_inv, baseChangedConstantCharacter_inv]
  rw [mapConstantCoordinates_localLeft_pairTwelve_eq_pairThirteen
    (G := G) (A := A) (B := B) x]
  rw [← AlgHom.comp_apply, pointTranslation_comp]
  rw [baseChangedConstantCocycle_inverse_relation (G := G) q hq]

/-- Collapse the first two factors of the threefold overlap. -/
private noncomputable def collapseFirstTwo
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    TripleAlgebra A B →ₐ[A] PairAlgebra A B :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] PairAlgebra A B)
    (AlgHom.id A (PairAlgebra A B))
    (fun _ _ ↦ Commute.all _ _)

private theorem collapseFirstTwo_comp_pairTwelve
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    (collapseFirstTwo (A := A) (B := B)).comp
        (pairTwelve (A := A) (B := B)) =
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] PairAlgebra A B).comp
        (Algebra.TensorProduct.lmul' A : PairAlgebra A B →ₐ[A] B) := by
  ext <;> simp [collapseFirstTwo, pairTwelve, firstToTriple, secondToTriple]

private theorem collapseFirstTwo_comp_pairThirteen
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    (collapseFirstTwo (A := A) (B := B)).comp
        (pairThirteen (A := A) (B := B)) =
      AlgHom.id A (PairAlgebra A B) := by
  ext <;> simp [collapseFirstTwo, pairThirteen, firstToTriple, thirdToTriple]

private theorem baseChangedConstantCocycle_relation
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    toConv (baseChangedConstantCharacter (G := G)
        ((pairTwelve (A := A) (B := B)).comp q)) *
        toConv (baseChangedConstantCharacter (G := G)
          ((pairTwentyThree (A := A) (B := B)).comp q)) =
      toConv (baseChangedConstantCharacter (G := G)
        ((pairThirteen (A := A) (B := B)).comp q)) := by
  let e := constantBaseChangePointsMulEquiv (G := G) (A := A)
    (C := TripleAlgebra A B)
  have hqE := congrArg e hq
  rw [map_mul] at hqE
  exact hqE

private theorem constantTranslated_triple_equal
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q)
    (y : ConstantCoordinates (PairAlgebra A B) G)
    (hy :
      mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B)) y =
        pointTranslation
            (baseChangedConstantCharacter (G := G)
              ((pairTwentyThree (A := A) (B := B)).comp q))
          (mapConstantCoordinates (G := G)
            (pairThirteen (A := A) (B := B)) y)) :
    mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B))
        (pointTranslation (baseChangedConstantCharacter (G := G) q) y) =
      mapConstantCoordinates (G := G) (pairThirteen (A := A) (B := B))
        (pointTranslation (baseChangedConstantCharacter (G := G) q) y) := by
  have h12 := pointTranslation_baseChanged_natural
    (G := G) (f := pairTwelve (A := A) (B := B)) q y
  have h13 := pointTranslation_baseChanged_natural
    (G := G) (f := pairThirteen (A := A) (B := B)) q y
  rw [h12, h13, hy]
  rw [← AlgHom.comp_apply, pointTranslation_comp]
  rw [mul_comm, baseChangedConstantCocycle_relation (G := G) q hq]

private theorem constantLocalLeft_recover_eq_translated
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q)
    (y : ConstantCoordinates (PairAlgebra A B) G)
    (hy :
      mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B)) y =
        pointTranslation
            (baseChangedConstantCharacter (G := G)
              ((pairTwentyThree (A := A) (B := B)).comp q))
          (mapConstantCoordinates (G := G)
            (pairThirteen (A := A) (B := B)) y)) :
    mapConstantCoordinates (G := G)
        (Algebra.TensorProduct.includeLeft :
          B →ₐ[B] PairAlgebra A B)
        (constantLocalRecover (G := G) q y) =
      pointTranslation (baseChangedConstantCharacter (G := G) q) y := by
  let w := pointTranslation (baseChangedConstantCharacter (G := G) q) y
  have hw := constantTranslated_triple_equal (G := G) q hq y hy
  have hc := congrArg
    (mapConstantCoordinates (G := G) (collapseFirstTwo (A := A) (B := B))) hw
  apply ULift.down_injective
  funext g
  have hcg := congrArg (fun z ↦ z.down g) hc
  simp only [mapConstantCoordinates_down_apply] at hcg
  rw [← AlgHom.comp_apply, collapseFirstTwo_comp_pairTwelve] at hcg
  rw [← AlgHom.comp_apply, collapseFirstTwo_comp_pairThirteen] at hcg
  change
    (Algebra.TensorProduct.includeLeft :
        B →ₐ[B] PairAlgebra A B)
        ((Algebra.TensorProduct.lmul'' A)
          ((pointTranslation (baseChangedConstantCharacter (G := G) q) y).down g)) =
      (pointTranslation (baseChangedConstantCharacter (G := G) q) y).down g
  exact hcg

private theorem constantLocalSplit_recover
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q)
    (y : ConstantCoordinates (PairAlgebra A B) G)
    (hy :
      mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B)) y =
        pointTranslation
            (baseChangedConstantCharacter (G := G)
              ((pairTwentyThree (A := A) (B := B)).comp q))
          (mapConstantCoordinates (G := G)
            (pairThirteen (A := A) (B := B)) y)) :
    constantLocalSplit (G := G) q (constantLocalRecover (G := G) q y) = y := by
  let qB := baseChangedConstantCharacter (G := G) q
  have hleft := constantLocalLeft_recover_eq_translated (G := G) q hq y hy
  have hcancel := pointTranslation_comp (toConv qB)⁻¹.ofConv qB
  rw [mul_inv_cancel, pointTranslation_one] at hcancel
  apply ULift.down_injective
  funext g
  change
    (pointTranslation (toConv qB)⁻¹.ofConv
      (mapConstantCoordinates (G := G)
        (Algebra.TensorProduct.includeLeft :
          B →ₐ[B] PairAlgebra A B)
        (constantLocalRecover (G := G) q y))).down g = y.down g
  rw [hleft]
  exact congrArg (fun z ↦ z.down g) (DFunLike.congr_fun hcancel y)

private abbrev constantPulledTorsorAlgebra
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) :=
  AlgHom.equalizer
    (tensorDescentLeft (G := G) (A := A) (B := B))
    (tensorDescentRight (G := G) q)

private noncomputable def constantLocalSplitEqualizer
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    ConstantCoordinates B G →ₐ[B] constantPulledTorsorAlgebra (G := G) q :=
  AlgHom.codRestrict
    ((outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)).symm.toAlgHom.comp
      (constantLocalSplit (G := G) q)) _ fun x ↦ by
    change
      tensorDescentLeft (G := G) (A := A) (B := B)
          ((outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)).symm
            (constantLocalSplit (G := G) q x)) =
        tensorDescentRight (G := G) q
          ((outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)).symm
            (constantLocalSplit (G := G) q x))
    apply (outerConstantTripleBaseChangeEquiv
      (G := G) (A := A) (B := B)).injective
    rw [outerConstantBaseChange_tensorDescentLeft,
      outerConstantBaseChange_tensorDescentRight]
    simp only [AlgEquiv.apply_symm_apply]
    exact constantLocalSplit_triple (G := G) q hq x

private noncomputable def constantLocalRecoverEqualizer
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B) :
    constantPulledTorsorAlgebra (G := G) q →ₐ[B]
      ConstantCoordinates B G :=
  (constantLocalRecover (G := G) q).comp
    ((outerConstantBaseChangeEquiv
      (G := G) (A := A) (B := B)).toAlgHom.comp
      (AlgHom.equalizer
        (tensorDescentLeft (G := G) (A := A) (B := B))
        (tensorDescentRight (G := G) q)).val)

private theorem constantLocalRecoverEqualizer_split
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    (constantLocalRecoverEqualizer (G := G) q).comp
        (constantLocalSplitEqualizer (G := G) q hq) =
      AlgHom.id B (ConstantCoordinates B G) := by
  apply AlgHom.ext
  intro x
  change constantLocalRecover (G := G) q
      ((outerConstantBaseChangeEquiv (G := G) (A := A) (B := B))
        ((outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)).symm
          (constantLocalSplit (G := G) q x))) = x
  rw [AlgEquiv.apply_symm_apply]
  exact constantLocalRecover_split (G := G) q x

private theorem constantLocalSplitEqualizer_recover
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    (constantLocalSplitEqualizer (G := G) q hq).comp
        (constantLocalRecoverEqualizer (G := G) q) =
      AlgHom.id B (constantPulledTorsorAlgebra (G := G) q) := by
  apply AlgHom.ext
  intro z
  let y := outerConstantBaseChangeEquiv (G := G) (A := A) (B := B) z.1
  have hz := z.2
  have hy :
      mapConstantCoordinates (G := G) (pairTwelve (A := A) (B := B)) y =
        pointTranslation
            (baseChangedConstantCharacter (G := G)
              ((pairTwentyThree (A := A) (B := B)).comp q))
          (mapConstantCoordinates (G := G)
            (pairThirteen (A := A) (B := B)) y) := by
    have hz' := congrArg
      (outerConstantTripleBaseChangeEquiv (G := G) (A := A) (B := B)) hz
    rw [outerConstantBaseChange_tensorDescentLeft,
      outerConstantBaseChange_tensorDescentRight] at hz'
    exact hz'
  apply Subtype.ext
  change
    (outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)).symm
        (constantLocalSplit (G := G) q
          (constantLocalRecover (G := G) q y)) = z.1
  apply (outerConstantBaseChangeEquiv
    (G := G) (A := A) (B := B)).injective
  rw [AlgEquiv.apply_symm_apply]
  exact constantLocalSplit_recover (G := G) q hq y hy

/-- The cocycle-twisted equalizer becomes the constant coordinate algebra after pulling back
to the faithfully-flat cover. -/
private noncomputable def constantPulledTorsorEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    constantPulledTorsorAlgebra (G := G) q ≃ₐ[B]
      ConstantCoordinates B G :=
  AlgEquiv.ofAlgHom
    (constantLocalRecoverEqualizer (G := G) q)
    (constantLocalSplitEqualizer (G := G) q hq)
    (constantLocalRecoverEqualizer_split (G := G) q hq)
    (constantLocalSplitEqualizer_recover (G := G) q hq)

/-- Flat base change carries the descended twisted equalizer algebra to the constant
coordinate algebra on the cover. -/
private noncomputable def constantTorsorBaseChangeEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    B ⊗[A] constantTorsorAlgebra (G := G) q ≃ₐ[B]
      ConstantCoordinates B G :=
  (AlgHom.tensorEqualizerEquiv B B
    (constantDescentLeft (G := G) (A := A) (B := B))
    (constantDescentRight (G := G) q)).trans
      (constantPulledTorsorEquiv (G := G) q hq)

private theorem constantTorsorBaseChangeEquiv_includeRight
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q)
    (t : constantTorsorAlgebra (G := G) q) :
    constantTorsorBaseChangeEquiv (G := G) q hq
        ((Algebra.TensorProduct.includeRight :
          constantTorsorAlgebra (G := G) q →ₐ[A]
            B ⊗[A] constantTorsorAlgebra (G := G) q) t) =
      t.1 := by
  apply ULift.down_injective
  funext g
  have ht := t.2
  have htg := congrArg (fun x ↦ x.down g) ht
  change
    (constantLocalRecover (G := G) q
      (outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)
        ((Algebra.TensorProduct.map (AlgHom.id B B)
          (AlgHom.equalizer
            (constantDescentLeft (G := G) (A := A) (B := B))
            (constantDescentRight (G := G) q)).val)
          (1 ⊗ₜ[A] t)))).down g = t.1.down g
  rw [Algebra.TensorProduct.map_tmul]
  change
    (constantLocalRecover (G := G) q
      (outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)
        (1 ⊗ₜ[A] t.1))).down g = t.1.down g
  have houter :
      outerConstantBaseChangeEquiv (G := G) (A := A) (B := B)
          (1 ⊗ₜ[A] t.1) =
        mapConstantCoordinates (G := G)
          (Algebra.TensorProduct.includeRight : B →ₐ[A] PairAlgebra A B) t.1 := by
    apply ULift.down_injective
    funext h
    simp [outerConstantBaseChangeEquiv_tmul_down_apply,
      mapConstantCoordinates_down_apply,
      Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]
  rw [houter]
  change
    (Algebra.TensorProduct.lmul'' A)
        ((pointTranslation (baseChangedConstantCharacter (G := G) q)
          (mapConstantCoordinates (G := G)
            (Algebra.TensorProduct.includeRight : B →ₐ[A] PairAlgebra A B)
            t.1)).down g) =
      t.1.down g
  change
    (mapConstantCoordinates (G := G)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] PairAlgebra A B) t.1).down g =
      (pointTranslation (baseChangedConstantCharacter (G := G) q)
        (mapConstantCoordinates (G := G)
          (Algebra.TensorProduct.includeRight : B →ₐ[A] PairAlgebra A B)
          t.1)).down g at htg
  have hcollapsed := congrArg (Algebra.TensorProduct.lmul'' A) htg
  change t.1.down g * 1 =
    (Algebra.TensorProduct.lmul'' A)
      ((pointTranslation (baseChangedConstantCharacter (G := G) q)
        (mapConstantCoordinates (G := G)
          (Algebra.TensorProduct.includeRight : B →ₐ[A] PairAlgebra A B)
          t.1)).down g) at hcollapsed
  simpa only [mul_one] using hcollapsed.symm

private theorem constantTorsorBaseChangeEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q)
    (b : B) (t : constantTorsorAlgebra (G := G) q) :
    constantTorsorBaseChangeEquiv (G := G) q hq (b ⊗ₜ[A] t) =
      algebraMap B (ConstantCoordinates B G) b * t.1 := by
  change constantTorsorBaseChangeEquiv (G := G) q hq
      ((algebraMap B (B ⊗[A] constantTorsorAlgebra (G := G) q) b) *
        (Algebra.TensorProduct.includeRight :
          constantTorsorAlgebra (G := G) q →ₐ[A]
            B ⊗[A] constantTorsorAlgebra (G := G) q) t) = _
  rw [map_mul, (constantTorsorBaseChangeEquiv (G := G) q hq).commutes,
    constantTorsorBaseChangeEquiv_includeRight (G := G) q hq t]

private theorem constantTorsorAlgebra_finite
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    Module.Finite A (constantTorsorAlgebra (G := G) q) := by
  let e := constantTorsorBaseChangeEquiv (G := G) q hq
  letI : Module.Finite B (ConstantCoordinates B G) := inferInstance
  letI : Module.Finite B
      (B ⊗[A] constantTorsorAlgebra (G := G) q) :=
    (Module.Finite.equiv_iff e.toLinearEquiv).mpr inferInstance
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

private theorem constantTorsorAlgebra_etale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (q : ConstantCoordinates A G →ₐ[A] PairAlgebra A B)
    (hq : IsConstantCechCocycle (G := G) q) :
    Algebra.Etale A (constantTorsorAlgebra (G := G) q) := by
  let e := constantTorsorBaseChangeEquiv (G := G) q hq
  letI : Algebra.Etale B (G → B) := inferInstance
  letI : Algebra.Etale B (ConstantCoordinates B G) :=
    Algebra.Etale.of_equiv (ULift.algEquiv (R := B)).symm
  letI : Algebra.Etale B
      (B ⊗[A] constantTorsorAlgebra (G := G) q) :=
    Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat B

private theorem constantTorsorAlgebra_nontrivial
    {G₀ B : Type} [CommGroup G₀] [Fintype G₀]
    [CommRing B]
    [Module.FaithfullyFlat ℤ B]
    (q : ConstantCoordinates ℤ G₀ →ₐ[ℤ] PairAlgebra ℤ B)
    (hq : IsConstantCechCocycle (G := G₀) q) :
    Nontrivial (constantTorsorAlgebra (G := G₀) q) := by
  letI : Nontrivial B :=
    (FaithfulSMul.algebraMap_injective ℤ B).nontrivial
  letI : Nontrivial (ConstantCoordinates B G₀) := inferInstance
  let e := constantTorsorBaseChangeEquiv (G := G₀) q hq
  letI : Nontrivial (B ⊗[ℤ] constantTorsorAlgebra (G := G₀) q) :=
    e.toEquiv.nontrivial
  exact
    (Algebra.TensorProduct.includeRight :
      constantTorsorAlgebra (G := G₀) q →ₐ[ℤ]
        B ⊗[ℤ] constantTorsorAlgebra (G := G₀) q).toRingHom.domain_nontrivial

/-- The descended finite-etale constant torsor over the integers has an actual integral
section. -/
private noncomputable def constantTorsorSection
    {G₀ B : Type} [CommGroup G₀] [Fintype G₀]
    [CommRing B]
    [Module.FaithfullyFlat ℤ B]
    (q : ConstantCoordinates ℤ G₀ →ₐ[ℤ] PairAlgebra ℤ B)
    (hq : IsConstantCechCocycle (G := G₀) q) :
    constantTorsorAlgebra (G := G₀) q →ₐ[ℤ] ℤ := by
  letI : Module.Finite ℤ (constantTorsorAlgebra (G := G₀) q) :=
    constantTorsorAlgebra_finite (G := G₀) q hq
  letI hEtaleT : Algebra.Etale ℤ (constantTorsorAlgebra (G := G₀) q) :=
    constantTorsorAlgebra_etale (G := G₀) q hq
  letI : Nontrivial (constantTorsorAlgebra (G := G₀) q) :=
    constantTorsorAlgebra_nontrivial (G₀ := G₀) q hq
  letI : Module.Flat ℤ (constantTorsorAlgebra (G := G₀) q) :=
    Algebra.Smooth.flat ℤ _
  letI : Module.IsTorsionFree ℤ (constantTorsorAlgebra (G := G₀) q) :=
    Module.Flat.isTorsionFree
  letI : Module.Free ℤ (constantTorsorAlgebra (G := G₀) q) :=
    Module.free_of_finite_type_torsion_free'
  have hAlgebra :
      (inferInstance : Algebra ℤ (constantTorsorAlgebra (G := G₀) q)) =
        Ring.toIntAlgebra (constantTorsorAlgebra (G := G₀) q) :=
    Subsingleton.elim _ _
  letI : @Algebra.Etale ℤ (constantTorsorAlgebra (G := G₀) q) _ _
      (Ring.toIntAlgebra (constantTorsorAlgebra (G := G₀) q)) :=
    hAlgebra ▸ hEtaleT
  exact (exists_intAlgHom (constantTorsorAlgebra (G := G₀) q)
    (Module.finrank_pos (R := ℤ))).some

private noncomputable def baseChangedTorsorSection
    {A B T : Type} [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] (s : T →ₐ[A] A) :
    B ⊗[A] T →ₐ[B] B :=
  AlgHom.liftEquiv A B T B ((Algebra.ofId A B).comp s)

/-- The local represented character selected by the integral section of the descended torsor. -/
private noncomputable def constantTorsorGaugeCharacter
    {G₀ B : Type} [CommGroup G₀] [Fintype G₀]
    [CommRing B]
    [Module.FaithfullyFlat ℤ B]
    (q : ConstantCoordinates ℤ G₀ →ₐ[ℤ] PairAlgebra ℤ B)
    (hq : IsConstantCechCocycle (G := G₀) q) :
    ConstantCoordinates B G₀ →ₐ[B] B :=
  (baseChangedTorsorSection (B := B)
    (constantTorsorSection (G₀ := G₀) q hq)).comp
    (constantTorsorBaseChangeEquiv (G := G₀) q hq).symm.toAlgHom

private theorem constantTorsorGaugeCharacter_val_apply
    {G₀ B : Type} [CommGroup G₀] [Fintype G₀]
    [CommRing B]
    [Module.FaithfullyFlat ℤ B]
    (q : ConstantCoordinates ℤ G₀ →ₐ[ℤ] PairAlgebra ℤ B)
    (hq : IsConstantCechCocycle (G := G₀) q)
    (t : constantTorsorAlgebra (G := G₀) q) :
    constantTorsorGaugeCharacter q hq t.1 =
      algebraMap ℤ B (constantTorsorSection (G₀ := G₀) q hq t) := by
  rw [← constantTorsorBaseChangeEquiv_includeRight (G := G₀) q hq t]
  simp [constantTorsorGaugeCharacter, baseChangedTorsorSection]

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale
