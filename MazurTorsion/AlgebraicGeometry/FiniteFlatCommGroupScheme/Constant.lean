/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.TensorProduct.Pi
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Affine

/-!
# Constant finite commutative group schemes

For a finite commutative group `G`, the constant group scheme over `R` has coordinate algebra
the finite product `R^G`.  Its Hopf structure is pullback along the structure maps of `G`:

* `Δ(f)(a,b) = f(a*b)`,
* `ε(f) = f(1)`, and
* `S(f)(a) = f(a⁻¹)`.

We use a universe-preserving `ULift` of the function ring.  Besides preventing an accidental
collision with Mathlib's unrelated direct-product coalgebra instance, this keeps the coordinate
algebra in the universe required by `AffineCommGroupScheme`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj
open WithConv

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

universe u

/-- Coordinates of the constant scheme on `G`: a universe-preserving copy of `R^G`. -/
abbrev ConstantCoordinates (R : Type u) (G : Type u) := ULift.{0} (G → R)

namespace ConstantCoordinates

variable {R : Type u} [CommRing R] {G : Type u} [CommGroup G] [Fintype G]

/-- Uncurry a two-variable function, with the order adapted to `piScalarRight`. -/
def uncurryAlgEquiv : (G → G → R) ≃ₐ[R] (G × G → R) where
  toFun f p := f p.2 p.1
  invFun f b a := f (a, b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Evaluate a tensor of functions on a pair.  On pure tensors this is
`tensorEval (x ⊗ y) (a,b) = x(a) * y(b)`. -/
def tensorEval :
    ConstantCoordinates R G ⊗[R] ConstantCoordinates R G ≃ₐ[R] (G × G → R) := by
  classical
  exact (Algebra.TensorProduct.congr ULift.algEquiv ULift.algEquiv).trans <|
    (Algebra.TensorProduct.piScalarRight R R (G → R) G).trans uncurryAlgEquiv

omit [CommGroup G] in
@[simp]
theorem tensorEval_tmul (x y : ConstantCoordinates R G) (a b : G) :
    tensorEval (R := R) (G := G) (x ⊗ₜ[R] y) (a, b) = x.down a * y.down b := by
  change y.down b • x.down a = x.down a * y.down b
  simp [smul_eq_mul, mul_comm]

/-- Pull functions back along multiplication in `G`. -/
def mulPullbackAlgHom : ConstantCoordinates R G →ₐ[R] (G × G → R) where
  toFun f p := f.down (p.1 * p.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The comultiplication of the coordinate Hopf algebra of a constant group. -/
def comulAlgHom : ConstantCoordinates R G →ₐ[R]
    ConstantCoordinates R G ⊗[R] ConstantCoordinates R G :=
  tensorEval.symm.toAlgHom.comp mulPullbackAlgHom

@[simp]
theorem tensorEval_comulAlgHom (f : ConstantCoordinates R G) (a b : G) :
    tensorEval (R := R) (G := G)
      (comulAlgHom (R := R) (G := G) f) (a, b) = f.down (a * b) := by
  change tensorEval (R := R) (G := G)
      ((tensorEval (R := R) (G := G)).symm (mulPullbackAlgHom f)) (a, b) = _
  exact congrArg (fun q : G × G → R ↦ q (a, b))
    ((tensorEval (R := R) (G := G)).apply_symm_apply (mulPullbackAlgHom f))

/-- Pull functions back along the identity element of `G`. -/
def counitAlgHom : ConstantCoordinates R G →ₐ[R] R where
  toFun f := f.down 1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype G] in
@[simp]
theorem counitAlgHom_apply (f : ConstantCoordinates R G) :
    counitAlgHom (R := R) (G := G) f = f.down 1 := rfl

/-- Pull functions back along inversion in `G`. -/
def antipodeAlgHom : ConstantCoordinates R G →ₐ[R] ConstantCoordinates R G where
  toFun f := ULift.up (fun g ↦ f.down g⁻¹)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype G] in
@[simp]
theorem antipodeAlgHom_down_apply (f : ConstantCoordinates R G) (g : G) :
    (antipodeAlgHom f).down g = f.down g⁻¹ := rfl

/-- Evaluation at a group element, viewed as a point of the affine constant scheme. -/
def evaluation (g : G) : ConstantCoordinates R G →ₐ[R] R where
  toFun f := f.down g
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [CommGroup G] [Fintype G] in
@[simp]
theorem evaluation_apply (g : G) (f : ConstantCoordinates R G) :
    evaluation (R := R) g f = f.down g := rfl

/-- Pull functions back along a homomorphism of the indexing groups. -/
def pullbackAlgHom {H : Type u} [CommGroup H] (f : G →* H) :
    ConstantCoordinates R H →ₐ[R] ConstantCoordinates R G where
  toFun x := ULift.up (fun g ↦ x.down (f g))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype G] in
@[simp]
theorem pullbackAlgHom_down_apply {H : Type u} [CommGroup H]
    (f : G →* H) (x : ConstantCoordinates R H) (g : G) :
    (pullbackAlgHom (R := R) f x).down g = x.down (f g) := rfl

omit [Fintype G] in
/-- Over a nonzero base ring, pullback on the function algebra remembers the indexing map. -/
theorem pullbackAlgHom_injective [Nontrivial R]
    {H : Type u} [CommGroup H] {f g : G →* H}
    (h : pullbackAlgHom (R := R) f = pullbackAlgHom (R := R) g) : f = g := by
  classical
  apply MonoidHom.ext
  intro x
  by_contra hne
  let δ : ConstantCoordinates R H :=
    ULift.up (fun y ↦ if y = f x then 1 else 0)
  have heq := congrArg (fun z : ConstantCoordinates R G ↦ z.down x)
    (DFunLike.congr_fun h δ)
  have hzero : (1 : R) = 0 := by
    change (if f x = f x then 1 else 0) = (if g x = f x then 1 else 0) at heq
    rw [if_pos rfl, if_neg (Ne.symm hne)] at heq
    exact heq
  exact one_ne_zero hzero

omit [CommGroup G] in
/-- Tensoring two evaluation maps is evaluation on the corresponding ordered pair. -/
theorem lift_evaluation_evaluation (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G)
    (g h : G) :
    Algebra.TensorProduct.lift (evaluation (R := R) g) (evaluation (R := R) h)
        (fun _ _ ↦ Commute.all _ _) t =
      tensorEval (R := R) (G := G) t (g, h) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.lift_tmul, tensorEval_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

/-- Tensor evaluation is natural under pullback along a group homomorphism. -/
theorem tensorEval_map_pullback {H : Type u} [CommGroup H] [Fintype H]
    (f : G →* H)
    (t : ConstantCoordinates R H ⊗[R] ConstantCoordinates R H) (g h : G) :
    tensorEval (R := R) (G := G)
        (Algebra.TensorProduct.map (pullbackAlgHom (R := R) f)
          (pullbackAlgHom (R := R) f) t) (g, h) =
      tensorEval (R := R) (G := H) t (f g, f h) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.map_tmul, tensorEval_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Uncurry a function on a pair and one further variable. -/
def uncurryTripleAlgEquiv : ((G × G) → G → R) ≃ₐ[R] (G × (G × G) → R) where
  toFun f p := f p.2 p.1
  invFun f bc a := f (a, bc)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Evaluate a right-associated triple tensor on three group elements. -/
def rightTripleEval :
    ConstantCoordinates R G ⊗[R]
        (ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) ≃ₐ[R]
      (G × (G × G) → R) := by
  classical
  exact (Algebra.TensorProduct.congr ULift.algEquiv
      (tensorEval (R := R) (G := G))).trans <|
    (Algebra.TensorProduct.piScalarRight R R (G → R) (G × G)).trans
      uncurryTripleAlgEquiv

omit [CommGroup G] in
@[simp]
theorem rightTripleEval_tmul (x : ConstantCoordinates R G)
    (y : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (a b c : G) :
    rightTripleEval (R := R) (G := G) (x ⊗ₜ[R] y) (a, (b, c)) =
      x.down a * tensorEval (R := R) (G := G) y (b, c) := by
  change tensorEval (R := R) (G := G) y (b, c) • x.down a = _
  simp [smul_eq_mul, mul_comm]

omit [CommGroup G] in
@[simp]
theorem rightTripleEval_assoc_tmul
    (x : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G)
    (y : ConstantCoordinates R G) (a b c : G) :
    rightTripleEval (R := R) (G := G)
        (Algebra.TensorProduct.assoc R R R _ _ _ (x ⊗ₜ[R] y)) (a, (b, c)) =
      tensorEval (R := R) (G := G) x (a, b) * y.down c := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [Algebra.TensorProduct.assoc_tmul, mul_assoc]
  | add x y hx hy =>
      simp only [TensorProduct.add_tmul, map_add, Pi.add_apply, hx, hy, add_mul]

/-- Evaluating `Δ ⊗ id` amounts to multiplying the first two input coordinates. -/
theorem rightTripleEval_assoc_map_comul_id
    (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (a b c : G) :
    rightTripleEval (R := R) (G := G)
        ((Algebra.TensorProduct.assoc R R R _ _ _).toAlgHom
          (Algebra.TensorProduct.map (comulAlgHom (R := R) (G := G))
            (.id R _) t)) (a, (b, c)) =
      tensorEval (R := R) (G := G) t (a * b, c) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [Algebra.TensorProduct.map_tmul, tensorEval_comulAlgHom]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Evaluating `id ⊗ Δ` amounts to multiplying the last two input coordinates. -/
theorem rightTripleEval_map_id_comul
    (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (a b c : G) :
    rightTripleEval (R := R) (G := G)
        (Algebra.TensorProduct.map (.id R _)
          (comulAlgHom (R := R) (G := G)) t) (a, (b, c)) =
      tensorEval (R := R) (G := G) t (a, b * c) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [Algebra.TensorProduct.map_tmul, tensorEval_comulAlgHom]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Applying the left unit isomorphism after `ε ⊗ id` evaluates a tensor at `(1,g)`. -/
theorem lid_map_counit_id_down_apply
    (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (g : G) :
    ((Algebra.TensorProduct.lid R (ConstantCoordinates R G))
      (Algebra.TensorProduct.map (counitAlgHom (R := R) (G := G))
        (.id R _) t)).down g =
      tensorEval (R := R) (G := G) t (1, g) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [Algebra.TensorProduct.map_tmul, smul_eq_mul]
  | add x y hx hy => simp only [map_add, ULift.add_down, Pi.add_apply, hx, hy]

/-- Applying the right unit isomorphism after `id ⊗ ε` evaluates a tensor at `(g,1)`. -/
theorem rid_map_id_counit_down_apply
    (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (g : G) :
    ((Algebra.TensorProduct.rid R R (ConstantCoordinates R G))
      (Algebra.TensorProduct.map (.id R _)
        (counitAlgHom (R := R) (G := G)) t)).down g =
      tensorEval (R := R) (G := G) t (g, 1) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [Algebra.TensorProduct.map_tmul, smul_eq_mul, mul_comm]
  | add x y hx hy => simp only [map_add, ULift.add_down, Pi.add_apply, hx, hy]

/-- Coassociativity of pullback along the group multiplication. -/
theorem comulAlgHom_coassoc :
    (Algebra.TensorProduct.assoc R R R
        (ConstantCoordinates R G) (ConstantCoordinates R G) (ConstantCoordinates R G)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom (R := R) (G := G)) (.id R _)).comp
        (comulAlgHom (R := R) (G := G))) =
    (Algebra.TensorProduct.map (.id R _) (comulAlgHom (R := R) (G := G))).comp
      (comulAlgHom (R := R) (G := G)) := by
  apply AlgHom.ext
  intro f
  apply (rightTripleEval (R := R) (G := G)).injective
  funext p
  rcases p with ⟨a, b, c⟩
  simp only [AlgHom.comp_apply]
  calc
    rightTripleEval (R := R) (G := G)
        ((Algebra.TensorProduct.assoc R R R _ _ _).toAlgHom
          (Algebra.TensorProduct.map (comulAlgHom (R := R) (G := G))
            (.id R _) (comulAlgHom (R := R) (G := G) f))) (a, (b, c)) =
        tensorEval (R := R) (G := G)
          (comulAlgHom (R := R) (G := G) f) (a * b, c) := by
            simpa only using rightTripleEval_assoc_map_comul_id
              (R := R) (G := G) (comulAlgHom (R := R) (G := G) f) a b c
    _ = f.down ((a * b) * c) := tensorEval_comulAlgHom _ _ _
    _ = f.down (a * (b * c)) := by rw [mul_assoc]
    _ = tensorEval (R := R) (G := G)
          (comulAlgHom (R := R) (G := G) f) (a, b * c) :=
        (tensorEval_comulAlgHom _ _ _).symm
    _ = rightTripleEval (R := R) (G := G)
          (Algebra.TensorProduct.map (.id R _)
            (comulAlgHom (R := R) (G := G))
              (comulAlgHom (R := R) (G := G) f)) (a, (b, c)) :=
        (rightTripleEval_map_id_comul _ _ _ _).symm

/-- Left counitality of pullback along multiplication. -/
theorem comulAlgHom_rTensor_counit :
    (Algebra.TensorProduct.map (counitAlgHom (R := R) (G := G)) (.id R _)).comp
        (comulAlgHom (R := R) (G := G)) =
      (Algebra.TensorProduct.lid R (ConstantCoordinates R G)).symm.toAlgHom := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.lid R (ConstantCoordinates R G)).injective
  simp only [AlgHom.comp_apply]
  calc
    (Algebra.TensorProduct.lid R (ConstantCoordinates R G))
        (Algebra.TensorProduct.map (counitAlgHom (R := R) (G := G)) (.id R _)
          (comulAlgHom (R := R) (G := G) f)) = f := by
      apply ULift.down_injective
      funext g
      rw [lid_map_counit_id_down_apply, tensorEval_comulAlgHom, one_mul]
    _ = (Algebra.TensorProduct.lid R (ConstantCoordinates R G))
        ((Algebra.TensorProduct.lid R (ConstantCoordinates R G)).symm f) :=
      ((Algebra.TensorProduct.lid R (ConstantCoordinates R G)).apply_symm_apply f).symm

/-- Right counitality of pullback along multiplication. -/
theorem comulAlgHom_lTensor_counit :
    (Algebra.TensorProduct.map (.id R _) (counitAlgHom (R := R) (G := G))).comp
        (comulAlgHom (R := R) (G := G)) =
      (Algebra.TensorProduct.rid R R (ConstantCoordinates R G)).symm.toAlgHom := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.rid R R (ConstantCoordinates R G)).injective
  simp only [AlgHom.comp_apply]
  calc
    (Algebra.TensorProduct.rid R R (ConstantCoordinates R G))
        (Algebra.TensorProduct.map (.id R _) (counitAlgHom (R := R) (G := G))
          (comulAlgHom (R := R) (G := G) f)) = f := by
      apply ULift.down_injective
      funext g
      rw [rid_map_id_counit_down_apply, tensorEval_comulAlgHom, mul_one]
    _ = (Algebra.TensorProduct.rid R R (ConstantCoordinates R G))
        ((Algebra.TensorProduct.rid R R (ConstantCoordinates R G)).symm f) :=
      ((Algebra.TensorProduct.rid R R (ConstantCoordinates R G)).apply_symm_apply f).symm

/-- The bialgebra structure on functions on a finite group. -/
instance instBialgebra : Bialgebra R (ConstantCoordinates R G) :=
  Bialgebra.ofAlgHom (comulAlgHom (R := R) (G := G))
    (counitAlgHom (R := R) (G := G)) comulAlgHom_coassoc
    comulAlgHom_rTensor_counit comulAlgHom_lTensor_counit

@[simp]
theorem bialgebra_comulAlgHom :
    Bialgebra.comulAlgHom R (ConstantCoordinates R G) =
      comulAlgHom (R := R) (G := G) := rfl

@[simp]
theorem bialgebra_counitAlgHom :
    Bialgebra.counitAlgHom R (ConstantCoordinates R G) =
      counitAlgHom (R := R) (G := G) := rfl

/-- Multiplication after applying inversion in the first tensor coordinate evaluates at
`(g⁻¹,g)`. -/
theorem lift_antipode_id_down_apply
    (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (g : G) :
    ((Algebra.TensorProduct.lift (antipodeAlgHom (R := R) (G := G)) (.id R _)
      (fun _ _ ↦ Commute.all _ _)) t).down g =
      tensorEval (R := R) (G := G) t (g⁻¹, g) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [Algebra.TensorProduct.lift_tmul, tensorEval_tmul]
  | add x y hx hy => simp only [map_add, ULift.add_down, Pi.add_apply, hx, hy]

/-- Multiplication after applying inversion in the second tensor coordinate evaluates at
`(g,g⁻¹)`. -/
theorem lift_id_antipode_down_apply
    (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (g : G) :
    ((Algebra.TensorProduct.lift (.id R _) (antipodeAlgHom (R := R) (G := G))
      (fun _ _ ↦ Commute.all _ _)) t).down g =
      tensorEval (R := R) (G := G) t (g, g⁻¹) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp [Algebra.TensorProduct.lift_tmul, tensorEval_tmul]
  | add x y hx hy => simp only [map_add, ULift.add_down, Pi.add_apply, hx, hy]

/-- The first antipode identity for functions on a group. -/
theorem antipodeAlgHom_mul_left :
    ((Algebra.TensorProduct.lift (antipodeAlgHom (R := R) (G := G)) (.id R _)
      (fun _ _ ↦ Commute.all _ _)).comp
        (Bialgebra.comulAlgHom R (ConstantCoordinates R G))) =
      (Algebra.ofId R (ConstantCoordinates R G)).comp
        (Bialgebra.counitAlgHom R (ConstantCoordinates R G)) := by
  apply AlgHom.ext
  intro f
  apply ULift.down_injective
  funext g
  simp only [AlgHom.comp_apply, bialgebra_comulAlgHom, bialgebra_counitAlgHom]
  rw [lift_antipode_id_down_apply, tensorEval_comulAlgHom, inv_mul_cancel]
  simp [Algebra.ofId_apply]

/-- The second antipode identity for functions on a group. -/
theorem antipodeAlgHom_mul_right :
    ((Algebra.TensorProduct.lift (.id R _) (antipodeAlgHom (R := R) (G := G))
      (fun _ _ ↦ Commute.all _ _)).comp
        (Bialgebra.comulAlgHom R (ConstantCoordinates R G))) =
      (Algebra.ofId R (ConstantCoordinates R G)).comp
        (Bialgebra.counitAlgHom R (ConstantCoordinates R G)) := by
  apply AlgHom.ext
  intro f
  apply ULift.down_injective
  funext g
  simp only [AlgHom.comp_apply, bialgebra_comulAlgHom, bialgebra_counitAlgHom]
  rw [lift_id_antipode_down_apply, tensorEval_comulAlgHom, mul_inv_cancel]
  simp [Algebra.ofId_apply]

/-- The Hopf algebra structure on functions on a finite group. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R (ConstantCoordinates R G) :=
  HopfAlgebra.ofAlgHom (antipodeAlgHom (R := R) (G := G))
    antipodeAlgHom_mul_left antipodeAlgHom_mul_right

/-- Pullback along a group homomorphism is a morphism of the function Hopf algebras. -/
def pullbackBialgHom {H : Type u} [CommGroup H] [Fintype H] (f : G →* H) :
    ConstantCoordinates R H →ₐc[R] ConstantCoordinates R G :=
  BialgHom.ofAlgHom (pullbackAlgHom (R := R) f) (by
    apply AlgHom.ext
    intro x
    change x.down (f 1) = x.down 1
    rw [map_one]) (by
    apply AlgHom.ext
    intro x
    apply (tensorEval (R := R) (G := G)).injective
    funext p
    rcases p with ⟨g, h⟩
    simp only [AlgHom.comp_apply, bialgebra_comulAlgHom]
    rw [tensorEval_map_pullback, tensorEval_comulAlgHom, tensorEval_comulAlgHom]
    change x.down (f g * f h) = x.down (f (g * h))
    rw [map_mul])

/-- Distinguished affine points of the constant scheme multiply as the underlying group does. -/
theorem evaluation_convMul (g h : G) :
    toConv (evaluation (R := R) g) * toConv (evaluation (R := R) h) =
      toConv (evaluation (R := R) (g * h)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro f
  rw [AlgHom.convMul_apply]
  change Algebra.TensorProduct.lift (evaluation (R := R) g) (evaluation (R := R) h)
      (fun _ _ ↦ Commute.all _ _)
        (comulAlgHom (R := R) (G := G) f) = f.down (g * h)
  rw [lift_evaluation_evaluation, tensorEval_comulAlgHom]

omit [CommGroup G] in
/-- Swapping tensor factors swaps the two evaluation coordinates. -/
theorem tensorEval_comm
    (t : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G) (a b : G) :
    tensorEval (R := R) (G := G)
        (TensorProduct.comm R _ _ t) (a, b) =
      tensorEval (R := R) (G := G) t (b, a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.comm_tmul, tensorEval_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- The coordinate Hopf algebra is cocommutative when `G` is commutative. -/
instance instIsCocomm : Coalgebra.IsCocomm R (ConstantCoordinates R G) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro f
    apply (tensorEval (R := R) (G := G)).injective
    funext p
    rcases p with ⟨a, b⟩
    change tensorEval (R := R) (G := G)
        (TensorProduct.comm R _ _ (comulAlgHom (R := R) (G := G) f)) (a, b) =
      tensorEval (R := R) (G := G) (comulAlgHom (R := R) (G := G) f) (a, b)
    rw [tensorEval_comm, tensorEval_comulAlgHom, tensorEval_comulAlgHom, mul_comm]

end ConstantCoordinates

/-- The finite-free affine constant group scheme on a finite commutative group `G`. -/
def constant (R : Type u) [CommRing R] (G : Type u) [CommGroup G] [Fintype G] :
    AffineFiniteFreeCommGroupScheme R where
  obj := Opposite.op
    ⟨CommHopfAlgCat.of R (ConstantCoordinates R G), by
      change Coalgebra.IsCocomm R (ConstantCoordinates R G)
      infer_instance⟩
  property := by
    change Module.Free R (ConstantCoordinates R G) ∧
      Module.Finite R (ConstantCoordinates R G)
    constructor <;> infer_instance

/-- A group homomorphism induces the corresponding morphism of constant affine group schemes. -/
def constantMapAffine (R : Type u) [CommRing R]
    {G H : Type u} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H]
    (f : G →* H) : constant R G ⟶ constant R H :=
  CategoryTheory.ObjectProperty.homMk <| (CategoryTheory.ObjectProperty.homMk <|
    CommHopfAlgCat.ofHom (ConstantCoordinates.pullbackBialgHom (R := R) f)).op

@[simp]
theorem constantMapAffine_coordinateMap (R : Type u) [CommRing R]
    {G H : Type u} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H]
    (f : G →* H) :
    AffineCommGroupScheme.coordinateMap (constantMapAffine R f).hom =
      ConstantCoordinates.pullbackBialgHom (R := R) f :=
  rfl

@[simp]
theorem constantMapAffine_comp (R : Type u) [CommRing R]
    {G H K : Type u} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H]
    [CommGroup K] [Fintype K] (f : G →* H) (g : H →* K) :
    constantMapAffine R (g.comp f) =
      (constantMapAffine R f ≫ constantMapAffine R g) := by
  rfl

/-- Over a nonzero base ring, the constant affine group-scheme construction is faithful. -/
theorem constantMapAffine_injective (R : Type u) [CommRing R] [Nontrivial R]
    {G H : Type u} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H] :
    Function.Injective
      (constantMapAffine R : (G →* H) → (constant R G ⟶ constant R H)) := by
  intro f g h
  apply ConstantCoordinates.pullbackAlgHom_injective (R := R)
  have hb := congrArg
    (fun q : constant R G ⟶ constant R H ↦
      AffineCommGroupScheme.coordinateMap q.hom) h
  exact congrArg BialgHom.toAlgHom hb

/-- The geometric realization of the constant finite group scheme. -/
abbrev constantScheme (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] :
    FiniteFlatCommGroupScheme (Spec (.of R)) :=
  (constant R G).realize

/-- The geometric morphism of constant finite-flat group schemes induced by a group homomorphism. -/
def constantMap (R : Type u) [CommRing R]
    {G H : Type u} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H]
    (f : G →* H) : constantScheme R G ⟶ constantScheme R H :=
  (AffineFiniteFreeCommGroupScheme.realizationFunctor R).map (constantMapAffine R f)

/-- The geometric constant-group construction respects composition.  This is a concrete
downstream consumer of the finite-free realization functor's composition law. -/
@[simp]
theorem constantMap_comp (R : Type u) [CommRing R]
    {G H K : Type u} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H]
    [CommGroup K] [Fintype K] (f : G →* H) (g : H →* K) :
    constantMap R (g.comp f) = constantMap R f ≫ constantMap R g := by
  rw [constantMap, constantMapAffine_comp,
    AffineFiniteFreeCommGroupScheme.realizationFunctor_map,
    AffineFiniteFreeCommGroupScheme.realizeMap_comp]
  rfl

/-- Scalar extension commutes with the function-ring coordinates of a finite constant group.
On a pure tensor, this sends `s ⊗ f` to the function `g ↦ algebraMap R K (f g) * s`. -/
def constantBaseChangeAlgEquiv
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G] :
    K ⊗[R] ConstantCoordinates R G ≃ₐ[K] ConstantCoordinates K G := by
  classical
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) ULift.algEquiv).trans <|
    (Algebra.TensorProduct.piScalarRight R K K G).trans ULift.algEquiv.symm

@[simp]
theorem constantBaseChangeAlgEquiv_tmul
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G]
    (s : K) (f : ConstantCoordinates R G) (g : G) :
    (constantBaseChangeAlgEquiv (R := R) (K := K) G (s ⊗ₜ[R] f)).down g =
      algebraMap R K (f.down g) * s := by
  classical
  simp [constantBaseChangeAlgEquiv, Algebra.TensorProduct.piScalarRight_tmul,
    Algebra.smul_def, mul_comm]

private theorem constantBaseChange_tensorEval_comulAux
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G]
    (s : K) (q : ConstantCoordinates R G ⊗[R] ConstantCoordinates R G)
    (g h : G) :
    ConstantCoordinates.tensorEval (R := K) (G := G)
        (TensorProduct.map
          (constantBaseChangeAlgEquiv (R := R) (K := K) G).toLinearMap
          (constantBaseChangeAlgEquiv (R := R) (K := K) G).toLinearMap
          ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
            R K R K K K (ConstantCoordinates R G) (ConstantCoordinates R G))
              (1 ⊗ₜ[K] s ⊗ₜ[R] q))) (g, h) =
      algebraMap R K
          (ConstantCoordinates.tensorEval (R := R) (G := G) q (g, h)) * s := by
  classical
  induction q using TensorProduct.induction_on with
  | zero =>
      simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
      rw [map_zero, map_zero]
      change (0 : K) = algebraMap R K 0 * s
      simp
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, hx, hy, add_mul]
  | tmul x y =>
      simp [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        ConstantCoordinates.tensorEval_tmul, constantBaseChangeAlgEquiv_tmul,
        map_mul, mul_assoc]

/-- The scalar-extension equivalence for constant coordinates respects the full bialgebra
structure, hence also the Hopf structure. -/
def constantBaseChangeBialgEquiv
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G] :
    K ⊗[R] ConstantCoordinates R G ≃ₐc[K] ConstantCoordinates K G := by
  classical
  let e := constantBaseChangeAlgEquiv (R := R) (K := K) G
  let c : K ⊗[R] ConstantCoordinates R G ≃ₗc[K] ConstantCoordinates K G :=
    { e.toLinearEquiv with
      counit_comp := by
        apply LinearMap.ext
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul s f =>
            rw [TensorProduct.counit_tmul]
            change (e (s ⊗ₜ[R] f)).down 1 = _
            rw [constantBaseChangeAlgEquiv_tmul]
            change algebraMap R K (f.down 1) * s = f.down 1 • s
            rw [Algebra.smul_def]
      map_comp_comul := by
        apply LinearMap.ext
        intro t
        apply (ConstantCoordinates.tensorEval (R := K) (G := G)).injective
        funext p
        rcases p with ⟨g, h⟩
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
        | tmul s f =>
            simp only [LinearMap.comp_apply]
            rw [TensorProduct.comul_tmul]
            change ConstantCoordinates.tensorEval (R := K) (G := G)
                (TensorProduct.map e.toLinearMap e.toLinearMap
                  ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
                    R K R K K K (ConstantCoordinates R G) (ConstantCoordinates R G))
                      (1 ⊗ₜ[K] s ⊗ₜ[R]
                        Coalgebra.comul (R := R) (A := ConstantCoordinates R G) f))) (g, h) = _
            rw [constantBaseChange_tensorEval_comulAux]
            change algebraMap R K
                (ConstantCoordinates.tensorEval (R := R) (G := G)
                  (ConstantCoordinates.comulAlgHom (R := R) (G := G) f) (g, h)) * s = _
            rw [ConstantCoordinates.tensorEval_comulAlgHom]
            change algebraMap R K (f.down (g * h)) * s =
              ConstantCoordinates.tensorEval (R := K) (G := G)
                (ConstantCoordinates.comulAlgHom (R := K) (G := G) (e (s ⊗ₜ[R] f)))
                  (g, h)
            rw [ConstantCoordinates.tensorEval_comulAlgHom,
              constantBaseChangeAlgEquiv_tmul] }
  exact BialgEquiv.mk c e.map_mul

/-- Coordinate scalar extension of a constant affine group is canonically the named constant
affine group over the new base. -/
def constantAffineBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G] :
    (constant R G).baseChange (K := K) ≅ constant K G :=
  AffineFiniteFreeCommGroupScheme.isoOfCoordinateBialgEquiv
    (constantBaseChangeBialgEquiv (R := R) (K := K) G)

/-- Geometric base change of a constant finite group scheme agrees with scalar extension of
its function Hopf algebra. -/
noncomputable def constantRealizeBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G] :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (constantScheme R G) ≅
      ((constant R G).baseChange (K := K)).realize :=
  (constant R G).realizeBaseChangeIso

/-- Geometric base change of a constant finite group scheme is canonically the named constant
scheme over the new base. -/
noncomputable def constantBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G] :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (constantScheme R G) ≅ constantScheme K G :=
  constantRealizeBaseChangeIso (R := R) (K := K) G ≪≫
    (AffineFiniteFreeCommGroupScheme.realizationFunctor K).mapIso
      (constantAffineBaseChangeIso (R := R) (K := K) G)

/-- The named constant-family base-change isomorphism acts on points of every test scheme. -/
def constantBaseChangePointMulEquiv
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (G : Type u) [CommGroup G] [Fintype G] (X : Over (Spec (.of K))) :
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (constantScheme R G)).Point X ≃* (constantScheme K G).Point X :=
  pointMulEquivOfIso (constantBaseChangeIso (R := R) (K := K) G) X

/-- The geometric point of the constant group scheme selected by `g`. -/
def constantPoint (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] (g : G) :
    (constant R G).Point R :=
  ((constant R G).obj.pointMulEquiv R).symm
    (toConv (ConstantCoordinates.evaluation (R := R) g))

/-- The same distinguished point with its finite-flat geometric realization type exposed. -/
abbrev constantGeometricPoint (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] (g : G) :
    (constantScheme R G).Point (AffineCommGroupScheme.testObject (R := R) R) :=
  constantPoint R G g

@[simp]
theorem pointToAlgHom_constantPoint (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] (g : G) :
    (constant R G).obj.pointToAlgHom R (constantPoint R G g) =
      ConstantCoordinates.evaluation (R := R) g := by
  have h := ((constant R G).obj.pointMulEquiv R).apply_symm_apply
    (toConv (ConstantCoordinates.evaluation (R := R) g))
  rw [AffineCommGroupScheme.pointMulEquiv_apply] at h
  apply AlgHom.ext
  intro x
  exact congrArg (fun q : WithConv ((constant R G).coordinates →ₐ[R] R) ↦ q.ofConv x) h

/-- The geometric map of constant schemes acts on distinguished points by the original group
homomorphism. -/
@[simp]
theorem mapPoint_constantMap_constantPoint (R : Type u) [CommRing R]
    {G H : Type u} [CommGroup G] [Fintype G] [CommGroup H] [Fintype H]
    (f : G →* H) (g : G) :
    mapPoint (constantMap R f) (AffineCommGroupScheme.testObject (R := R) R)
        (constantGeometricPoint R G g) = constantGeometricPoint R H (f g) := by
  apply ((constant R H).realizePointMulEquiv R).injective
  rw [AffineFiniteFreeCommGroupScheme.realizePointMulEquiv_apply,
    AffineFiniteFreeCommGroupScheme.realizePointMulEquiv_apply]
  apply WithConv.ofConv_injective
  change (constant R H).obj.pointToAlgHom R
      (mapPoint (AffineFiniteFreeCommGroupScheme.realizeMap (constantMapAffine R f))
        (AffineCommGroupScheme.testObject (R := R) R) (constantGeometricPoint R G g)) =
    (constant R H).obj.pointToAlgHom R (constantGeometricPoint R H (f g))
  rw [AffineFiniteFreeCommGroupScheme.pointToAlgHom_map_realizeMap]
  rw [pointToAlgHom_constantPoint, pointToAlgHom_constantPoint]
  rfl

/-- The distinguished geometric points preserve the multiplication of `G`. -/
@[simp]
theorem constantPoint_mul (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] (g h : G) :
    constantPoint R G (g * h) = constantPoint R G g * constantPoint R G h := by
  apply ((constant R G).obj.pointMulEquiv R).injective
  rw [map_mul]
  simp only [constantPoint, MulEquiv.apply_symm_apply]
  exact (ConstantCoordinates.evaluation_convMul (R := R) g h).symm

/-- The standard basis of the coordinate ring `R^G`. -/
def ConstantCoordinates.basis (R : Type u) [CommRing R]
    (G : Type u) [CommGroup G] [Fintype G] :
    Module.Basis G R (ConstantCoordinates R G) :=
  (Pi.basisFun R G).map ULift.moduleEquiv.symm

/-- The finite-free coordinate rank of the constant group scheme is the cardinality of `G`. -/
@[simp]
theorem constant_order (R : Type u) [CommRing R] [Nontrivial R]
    (G : Type u) [CommGroup G] [Fintype G] :
    (constant R G).order = Fintype.card G := by
  change Module.finrank R (ConstantCoordinates R G) = Fintype.card G
  exact Module.finrank_eq_card_basis (ConstantCoordinates.basis R G)

/-- The geometric order function of a constant group scheme has the expected value. -/
@[simp]
theorem constantScheme_orderAt (R : Type u) [CommRing R] [Nontrivial R]
    (G : Type u) [CommGroup G] [Fintype G] (s : Spec (.of R)) :
    (constantScheme R G).orderAt s = Fintype.card G :=
  (constant R G).orderAt_eq_order s |>.trans (constant_order R G)

end FiniteFlatCommGroupScheme
end AlgebraicGeometry
