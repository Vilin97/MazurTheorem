/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Cartier duality and Deligne's order theorem (BB-DELIGNE)

This file develops the abstract Hopf-algebraic layer (Layer A of `plan-deligne.md`) of
**Deligne's theorem**: a finite locally free commutative group scheme of rank `N` is killed
by `N`. The route is Tate's, from J. Tate, *Finite flat group schemes* (in Cornell–Silverman–
Stevens, *Modular Forms and Fermat's Last Theorem*), §3.8, book pp. 143–145.

The mathematical content of §3.8, in the affine/Hopf-algebra picture `G = Spec A`, `R` the base
ring, `A` a finite locally free `R`-Hopf algebra of rank `n`:

* `A' := Hom_R(A, R)` is the **Cartier dual** — itself a commutative `R`-Hopf algebra when `A` is
  cocommutative (equivalently `G` commutative), finite locally free of the same rank `n`. In
  mathlib this convolution algebra is `WithConv (A →ₗ[R] R)` (`LinearMap.convAlgebra`, and
  `LinearMap.convCommRing` under `IsCocomm R A`).
* A `B`-point of `G`, i.e. an `R`-algebra map `A → B`, is a **group-like** element `λ` of
  `A'_B := WithConv (A →ₗ[R] B)` — a *unit* whose convolution powers `λ^k` are the multiples
  `k • Q` of the point. (Tate p. 144: "`G(R) = Hom_(R-alg)(A,R) ⊂ Hom_(R-mod)(A,R) = A'`
  identifies `G(R)` with the multiplicative group of group-like elements of `A'`.")
* The free rank-`n` left `A'`-module `A' ⊗_R A` carries operators `τ = id ⊗ τ_λ`, `ρ` (right
  mult by `id`), `ℓ` (right mult by `λ ⊗ 1`) with `τ ρ τ⁻¹ ρ⁻¹ = ℓ` (Prop 3.8.1), and `ℓ` is
  the scalar matrix `λ · Iₙ`.
* Since `A'` is commutative, `det : GLₙ(A') → (A')ˣ` kills the commutator, so
  `det(λ · Iₙ) = λⁿ = 1` (Tate p. 144). Equivalently `n • Q = 0`.

This file proves the pieces bottom-up. The determinant step (leaf **T-D5f**) is pure matrix
algebra over a commutative ring and is complete; the point↔convolution-unit dictionary
(**T-D5c**) and the Cartier-dual algebra (**T-D5a**) are discharged from mathlib's convolution
API; the operator/commutator package (**T-D5d/e**, Prop 3.8.1) and the final assembly
(**T-D5g**) remain. The geometric bridge (Layer B) lives in
`ModularCurves.GroupScheme.DeligneOrder`.

See `.mathlib-quality/plan-deligne.md` for the full ticket board and verbatim source quotes.
-/

open scoped Matrix TensorProduct
open HopfAlgebra Coalgebra WithConv

namespace ModularCurves.CartierDual

universe u v w

/-! ## Layer A leaf T-D5f — the determinant step

The determinant homomorphism `GLₙ(S) → Sˣ` over a *commutative* ring `S` kills commutators;
applied to the scalar matrix `λ · Iₙ = A B A⁻¹ B⁻¹` this gives `λⁿ = 1`. In Deligne's proof
`S = A'` is the (commutative) Cartier dual, `λ` the group-like element attached to a point,
and `n` the rank of `G` — so this leaf is exactly the last two sentences of Tate §3.8 (p. 144):
"we can use the determinant homomorphism `GLₙ(A') → (A')*` to conclude that `λⁿ = 1`." -/

/-- The determinant of a `unit` matrix and of its inverse multiply to `1`: `det ↑A · det ↑A⁻¹ = 1`.
A packaging of `Matrix.det_mul` + `Units.mul_inv` used repeatedly below. -/
theorem det_val_mul_det_val_inv {S : Type u} [CommRing S] {n : ℕ}
    (A : (Matrix (Fin n) (Fin n) S)ˣ) :
    (↑A : Matrix (Fin n) (Fin n) S).det * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det = 1 := by
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

/-- **(T-D5f — determinant step, Tate §3.8 p. 144.)** Over a commutative ring `S`, if the scalar
matrix `λ • Iₙ` is a commutator `A · B · A⁻¹ · B⁻¹` of invertible `n × n` matrices, then `λⁿ = 1`.

Proof: `det` is multiplicative and `S` is commutative, so `det(A B A⁻¹ B⁻¹) = 1`; and
`det(λ • Iₙ) = λⁿ` by `Matrix.det_smul`. This is the leaf discharged purely from mathlib
(`Matrix.det_smul`, `Matrix.det_mul`, `Matrix.det_one`, `Units.mul_inv`). -/
theorem pow_eq_one_of_smul_one_eq_commutator {S : Type u} [CommRing S] {n : ℕ}
    (lam : S) (A B : (Matrix (Fin n) (Fin n) S)ˣ)
    (h : lam • (1 : Matrix (Fin n) (Fin n) S) = ↑(A * B * A⁻¹ * B⁻¹)) :
    lam ^ n = 1 := by
  -- Take determinants of both sides.
  have key := congrArg Matrix.det h
  -- LHS: det (λ • 1) = λ ^ n.
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at key
  rw [key]
  -- RHS: det of the commutator is 1.
  simp only [Units.val_mul]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  -- goal: det↑A * det↑B * det↑A⁻¹ * det↑B⁻¹ = 1
  calc (↑A : Matrix (Fin n) (Fin n) S).det * (↑B : Matrix (Fin n) (Fin n) S).det
          * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det * (↑B⁻¹ : Matrix (Fin n) (Fin n) S).det
      = ((↑A : Matrix (Fin n) (Fin n) S).det * (↑A⁻¹ : Matrix (Fin n) (Fin n) S).det)
          * ((↑B : Matrix (Fin n) (Fin n) S).det * (↑B⁻¹ : Matrix (Fin n) (Fin n) S).det) := by
        ring
    _ = 1 * 1 := by rw [det_val_mul_det_val_inv, det_val_mul_det_val_inv]
    _ = 1 := by ring

/-- **(T-D5f′ — determinant step, endomorphism form.)** The same as
`pow_eq_one_of_smul_one_eq_commutator` but phrased with `LinearMap.det` on a free finite module
`M` (rank `n`), which is the form the geometric operators `τ, ρ, ℓ` of §3.8 naturally take: if
`λ • id_M` is a commutator `P Q P⁻¹ Q⁻¹` of `S`-linear automorphisms of `M`, then `λⁿ = 1`.

Proof: `LinearMap.det` is a monoid hom killing commutators over the commutative ring `S`, and
`det(λ • id_M) = λ^(finrank M) = λⁿ` (`LinearMap.det_smul`, `LinearMap.det_id`). -/
theorem pow_eq_one_of_smul_id_eq_commutator {S : Type u} [CommRing S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module.Free S M] [Module.Finite S M]
    {n : ℕ} (hn : Module.finrank S M = n) (lam : S)
    (P Q : (M →ₗ[S] M)ˣ)
    (h : lam • (LinearMap.id : M →ₗ[S] M) = ↑(P * Q * P⁻¹ * Q⁻¹)) :
    lam ^ n = 1 := by
  have key := congrArg LinearMap.det h
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hn] at key
  rw [key]
  have hP : LinearMap.det (↑P : M →ₗ[S] M) * LinearMap.det (↑P⁻¹ : M →ₗ[S] M) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hQ : LinearMap.det (↑Q : M →ₗ[S] M) * LinearMap.det (↑Q⁻¹ : M →ₗ[S] M) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, map_mul]
  calc LinearMap.det (↑P : M →ₗ[S] M) * LinearMap.det (↑Q : M →ₗ[S] M)
          * LinearMap.det (↑P⁻¹ : M →ₗ[S] M) * LinearMap.det (↑Q⁻¹ : M →ₗ[S] M)
      = (LinearMap.det (↑P : M →ₗ[S] M) * LinearMap.det (↑P⁻¹ : M →ₗ[S] M))
          * (LinearMap.det (↑Q : M →ₗ[S] M) * LinearMap.det (↑Q⁻¹ : M →ₗ[S] M)) := by ring
    _ = 1 := by rw [hP, hQ]; ring

/-! ## The Cartier dual algebra and points as group-like elements

We fix a commutative `R`-Hopf algebra `A` (`= 𝒪(G)`), cocommutative (`G` commutative), and a
test `R`-algebra `B`. Tate's `A'_B` is mathlib's `WithConv (A →ₗ[R] B)`: the convolution
algebra of `R`-linear maps `A → B`, whose product is dual to the comultiplication of `A`. -/

/-- **(T-D5a — Cartier dual algebra, Tate §3.8 p. 143.)** The Cartier dual `A' = Hom_R(A, R)`
(i.e. `Module.Dual R A`) with its convolution product, as a commutative `R`-algebra. This is
mathlib's `WithConv (A →ₗ[R] R)`; the instances `LinearMap.convAlgebra` and (under `IsCocomm R A`,
i.e. `G` commutative) `LinearMap.convCommRing` supply the `R`-algebra and commutativity. -/
abbrev _root_.ModularCurves.CartierDual (R : Type u) (A : Type v) [CommRing R] [AddCommGroup A]
    [Module R A] [Coalgebra R A] : Type max u v := WithConv (A →ₗ[R] R)

section Point

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- **(T-D5c — points as convolution elements, Tate §3.8 p. 144.)** A `B`-point `φ : A →ₐ[R] B`,
viewed in `A'_B = WithConv (A →ₗ[R] B)` as the group-like element `λ_φ`. The group law of
`G(B)` is convolution, so the `k`-th convolution power `(pointConv φ)^k` is `k • Q`. -/
def pointConv (φ : A →ₐ[R] B) : WithConv (A →ₗ[R] B) := toConv φ.toLinearMap

@[simp] lemma ofConv_pointConv (φ : A →ₐ[R] B) : ofConv (pointConv φ) = φ.toLinearMap := rfl

/-- The convolution inverse of a point is the point composed with the antipode: this is the
Hopf-algebra identity `∑ φ(a₍₁₎) · φ(S a₍₂₎) = φ(∑ a₍₁₎ · S a₍₂₎) = φ(ε(a) • 1) = ε_B(a)`,
i.e. `λ_φ · (λ_φ ∘ S) = 1` in `A'_B`. (Tate p. 144: "λ is group-like iff it is invertible in
`A'` and the map `λ : A → R` is multiplicative … invertible iff `λ(1) = 1`.") -/
theorem mul_pointConv_antipode_eq_one (φ : A →ₐ[R] B) :
    pointConv φ * toConv (φ.toLinearMap ∘ₗ antipode R) = 1 := by
  ext a
  rw [(ℛ R a).convMul_apply, LinearMap.convOne_apply]
  have hsum : ∀ i, (pointConv φ) ((ℛ R a).left i)
      * (toConv (φ.toLinearMap ∘ₗ antipode R)) ((ℛ R a).right i)
      = φ ((ℛ R a).left i * antipode R ((ℛ R a).right i)) :=
    fun i => by simp [pointConv, map_mul]
  simp only [hsum]
  rw [← map_sum φ, sum_mul_antipode_eq_algebraMap_counit (ℛ R a), AlgHom.commutes]

/-- **(T-D5c — corollary.)** A `B`-point `φ` is a *unit* in `A'_B` (its convolution inverse
being `φ ∘ S`). This is the statement that the points of `G` are group-like elements of `A'`,
in particular invertible — needed so `λ_φ · Iₙ ∈ GLₙ(A'_B)` in the determinant step. Requires
`G` commutative (`IsCocomm R A`) so that `A'_B` is a commutative ring. -/
theorem isUnit_pointConv [IsCocomm R A] (φ : A →ₐ[R] B) : IsUnit (pointConv φ) :=
  ⟨⟨pointConv φ, toConv (φ.toLinearMap ∘ₗ antipode R), mul_pointConv_antipode_eq_one φ,
    by rw [mul_comm]; exact mul_pointConv_antipode_eq_one φ⟩, rfl⟩

end Point

/-! ## The commutator package (Prop 3.8.1) and the final assembly — REMAINING

The heart of §3.8: on the free rank-`n` left `A'`-module `A' ⊗_R A`, the scalar `λ · Iₙ` is a
commutator, so `det` gives `λⁿ = 1`. Prop 3.8.1 (leaf T-D5e, itself resting on the operator
`τ_λ` of T-D5d) is stated in the concrete existential form the determinant step consumes; it is
`sorry` here and proved in its sub-tickets. The assembly `deligne_pointConv_pow` (T-D5g) then
combines it with `pow_eq_one_of_smul_one_eq_commutator`. -/

/-! ### General right-multiplication lemmas (Hopf-free)

The commutator computation of Prop 3.8.1 rests on two facts about right multiplication in a
commutative `S`-algebra `M`, neither involving Hopf algebras:

* conjugating `R_u` (right mult by a unit `u`) by an `S`-algebra automorphism `τ` gives
  `R_{τ(u)}`, so `τ R_u τ⁻¹ R_{u}⁻¹ = R_{u⁻¹ · τ(u)}` (`mulRight_conj_mulRight_inv`);
* over `M = S ⊗_R A`, right multiplication by `λ ⊗ 1` is the scalar `λ • id`
  (`mulRight_tmul_one`). -/

section RightMul

variable {S : Type*} [CommRing S] {M : Type*} [CommRing M] [Algebra S M]

/-- Conjugating right-multiplication `R_u` by an `S`-algebra automorphism `τ` and then
composing with `R_{u⁻¹}` yields right-multiplication by `u⁻¹ · τ(u)`:
`τ ∘ R_u ∘ τ⁻¹ ∘ R_{u⁻¹} = R_{u⁻¹ · τ(u)}`. Pure ring theory (`map_mul`, associativity). -/
theorem mulRight_conj_mulRight_inv (τ : M ≃ₐ[S] M) (u : Mˣ) :
    (τ.toLinearMap ∘ₗ LinearMap.mulRight S (↑u : M)) ∘ₗ
        (τ.symm.toLinearMap ∘ₗ LinearMap.mulRight S (↑u⁻¹ : M))
      = LinearMap.mulRight S ((↑u⁻¹ : M) * τ (↑u : M)) := by
  ext y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    AlgEquiv.toLinearMap_apply, map_mul, AlgEquiv.apply_symm_apply]
  ring

end RightMul

section RightMulTensor

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable {A : Type*} [CommRing A] [Algebra R A]

/-- Over `M = S ⊗_R A`, right multiplication by `λ ⊗ 1` is the scalar `λ • id_M`
(`R_{λ⊗1} = λ • id`). This is the identification `ℓ = λ • Iₙ` of Tate §3.8 (p. 144). -/
theorem mulRight_tmul_one (lam : S) :
    LinearMap.mulRight S ((lam ⊗ₜ[R] 1 : S ⊗[R] A)) = lam • LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      simp only [LinearMap.mulRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, TensorProduct.smul_tmul', smul_eq_mul]
      rw [mul_comm s lam]
  | add z w hz hw => simp only [map_add, hz, hw]

end RightMulTensor

/-- **(T-D5e-τ chain link 1.)** The scalar tower `R → B → A'_B`: the `R`- and `B`-algebra
structures on `S = WithConv (A →ₗ[R] B)` are compatible (transported through the `ofConv`
bijection via `WithConv.ofConv_smul`). This unblocks `pointAlgHom` (the point as an
`R`-algebra map `A → S`) and hence the automorphism `τ`. -/
instance instIsScalarTowerWithConv {R : Type u} [CommRing R] {A : Type v} [AddCommGroup A]
    [Module R A] {B : Type w} [CommRing B] [Algebra R B] :
    IsScalarTower R B (WithConv (A →ₗ[R] B)) where
  smul_assoc r b x := by
    apply WithConv.ofConv_injective
    simp only [WithConv.ofConv_smul, smul_assoc]

section Commutator

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [HopfAlgebra R A] [IsCocomm R A]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- **(T-D5e-τ chain link 2.)** The `B`-point `φ` as an `R`-algebra map into `S = A'_B`
(via the tower `R → B → S`). Feeds `translationTarget`/`τ`. -/
noncomputable def pointAlgHom (φ : A →ₐ[R] B) : A →ₐ[R] WithConv (A →ₗ[R] B) :=
  (IsScalarTower.toAlgHom R B (WithConv (A →ₗ[R] B))).comp φ

/-- **(T-D5e-τ chain link 3.)** `g : A →ₐ[R] S ⊗_R A`, `a ↦ ∑ ptS(a₍₁₎) ⊗ a₍₂₎`, where `ptS`
is `pointAlgHom φ`. This is the `R`-algebra map that defines the right-translation automorphism
`τ` of `M = S ⊗_R A` through the tensor-product universal property. -/
noncomputable def translationTarget (φ : A →ₐ[R] B) :
    A →ₐ[R] WithConv (A →ₗ[R] B) ⊗[R] A :=
  (Algebra.TensorProduct.map (pointAlgHom φ) (AlgHom.id R A)).comp (Bialgebra.comulAlgHom R A)

/-- **(T-D5e-τ chain link 4.)** The right-translation `S`-algebra *endomorphism* of `M = S ⊗_R A`,
`s ⊗ a ↦ ∑ (s · ptS(a₍₁₎)) ⊗ a₍₂₎`, obtained from `translationTarget` by the tensor-product
universal property (`Algebra.TensorProduct.liftEquiv`). Promoted to an automorphism `τ` in
`deligne_operators` via the convolution-inverse point. -/
noncomputable def translationEndo (φ : A →ₐ[R] B) :
    WithConv (A →ₗ[R] B) ⊗[R] A →ₐ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (translationTarget φ) (fun _ _ => Commute.all _ _)

/-- **(T-D5e-τ ingredient — the base-changed right translation.)** For a `B`-point `φ`, the
`R`-algebra map `A → B ⊗_R A`, `a ↦ ∑ φ(a₍₁₎) ⊗ a₍₂₎ = (φ ⊗ id)(Δ a)`. This is the coordinate
form of Tate's right-translation operator `τ_λ` base-changed to `B` (Tate §3.8 p. 144: "`τ_λ` is
the automorphism of the `R`-algebra `A` corresponding to right translation by λ"). It is an algebra
hom because `Δ = comulAlgHom` and `φ ⊗ id` are; the automorphism `τ` of `M = A'_B ⊗_R A` and the
identity `τ(u) = u·(λ⊗1)` are built on it (sub-tickets T-D5e-τ, T-D5e-3.8.2). -/
noncomputable def rightTranslationAlgHom (φ : A →ₐ[R] B) : A →ₐ[R] B ⊗[R] A :=
  (Algebra.TensorProduct.map φ (AlgHom.id R A)).comp (Bialgebra.comulAlgHom R A)

omit [IsCocomm R A] in
@[simp] lemma rightTranslationAlgHom_toLinearMap (φ : A →ₐ[R] B) :
    (rightTranslationAlgHom φ).toLinearMap
      = (Algebra.TensorProduct.map φ (AlgHom.id R A)).toLinearMap ∘ₗ Coalgebra.comul := by
  rfl

/-! ### The comparison iso `Ψ : A'_B ⊗_R A ≅ A'_{B⊗A}` (T-D5e-core, coevaluation engine)

Tate's Lemma 3.8.2 and the coevaluation unit `u = 𝟙 ∈ M` are cleanest through the natural
identification of the free-module operators with honest convolution maps. For `A` finite free over
`R`, the linear map
`Ψ : (A →ₗ[R] B) ⊗_R A → (A →ₗ[R] B ⊗_R A)`, `f ⊗ a ↦ (x ↦ f x ⊗ a)`
(mathlib's `rTensorHomEquivHomRTensor`) is an **isomorphism**, and — with `M = A'_B ⊗_R A`
carrying the tensor-of-algebras product and `T = A'_{B⊗_R A}` the convolution product — it is an
`R`-**algebra** isomorphism `M ≅ T`. Under Ψ the coevaluation `u = ∑ᵢ eᵢ' ⊗ eᵢ` becomes the
universal point `pointConv (includeRight)` of `T` (hence a unit, by `isUnit_pointConv`), and Tate's
Lemma 3.8.2 becomes the cocommutativity identity `∑ φ(x₍₁₎) ⊗ x₍₂₎ = ∑ φ(x₍₂₎) ⊗ x₍₁₎`. -/

section DeligneLeaf

variable [Module.Free R A] [Module.Finite R A]

/-- `Ψ` as an `R`-linear equivalence `A'_B ⊗_R A ≃ A'_{B⊗A}`, `f ⊗ a ↦ (x ↦ f x ⊗ a)`, from
mathlib's `rTensorHomEquivHomRTensor` (an equivalence since `A` is finite free) bridged through the
`WithConv` type synonym on both sides. -/
noncomputable def psiLinearEquiv :
    WithConv (A →ₗ[R] B) ⊗[R] A ≃ₗ[R] WithConv (A →ₗ[R] B ⊗[R] A) :=
  (TensorProduct.congr (WithConv.linearEquiv R (A →ₗ[R] B)) (LinearEquiv.refl R A)) ≪≫ₗ
    rTensorHomEquivHomRTensor R A B A ≪≫ₗ
    (WithConv.linearEquiv R (A →ₗ[R] B ⊗[R] A)).symm

omit [IsCocomm R A] in
@[simp] lemma psiLinearEquiv_tmul_ofConv (f : WithConv (A →ₗ[R] B)) (a : A) (x : A) :
    (psiLinearEquiv (f ⊗ₜ[R] a) : WithConv (A →ₗ[R] B ⊗[R] A)).ofConv x = f.ofConv x ⊗ₜ[R] a := by
  simp only [psiLinearEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    WithConv.linearEquiv_apply, LinearEquiv.refl_apply, rTensorHomEquivHomRTensor_apply,
    WithConv.symm_linearEquiv_apply, WithConv.ofConv_toConv,
    TensorProduct.rTensorHomToHomRTensor_apply]

omit [IsCocomm R A] in
/-- `Ψ` preserves the unit: `1_M = 1_S ⊗ 1_A ↦ 1_T` (both send `x ↦ ε(x) • (1 ⊗ 1)`). -/
lemma psiLinearEquiv_one :
    psiLinearEquiv (1 : WithConv (A →ₗ[R] B) ⊗[R] A) = 1 := by
  apply WithConv.ext
  ext x
  rw [Algebra.TensorProduct.one_def, psiLinearEquiv_tmul_ofConv]
  simp [LinearMap.convOne_apply, Algebra.TensorProduct.algebraMap_apply]

omit [IsCocomm R A] in
/-- `Ψ` is multiplicative: it carries the tensor-of-algebras product on `M = A'_B ⊗_R A` to the
convolution product on `T = A'_{B⊗A}`. On generators both sides send
`x ↦ ∑ (f x₍₁₎ · g x₍₂₎) ⊗ (a·c)` (the convolution Sweedler sum), by `convMul_apply` on each
side. -/
lemma psiLinearEquiv_mul (m₁ m₂ : WithConv (A →ₗ[R] B) ⊗[R] A) :
    psiLinearEquiv (m₁ * m₂) = psiLinearEquiv m₁ * psiLinearEquiv m₂ := by
  induction m₁ using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [add_mul, map_add, hx, hy]
  | tmul f a =>
    induction m₂ using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [mul_add, map_add, hx, hy]
    | tmul g c =>
      apply WithConv.ext
      ext x
      rw [Algebra.TensorProduct.tmul_mul_tmul, psiLinearEquiv_tmul_ofConv,
        (ℛ R x).convMul_apply f g, (ℛ R x).convMul_apply (psiLinearEquiv (f ⊗ₜ[R] a))
          (psiLinearEquiv (g ⊗ₜ[R] c)), TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psiLinearEquiv_tmul_ofConv, psiLinearEquiv_tmul_ofConv,
        Algebra.TensorProduct.tmul_mul_tmul]

/-- **(T-D5e-core — the comparison algebra isomorphism.)** `Ψ : M = A'_B ⊗_R A ≅ T = A'_{B⊗A}`
as an `R`-algebra equivalence. Tensor-of-algebras product ↦ convolution product. -/
noncomputable def psiAlgEquiv :
    WithConv (A →ₗ[R] B) ⊗[R] A ≃ₐ[R] WithConv (A →ₗ[R] B ⊗[R] A) :=
  AlgEquiv.ofLinearEquiv psiLinearEquiv psiLinearEquiv_one psiLinearEquiv_mul

omit [IsCocomm R A] in
@[simp] lemma psiAlgEquiv_apply (m : WithConv (A →ₗ[R] B) ⊗[R] A) :
    psiAlgEquiv m = psiLinearEquiv m := rfl

/-! ### The right-translation automorphism `τ` (T-D5e-τ auto-ness)

`τ = translationEndo φ` is promoted to an `A'_B`-algebra **automorphism** with inverse
`translationEndo φ'`, `φ' = φ ∘ S`. The two compositions reduce (via `Algebra.TensorProduct.ext`)
to `translationEndo φ (translationTarget φ' a) = 1 ⊗ a`, which is monoid algebra in the
*commutative* linear-convolution ring `A'_M = WithConv (A →ₗ[R] M)`: writing
`Pψ = pointConv(a ↦ ptS ψ(a) ⊗ 1)`,
`η = pointConv includeRight`, one has `translationTarget φ = Pφ ⋆ η` and
`translationEndo φ ∘ translationTarget ψ = Pψ ⋆ Pφ ⋆ η`, with `Pφ' = Pφ⁻¹` (the antipode is the
convolution inverse, `mul_pointConv_antipode_eq_one`). -/

/-- `A →ₐ[R] M`, `a ↦ ptS φ(a) ⊗ 1` — the "constant in the `A`-factor" leg of the right translation
(here `ptS = pointAlgHom φ`). Its `pointConv` is Tate's `Pφ`. -/
noncomputable def leftPointHom (φ : A →ₐ[R] B) :
    A →ₐ[R] WithConv (A →ₗ[R] B) ⊗[R] A :=
  (Algebra.TensorProduct.includeLeft :
    WithConv (A →ₗ[R] B) →ₐ[R] WithConv (A →ₗ[R] B) ⊗[R] A).comp (pointAlgHom φ)

omit [IsCocomm R A] [Module.Free R A] [Module.Finite R A] in
@[simp] lemma leftPointHom_apply (φ : A →ₐ[R] B) (a : A) :
    leftPointHom φ a = pointAlgHom φ a ⊗ₜ[R] (1 : A) := rfl

omit [Module.Free R A] [Module.Finite R A] in
/-- `translationEndo φ (s ⊗ a') = (s ⊗ 1) · translationTarget φ a'` (from the tensor-lift on
generators; `Algebra.ofId S M s = s ⊗ 1`). -/
lemma translationEndo_tmul (φ : A →ₐ[R] B) (s : WithConv (A →ₗ[R] B)) (a' : A) :
    translationEndo φ (s ⊗ₜ[R] a') = (s ⊗ₜ[R] (1 : A)) * translationTarget φ a' := by
  rw [translationEndo, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]

omit [Module.Free R A] [Module.Finite R A] in
lemma translationEndo_one_tmul (φ : A →ₐ[R] B) (a : A) :
    translationEndo φ (1 ⊗ₜ[R] a) = translationTarget φ a := by
  rw [translationEndo_tmul, ← Algebra.TensorProduct.one_def, one_mul]

omit [IsCocomm R A] [Module.Free R A] [Module.Finite R A] in
/-- `translationTarget φ a = ∑ ptS φ(a₍₁₎) ⊗ a₍₂₎` in any Sweedler representation of `a`. -/
lemma translationTarget_apply (φ : A →ₐ[R] B) (a : A) {ι : Type*} (repr : Coalgebra.Repr R a ι) :
    translationTarget φ a = ∑ i ∈ repr.index, pointAlgHom φ (repr.left i) ⊗ₜ[R] repr.right i := by
  rw [translationTarget, AlgHom.comp_apply,
    show (Bialgebra.comulAlgHom R A) a = Coalgebra.comul a from rfl, ← repr.eq, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [Module.Free R A] [Module.Finite R A] in
/-- **(T-D5e-τ, L1.)** In `A'_M`,
`translationEndo φ ∘ translationTarget ψ = Pψ ⋆ (translationTarget φ as a point)`: both send
`a ↦ ∑ (ptS ψ(a₍₁₎) ⊗ 1) · translationTarget φ(a₍₂₎)`. -/
lemma translationEndo_translationTarget_conv (φ ψ : A →ₐ[R] B) (a : A) :
    translationEndo φ (translationTarget ψ a)
      = (pointConv (leftPointHom ψ) * pointConv (translationTarget φ)) a := by
  rw [translationTarget_apply ψ a (ℛ R a), map_sum,
    (ℛ R a).convMul_apply (pointConv (leftPointHom ψ)) (pointConv (translationTarget φ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [translationEndo_tmul]
  simp only [pointConv, WithConv.ofConv_toConv, AlgHom.toLinearMap_apply,
    leftPointHom_apply]

omit [Module.Free R A] [Module.Finite R A] in
/-- **(T-D5e-τ, L2.)** `translationTarget φ = Pφ ⋆ η` in `A'_M`, `η = pointConv includeRight`:
both send `a ↦ ∑ (ptS φ(a₍₁₎) ⊗ 1)(1 ⊗ a₍₂₎) = ∑ ptS φ(a₍₁₎) ⊗ a₍₂₎`. -/
lemma pointConv_translationTarget_eq (φ : A →ₐ[R] B) :
    pointConv (translationTarget φ)
      = pointConv (leftPointHom φ) * pointConv (Algebra.TensorProduct.includeRight) := by
  apply WithConv.ext
  ext a
  rw [ofConv_pointConv]
  change translationTarget φ a = _
  rw [translationTarget_apply φ a (ℛ R a),
    (ℛ R a).convMul_apply (pointConv (leftPointHom φ))
      (pointConv Algebra.TensorProduct.includeRight)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pointConv, WithConv.ofConv_toConv, AlgHom.toLinearMap_apply,
    leftPointHom_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

omit [IsCocomm R A] [Module.Free R A] [Module.Finite R A] in
/-- `leftPointHom (φ ∘ S) = leftPointHom φ ∘ S` (the antipode passes through the point). -/
lemma leftPointHom_comp_antipode (φ : A →ₐ[R] B) :
    leftPointHom (φ.comp (antipodeAlgHom R A)) = (leftPointHom φ).comp (antipodeAlgHom R A) := by
  ext a
  simp only [leftPointHom_apply, AlgHom.comp_apply, pointAlgHom, AlgHom.comp_apply]

omit [Module.Free R A] [Module.Finite R A] in
/-- **(T-D5e-τ inverse.)** `Pφ ⋆ Pφ' = 1` in `A'_M` (`φ' = φ ∘ S`): the antipode gives the
convolution inverse of the left-point (`mul_pointConv_antipode_eq_one`). -/
lemma leftPointConv_mul_antipode (φ : A →ₐ[R] B) :
    pointConv (leftPointHom φ) * pointConv (leftPointHom (φ.comp (antipodeAlgHom R A))) = 1 := by
  have h : pointConv (leftPointHom (φ.comp (antipodeAlgHom R A)))
      = toConv ((leftPointHom φ).toLinearMap ∘ₗ antipode R) := by
    rw [leftPointHom_comp_antipode, pointConv, AlgHom.comp_toLinearMap, toLinearMap_antipodeAlgHom]
  rw [h]
  exact mul_pointConv_antipode_eq_one (leftPointHom φ)

omit [Module.Free R A] [Module.Finite R A] in
/-- **(T-D5e-τ crux.)** `translationEndo φ (translationTarget ψ a) = 1 ⊗ a` whenever the left-points
of `ψ` and `φ` are convolution-inverse (`Pψ ⋆ Pφ = 1`). Both antipode compositions of the
right-translation reduce to this. -/
lemma translationEndo_translationTarget_of_mul_eq_one (φ ψ : A →ₐ[R] B)
    (h : pointConv (leftPointHom ψ) * pointConv (leftPointHom φ) = 1) (a : A) :
    translationEndo φ (translationTarget ψ a) = 1 ⊗ₜ[R] a := by
  rw [translationEndo_translationTarget_conv φ ψ a, pointConv_translationTarget_eq φ,
    ← mul_assoc, h, one_mul]
  change (pointConv (Algebra.TensorProduct.includeRight :
    A →ₐ[R] WithConv (A →ₗ[R] B) ⊗[R] A)) a = 1 ⊗ₜ[R] a
  rw [pointConv]
  simp only [AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.includeRight_apply]

/-- **(T-D5e-τ — the right-translation automorphism.)** `τ = translationEndo φ` promoted to an
`A'_B`-algebra automorphism of `M = A'_B ⊗_R A`, with inverse `translationEndo (φ ∘ S)`. Both
compositions reduce (via `Algebra.TensorProduct.ext` and `translationEndo_tmul`) to the crux
`translationEndo _ (translationTarget _ a) = 1 ⊗ a`. -/
noncomputable def translationEquiv (φ : A →ₐ[R] B) :
    WithConv (A →ₗ[R] B) ⊗[R] A ≃ₐ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A :=
  AlgEquiv.ofAlgHom (translationEndo φ) (translationEndo (φ.comp (antipodeAlgHom R A)))
    (by
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => ?_)
      change translationEndo _ (translationEndo _ (1 ⊗ₜ[R] a)) = 1 ⊗ₜ[R] a
      rw [translationEndo_one_tmul]
      exact translationEndo_translationTarget_of_mul_eq_one φ (φ.comp (antipodeAlgHom R A))
        (by rw [mul_comm]; exact leftPointConv_mul_antipode φ) a)
    (by
      refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => ?_)
      change translationEndo _ (translationEndo _ (1 ⊗ₜ[R] a)) = 1 ⊗ₜ[R] a
      rw [translationEndo_one_tmul]
      exact translationEndo_translationTarget_of_mul_eq_one (φ.comp (antipodeAlgHom R A)) φ
        (leftPointConv_mul_antipode φ) a)

omit [Module.Free R A] [Module.Finite R A] in
@[simp] lemma translationEquiv_apply (φ : A →ₐ[R] B) (m : WithConv (A →ₗ[R] B) ⊗[R] A) :
    translationEquiv φ m = translationEndo φ m := rfl

/-! ### The coevaluation unit `u` and Lemma 3.8.2 (T-D5e-core)

`u = ∑ᵢ eᵢ' ⊗ eᵢ ∈ M` (`eᵢ` a basis of `A`, `eᵢ'` the dual coordinate pushed into `A'_B` via
`R → B`) is Tate's coevaluation element `𝟙 ∈ G(A)`. Under `Ψ` it becomes the universal point
`pointConv (includeRight)` of `T` — hence a **unit** (`isUnit_pointConv`). Tate's **Lemma 3.8.2**
`τ(u) = u · (λ ⊗ 1)` becomes, after applying `Ψ`,
`pointConv (rightTranslationAlgHom φ) = pointConv includeRight ⋆ pointConv (includeLeft ∘ φ)`,
i.e. `∑ φ(a₍₁₎) ⊗ a₍₂₎ = ∑ φ(a₍₂₎) ⊗ a₍₁₎`: **cocommutativity** (`comm_comul`). -/

/-- **(T-D5e-core — the coevaluation element `u = 𝟙 ∈ G(A)`.)** `∑ᵢ eᵢ' ⊗ eᵢ ∈ M`, with `eᵢ`
the chosen basis of the finite free `A` and `eᵢ'` its dual coordinate embedded `R → B`. -/
noncomputable def coev : WithConv (A →ₗ[R] B) ⊗[R] A :=
  ∑ i, toConv (Algebra.linearMap R B ∘ₗ (Module.Free.chooseBasis R A).coord i) ⊗ₜ[R]
    (Module.Free.chooseBasis R A) i

omit [IsCocomm R A] in
/-- **(T-D5e-core, key A.)** `Ψ(u) = pointConv (includeRight)`: under the comparison iso the
coevaluation is the universal point `a ↦ 1 ⊗ a` of `T` (dual-basis collapse
`∑ᵢ eᵢ'(x) • eᵢ = x`). -/
lemma psiAlgEquiv_coev :
    psiAlgEquiv coev = pointConv (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A) := by
  apply WithConv.ext
  ext x
  rw [psiAlgEquiv_apply, coev, map_sum, WithConv.ofConv_sum, LinearMap.coe_sum,
    Finset.sum_apply]
  rw [ofConv_pointConv, AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply]
  have : ∀ i, (psiLinearEquiv (toConv (Algebra.linearMap R B ∘ₗ
      (Module.Free.chooseBasis R A).coord i) ⊗ₜ[R] (Module.Free.chooseBasis R A) i)).ofConv x
      = (Module.Free.chooseBasis R A).repr x i •
        ((1 : B) ⊗ₜ[R] (Module.Free.chooseBasis R A) i) := by
    intro i
    rw [psiLinearEquiv_tmul_ofConv, WithConv.ofConv_toConv, LinearMap.comp_apply,
      Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      (Module.Free.chooseBasis R A).coord_apply, TensorProduct.smul_tmul']
  simp only [this]
  conv_rhs => rw [← (Module.Free.chooseBasis R A).sum_repr x, TensorProduct.tmul_sum]
  exact Finset.sum_congr rfl fun i _ => TensorProduct.smul_tmul _ _ _

omit [IsCocomm R A] [Module.Free R A] [Module.Finite R A] in
/-- `rightTranslationAlgHom φ a = ∑ φ(a₍₁₎) ⊗ a₍₂₎` in any Sweedler representation of `a`. -/
lemma rightTranslationAlgHom_apply (φ : A →ₐ[R] B) (a : A) {ι : Type*}
    (repr : Coalgebra.Repr R a ι) :
    rightTranslationAlgHom φ a = ∑ i ∈ repr.index, φ (repr.left i) ⊗ₜ[R] repr.right i := by
  rw [rightTranslationAlgHom, AlgHom.comp_apply,
    show (Bialgebra.comulAlgHom R A) a = Coalgebra.comul a from rfl, ← repr.eq, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [Module.Free R A] [Module.Finite R A] in
/-- `translationEndo φ (f ⊗ a) = ∑ (φ(a₍₁₎) • f) ⊗ a₍₂₎` (convolution with the point-element is a
scalar action; `f · ptS φ(a₍₁₎) = φ(a₍₁₎) • f`). -/
lemma translationEndo_tmul_expand (φ : A →ₐ[R] B) (f : WithConv (A →ₗ[R] B)) (a : A) :
    translationEndo φ (f ⊗ₜ[R] a)
      = ∑ i ∈ (ℛ R a).index, (φ ((ℛ R a).left i) • f) ⊗ₜ[R] (ℛ R a).right i := by
  rw [translationEndo_tmul, translationTarget_apply φ a (ℛ R a), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  rw [pointAlgHom, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, mul_comm, ← Algebra.smul_def]

/-- **(T-D5e-core generator formula.)** `Ψ(τ (f ⊗ a))(x) = (f(x) ⊗ 1) · (∑ φ(a₍₁₎) ⊗ a₍₂₎)` — the
key that makes the coevaluation computation basis-free: `x` enters only through `f(x)`, and the
right-translation `∑ φ(a₍₁₎) ⊗ a₍₂₎` is undivided. -/
lemma psiAlgEquiv_translationEndo_tmul (φ : A →ₐ[R] B) (f : WithConv (A →ₗ[R] B)) (a x : A) :
    (psiAlgEquiv (translationEndo φ (f ⊗ₜ[R] a))).ofConv x
      = (f.ofConv x ⊗ₜ[R] (1 : A)) * rightTranslationAlgHom φ a := by
  rw [psiAlgEquiv_apply, translationEndo_tmul_expand, map_sum, WithConv.ofConv_sum,
    LinearMap.coe_sum, Finset.sum_apply, rightTranslationAlgHom_apply φ a (ℛ R a), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [psiLinearEquiv_tmul_ofConv, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  rw [WithConv.ofConv_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]

/-- **(T-D5e-core, LHS of Lemma 3.8.2.)** `Ψ(τ u) = pointConv (rightTranslationAlgHom φ)`: applying
`τ` to the coevaluation and pushing through `Ψ` gives the point `a ↦ ∑ φ(a₍₁₎) ⊗ a₍₂₎`, by the
generator formula and the dual-basis collapse
`∑ᵢ eᵢ'(x) • rightTranslation(eᵢ) = rightTranslation x`. -/
lemma psiAlgEquiv_translationEndo_coev (φ : A →ₐ[R] B) :
    psiAlgEquiv (translationEndo φ coev) = pointConv (rightTranslationAlgHom φ) := by
  apply WithConv.ext
  ext x
  rw [ofConv_pointConv, AlgHom.toLinearMap_apply, coev, map_sum, map_sum, WithConv.ofConv_sum,
    LinearMap.coe_sum, Finset.sum_apply]
  have step : ∀ i, (psiAlgEquiv (translationEndo φ
      (toConv (Algebra.linearMap R B ∘ₗ (Module.Free.chooseBasis R A).coord i) ⊗ₜ[R]
        (Module.Free.chooseBasis R A) i))).ofConv x
      = (Module.Free.chooseBasis R A).repr x i •
          rightTranslationAlgHom φ ((Module.Free.chooseBasis R A) i) := by
    intro i
    rw [psiAlgEquiv_translationEndo_tmul, WithConv.ofConv_toConv, LinearMap.comp_apply,
      Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      (Module.Free.chooseBasis R A).coord_apply, ← TensorProduct.smul_tmul', smul_mul_assoc,
      ← Algebra.TensorProduct.one_def, one_mul]
  simp only [step, ← map_smul, ← map_sum, (Module.Free.chooseBasis R A).sum_repr]

omit [IsCocomm R A] in
/-- **(T-D5e-core, RHS of Lemma 3.8.2.)** `Ψ(λ ⊗ 1) = pointConv (includeLeft ∘ φ)`, the point
`a ↦ φ(a) ⊗ 1` of `T`. -/
lemma psiAlgEquiv_pointConv_tmul_one (φ : A →ₐ[R] B) :
    psiAlgEquiv (pointConv φ ⊗ₜ[R] (1 : A))
      = pointConv ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] A).comp φ) := by
  apply WithConv.ext
  ext x
  rw [psiAlgEquiv_apply, psiLinearEquiv_tmul_ofConv, ofConv_pointConv, ofConv_pointConv,
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    Algebra.TensorProduct.includeLeft_apply]

/-- **(T-D5e-core — Tate's Lemma 3.8.2, `τ(u) = u · (λ ⊗ 1)`.)** The sole remaining ingredient of
Deligne's proof. After applying the comparison iso `Ψ` (injective) it becomes the cocommutativity
identity `∑ φ(a₍₁₎) ⊗ a₍₂₎ = ∑ φ(a₍₂₎) ⊗ a₍₁₎` (`comm_comul`): both sides are
`(φ ⊗ id)(Δ a)` since `Δ` is cocommutative. -/
lemma coev_relation (φ : A →ₐ[R] B) :
    translationEndo φ coev = coev * (pointConv φ ⊗ₜ[R] (1 : A)) := by
  have key : psiAlgEquiv (translationEndo φ coev)
      = psiAlgEquiv (coev * (pointConv φ ⊗ₜ[R] (1 : A))) := by
    rw [psiAlgEquiv_translationEndo_coev, map_mul, psiAlgEquiv_coev, psiAlgEquiv_pointConv_tmul_one]
    apply WithConv.ext
    ext a
    rw [ofConv_pointConv, AlgHom.toLinearMap_apply, rightTranslationAlgHom_apply φ a (ℛ R a),
      (ℛ R a).convMul_apply]
    simp only [ofConv_pointConv, AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply,
      AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have e1 : (∑ i ∈ (ℛ R a).index, φ ((ℛ R a).left i) ⊗ₜ[R] (ℛ R a).right i)
        = TensorProduct.map φ.toLinearMap LinearMap.id (Coalgebra.comul a) := by
      rw [← (ℛ R a).eq, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [TensorProduct.map_tmul]; rfl
    have e2 : (∑ i ∈ (ℛ R a).index, φ ((ℛ R a).right i) ⊗ₜ[R] (ℛ R a).left i)
        = TensorProduct.map φ.toLinearMap LinearMap.id (Coalgebra.comul a) := by
      rw [← comm_comul R a, ← (ℛ R a).eq, map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [TensorProduct.comm_tmul, TensorProduct.map_tmul]; rfl
    rw [e1, e2]
  exact psiAlgEquiv.injective key

end DeligneLeaf

/-- **(Hopf core of Prop 3.8.1 = Lemma 3.8.2, Tate §3.8 p. 144 — SORRIED sub-ticket T-D5e-core.)**
The operators underlying Deligne's commutator: for a `B`-point `φ` (with `λ = pointConv φ`), there
is a unit `u` of the ring `M = A'_B ⊗_R A` — the **coevaluation element** `∑ eᵢ' ⊗ eᵢ`, i.e.
`id ∈ G(A)` under `A' ⊗ A ≅ End_R A` — and an `A'_B`-algebra automorphism `τ` of `M` — namely
`id_{A'} ⊗ τ_λ`, from the right-translation automorphism `τ_λ = (λ ⊗ id) ∘ Δ` on `A` — satisfying
`τ(u) = u · (λ ⊗ 1)`. This last equation is Tate's **Lemma 3.8.2** specialised to `φ = τ_λ`
("`(id_{A'} ⊗ φ)(id) = (id_A ⊗ φ')(id)`"), the sole remaining ingredient of Deligne's proof.

Proof (T-D5e-core, sorry-free): `u` is the coevaluation `coev = ∑ᵢ eᵢ' ⊗ eᵢ` — a **unit** because
the comparison iso `Ψ = psiAlgEquiv : M ≅ A'_{B⊗A}` carries it to the universal point
`pointConv (includeRight)`, which `isUnit_pointConv` shows invertible; `τ = translationEquiv φ` is
the right-translation automorphism; and `τ(u) = u · (λ ⊗ 1)` is `coev_relation`, which under `Ψ`
becomes cocommutativity `∑ φ(a₍₁₎) ⊗ a₍₂₎ = ∑ φ(a₍₂₎) ⊗ a₍₁₎`. All pieces live in the
`DeligneLeaf` section above. -/
theorem deligne_operators (φ : A →ₐ[R] B) [Module.Free R A] [Module.Finite R A] :
    ∃ (u : (WithConv (A →ₗ[R] B) ⊗[R] A)ˣ)
      (τ : WithConv (A →ₗ[R] B) ⊗[R] A ≃ₐ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A),
      τ (↑u : WithConv (A →ₗ[R] B) ⊗[R] A)
        = (↑u : WithConv (A →ₗ[R] B) ⊗[R] A) * (pointConv φ ⊗ₜ[R] (1 : A)) := by
  have hu : IsUnit (coev (R := R) (A := A) (B := B)) := by
    have h := (isUnit_pointConv (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A)).map
      (psiAlgEquiv (R := R) (A := A) (B := B)).symm
    rwa [← psiAlgEquiv_coev (R := R) (A := A) (B := B), AlgEquiv.symm_apply_apply] at h
  refine ⟨hu.unit, translationEquiv φ, ?_⟩
  rw [hu.unit_spec, translationEquiv_apply]
  exact coev_relation φ

/-- **(T-D5e — Proposition 3.8.1, Tate §3.8 p. 144.)** On the free rank-`n` left-`A'`-module
`M := A'_B ⊗_R A`, the scalar map `λ • id_M` — which is right multiplication by `λ ⊗ 1` — is the
commutator `τ ρ τ⁻¹ ρ⁻¹`, where `ρ` is right multiplication by the coevaluation unit `u = 𝟙 ∈ M`
and `τ = id_{A'} ⊗ τ_λ` is the ring automorphism of `M` induced by right translation `τ_λ` on `A`.
The key relation (Lemma 3.8.2 with `φ = τ_λ`) is `τ(u) = u · (λ ⊗ 1)`, whence for a ring
automorphism `τ`, `τ ρ τ⁻¹ = R_{τ(u)}` and `R_{τ(u)} ρ⁻¹ = R_{u⁻¹ · τ(u)} = R_{λ⊗1} = λ • id`.

Stated in the form the determinant step (`pow_eq_one_of_smul_id_eq_commutator`) consumes: over
`S := A'_B = WithConv (A →ₗ[R] B)` and the free `S`-module `M = S ⊗_R A`, there exist units
`P Q` of `End_S M` (i.e. `S`-linear automorphisms of `M`) with `λ • id_M = P Q P⁻¹ Q⁻¹`. Proof
deferred to the sub-tickets T-D5e1–e5 (tensor module, `τ_λ`, right-mult operators, Lemma 3.8.2,
commutator identity). -/
theorem exists_commutator_eq_pointConv_smul_one (φ : A →ₐ[R] B)
    [Module.Free R A] [Module.Finite R A] :
    ∃ P Q : (WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)]
              WithConv (A →ₗ[R] B) ⊗[R] A)ˣ,
      pointConv φ • (LinearMap.id : WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)]
              WithConv (A →ₗ[R] B) ⊗[R] A)
        = ↑(P * Q * P⁻¹ * Q⁻¹) := by
  obtain ⟨u, τ, hτu⟩ := deligne_operators φ
  -- `P` = the automorphism `τ`; `Q` = right multiplication `ρ = R_u` by the unit `u`.
  let P : (WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A)ˣ :=
    { val := τ.toLinearMap, inv := τ.symm.toLinearMap,
      val_inv := LinearMap.ext fun y => by simp [Module.End.mul_eq_comp]
      inv_val := LinearMap.ext fun y => by simp [Module.End.mul_eq_comp] }
  let Q : (WithConv (A →ₗ[R] B) ⊗[R] A →ₗ[WithConv (A →ₗ[R] B)] WithConv (A →ₗ[R] B) ⊗[R] A)ˣ :=
    { val := LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u)
      inv := LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u⁻¹)
      val_inv := LinearMap.ext fun y => by
        simp [Module.End.mul_eq_comp, LinearMap.mulRight_apply, mul_assoc]
      inv_val := LinearMap.ext fun y => by
        simp [Module.End.mul_eq_comp, LinearMap.mulRight_apply, mul_assoc] }
  refine ⟨P, Q, ?_⟩
  have hP : (↑P : _ →ₗ[_] _) = τ.toLinearMap := rfl
  have hPi : (↑P⁻¹ : _ →ₗ[_] _) = τ.symm.toLinearMap := rfl
  have hQ : (↑Q : _ →ₗ[_] _)
      = LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u : WithConv (A →ₗ[R] B) ⊗[R] A) := rfl
  have hQi : (↑Q⁻¹ : _ →ₗ[_] _)
      = LinearMap.mulRight (WithConv (A →ₗ[R] B)) (↑u⁻¹ : WithConv (A →ₗ[R] B) ⊗[R] A) := rfl
  -- `λ • id = τ ∘ R_u ∘ τ⁻¹ ∘ R_{u⁻¹} = R_{u⁻¹ · τ u} = R_{λ⊗1} = λ • id`.
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hP, hQ, hPi, hQi,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, mulRight_conj_mulRight_inv τ u, hτu, ← mul_assoc,
    Units.inv_mul, one_mul, mulRight_tmul_one]

/-- **(T-D5g — Deligne's order theorem, group-like form; Tate §3.8 pp. 144–145.)** For a
cocommutative Hopf algebra `A` finite free over `R`, any `B`-point `φ : A →ₐ[R] B` satisfies
`(pointConv φ)^n = 1`, where `n` is the `S`-rank of `M = S ⊗_R A` (`S := A'_B`) — which for a
nontrivial base equals the order `finrank R A` of `G`. Equivalently `n • Q = 0`: Deligne's
theorem that a commutative finite flat group scheme is killed by its order. Assembled from the
commutator `λ • id_M = P Q P⁻¹ Q⁻¹` (Prop 3.8.1, `exists_commutator_eq_pointConv_smul_one`) and
the determinant step (`pow_eq_one_of_smul_id_eq_commutator`).

The rank `n` is taken as `finrank S (S ⊗_R A)` (supplied by the caller) rather than reduced to
`finrank R A`: the reduction `finrank S (S ⊗_R A) = finrank R A` needs `StrongRankCondition` on
both rings (i.e. a nontrivial base), which the geometric consumer (Layer B) provides in context.
See `deligne_pointConv_pow_finrank` for that reduced form. -/
theorem deligne_pointConv_pow (φ : A →ₐ[R] B) [Module.Free R A] [Module.Finite R A]
    {n : ℕ}
    (hn : Module.finrank (WithConv (A →ₗ[R] B)) (WithConv (A →ₗ[R] B) ⊗[R] A) = n) :
    (pointConv φ) ^ n = 1 := by
  obtain ⟨P, Q, hPQ⟩ := exists_commutator_eq_pointConv_smul_one φ
  haveI : Module.Finite (WithConv (A →ₗ[R] B)) (WithConv (A →ₗ[R] B) ⊗[R] A) :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R A).baseChange _)
  exact pow_eq_one_of_smul_id_eq_commutator hn (pointConv φ) P Q hPQ

/-- **(T-D5g, reduced form.)** For a *nontrivial* base ring `R` (so `finrank` is well-behaved),
Deligne's theorem reads `(pointConv φ)^(finrank R A) = 1`: the point is killed by the order
`finrank R A` of `G`. Uses `Module.finrank_baseChange` (`finrank S (S ⊗_R A) = finrank R A`),
which requires `StrongRankCondition R` — supplied here by `[Nontrivial R]` via
`commRing_strongRankCondition`. -/
theorem deligne_pointConv_pow_finrank (φ : A →ₐ[R] B) [Module.Free R A] [Module.Finite R A]
    [Nontrivial R] [Nontrivial (WithConv (A →ₗ[R] B))] :
    (pointConv φ) ^ (Module.finrank R A) = 1 :=
  deligne_pointConv_pow φ (Module.finrank_baseChange)

/-- **(T-D5g, point-group form — the Layer-B consumable.)** Deligne's order theorem stated in
mathlib's convolution *group* of points `WithConv (A →ₐ[R] B)` (a `CommGroup` for `A` commutative
cocommutative, inverse via the antipode): a `B`-point `φ : A →ₐ[R] B` of a finite-free commutative
cocommutative Hopf algebra satisfies `(toConv φ)^(finrank R A) = 1`. This is `n • [point] = 0` in
the point group — the exact form the geometric bridge (`RelEffCartierDiv.IsSubgroup`, Layer B)
consumes once it identifies the curve's group law on a subgroup divisor with convolution of points.
Obtained from `deligne_pointConv_pow_finrank` by transporting along the injective forgetful
`AlgHom → LinearMap` (mathlib's `AlgHom.toLinearMap_convPow`/`toLinearMap_convOne`).
Mathlib-upstream candidate alongside the linear form. -/
theorem deligne_point_pow_eq_one (φ : A →ₐ[R] B) [Module.Free R A] [Module.Finite R A]
    [Nontrivial R] [Nontrivial (WithConv (A →ₗ[R] B))] :
    (toConv φ : WithConv (A →ₐ[R] B)) ^ (Module.finrank R A) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convPow, AlgHom.toLinearMap_convOne]
  exact deligne_pointConv_pow_finrank φ

end Commutator

end ModularCurves.CartierDual
