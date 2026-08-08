/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.TorsionFree
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.KummerLocalizationAway

/-!
# Multiplicative cocycles and effective rank-one descent

This file turns a normalized tensor-unit cocycle for a faithfully flat ring map `A → B`
into an effective rank-one `A`-module.  The cocycle is first checked directly against the
comonad for extension/restriction of scalars; Mathlib's comonadic faithfully-flat descent then
constructs the descended module.  Over a principal ideal domain, local triviality forces the
descended module to be free of rank one.

The final theorem specializes this construction to `ℤ[1/ℓ]` and consumes the checked Picard
triviality of that ring.  This file deliberately does not identify represented fppf cocycles
with tensor-unit cocycles and does not assert an ambient `H¹(G_m)` vanishing theorem.
-/

open CategoryTheory ModuleCat Comonad TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent

namespace ComonadicRankOneDescent

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- Coalgebras for the comonad attached to a faithfully flat extension of scalars. -/
abbrev DescentCoalgebra (hf : f.FaithfullyFlat) :=
  letI : ComonadicLeftAdjoint (extendScalars f) := comonadicExtendScalars hf
  (comonadicAdjunction (extendScalars f)).toComonad.Coalgebra

/-- The module recovered from effective faithfully-flat descent. -/
noncomputable def descendedModule (hf : f.FaithfullyFlat)
    (D : DescentCoalgebra f hf) : ModuleCat A := by
  letI : ComonadicLeftAdjoint (extendScalars f) := comonadicExtendScalars hf
  let K := Comonad.comparison (comonadicAdjunction (extendScalars f))
  exact K.objPreimage D

/-- Base-changing the recovered module gives the underlying module of the descent coalgebra. -/
noncomputable def baseChangeIso (hf : f.FaithfullyFlat)
    (D : DescentCoalgebra f hf) :
    (extendScalars f).obj (descendedModule f hf D) ≅ D.A := by
  letI : ComonadicLeftAdjoint (extendScalars f) := comonadicExtendScalars hf
  let adj := comonadicAdjunction (extendScalars f)
  let K := Comonad.comparison adj
  exact (Comonad.forget adj.toComonad).mapIso (K.objObjPreimageIso D)

private noncomputable def localTrivialization (hf : f.FaithfullyFlat)
    (D : DescentCoalgebra f hf) (e : D.A ≅ ModuleCat.of B B) :
    (extendScalars f).obj (descendedModule f hf D) ≅ ModuleCat.of B B :=
  baseChangeIso f hf D ≪≫ e

/-- If a faithfully-flat descent coalgebra is locally the regular rank-one module, its
effective descent is a free rank-one module over a principal ideal domain. -/
noncomputable def descendedModuleLinearEquivBase
    (hf : f.FaithfullyFlat) [Nontrivial B] [IsDomain A]
    [IsPrincipalIdealRing A] (D : DescentCoalgebra f hf)
    (e : D.A ≅ ModuleCat.of B B) :
    descendedModule f hf D ≃ₗ[A] A := by
  let M := descendedModule f hf D
  letI := f.toAlgebra
  letI : Module.FaithfullyFlat A B := hf
  let eB : B ⊗[A] M ≃ₗ[B] B := (localTrivialization f hf D e).toLinearEquiv
  letI : Module.Finite B (B ⊗[A] M) :=
    (Module.Finite.equiv_iff eB).mpr inferInstance
  letI : Module.Finite A M :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  letI : Module.Flat B (B ⊗[A] M) :=
    (Module.Flat.equiv_iff eB).mpr inferInstance
  letI : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M B
  letI : Module.IsTorsionFree A M := inferInstance
  letI : Module.Free A M := Module.free_of_finite_type_torsion_free'
  have hrankB : Module.rank B (B ⊗[A] M) = 1 := by
    rw [eB.rank_eq]
    exact Module.rank_self B
  have hrankA : Module.rank A M = 1 := by
    have hbase := Module.rank_baseChange (R := B) (S := A) (M' := M)
    rw [hrankB] at hbase
    simpa using hbase.symm
  exact finDimVectorspaceEquiv 1 hrankA ≪≫ₗ
    LinearEquiv.funUnique (Fin 1) A A

end ComonadicRankOneDescent

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

private noncomputable def leftOverlapMap : B →ₐ[A] B ⊗[A] B :=
  Algebra.TensorProduct.includeLeft

/-- The extension/restriction-of-scalars comonad used for affine module descent. -/
abbrev descentComonad :=
  (extendRestrictScalarsAdj (algebraMap A B)).toComonad

/-- The right-associated threefold tensor product used for the cocycle identity. -/
abbrev tripleRing := B ⊗[A] (B ⊗[A] B)

private noncomputable def firstToTriple : B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.includeLeft

private noncomputable def secondToTriple : B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft

private noncomputable def thirdToTriple : B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight

/-- Pullback from the double overlap to factors one and two of the triple overlap. -/
noncomputable def pairTwelve : B ⊗[A] B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.productMap firstToTriple secondToTriple

/-- Pullback from the double overlap to factors two and three of the triple overlap. -/
noncomputable def pairTwentyThree :
    B ⊗[A] B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.includeRight

/-- Pullback from the double overlap to factors one and three of the triple overlap. -/
noncomputable def pairThirteen : B ⊗[A] B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.productMap firstToTriple thirdToTriple

/-- A normalized multiplicative Čech cocycle on the singleton affine cover `A → B`.

The three maps in `cocycle` pull a unit on `B ⊗_A B` to the `(1,2)`, `(2,3)`, and
`(1,3)` overlaps in `B ⊗_A B ⊗_A B`, respectively. -/
structure MultiplicativeUnitCocycle where
  unit : (B ⊗[A] B)ˣ
  normalization :
    Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom unit = 1
  cocycle :
    Units.map pairTwelve.toMonoidHom unit *
        Units.map pairTwentyThree.toMonoidHom unit =
      Units.map pairThirteen.toMonoidHom unit

private def structureLinearMap (g : (B ⊗[A] B)ˣ) :
    B →ₗ[B] B ⊗[A] B where
  toFun b := leftOverlapMap b * (g : B ⊗[A] B)
  map_add' x y := by rw [map_add, add_mul]
  map_smul' b x := by
    calc
      leftOverlapMap (b • x) * (g : B ⊗[A] B) =
          leftOverlapMap (b * x) * (g : B ⊗[A] B) := by rw [smul_eq_mul]
      _ = (leftOverlapMap b * leftOverlapMap x) * (g : B ⊗[A] B) := by
        rw [map_mul]
      _ = leftOverlapMap b * (leftOverlapMap x * (g : B ⊗[A] B)) :=
        mul_assoc _ _ _
      _ = b • (leftOverlapMap x * (g : B ⊗[A] B)) := by
        rw [Algebra.smul_def]
        rfl

private def restrictedRegularToBaseLinearEquiv :
    (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change (show B from r • x) = r • (show B from x)
    rw [restrictScalars.smul_def]
    change ((algebraMap A B r) • (show B from x) : B) =
      r • (show B from x)
    rw [smul_eq_mul, Algebra.smul_def]

private def restrictedRegularToRegularLinearEquiv :
    (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[B] B where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def comonadPairLinearEquiv :
    (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B) ≃ₗ[B]
      B ⊗[A] B := by
  let N := (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B N := IsScalarTower.of_compHom A B N
  letI : SMulCommClass A B N :=
    ModuleCat.sMulCommClass_mk (algebraMap A B) B
  let raw : N ⊗[A] N ≃ₗ[B] B ⊗[A] B :=
    AlgebraTensorModule.congr
      (restrictedRegularToRegularLinearEquiv (A := A) (B := B))
      (restrictedRegularToBaseLinearEquiv (A := A) (B := B))
  exact raw

private noncomputable def comonadPairIso :
    (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B) ≅
      ModuleCat.of B (B ⊗[A] B) :=
  LinearEquiv.toModuleIso (comonadPairLinearEquiv (A := A) (B := B))

private def restrictedComonadPairToPairLinearEquiv :
    (restrictScalars (algebraMap A B)).obj
        ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) ≃ₗ[A]
      B ⊗[A] B where
  toFun x := (comonadPairLinearEquiv (A := A) (B := B)) x
  invFun x := (comonadPairLinearEquiv (A := A) (B := B)).symm x
  left_inv := (comonadPairLinearEquiv (A := A) (B := B)).left_inv
  right_inv := (comonadPairLinearEquiv (A := A) (B := B)).right_inv
  map_add' := (comonadPairLinearEquiv (A := A) (B := B)).map_add
  map_smul' r x := by
    rw [restrictScalars.smul_def]
    calc
      (comonadPairLinearEquiv (A := A) (B := B))
          ((algebraMap A B r) • x) =
          (algebraMap A B r) •
            (comonadPairLinearEquiv (A := A) (B := B)) x :=
        (comonadPairLinearEquiv (A := A) (B := B)).map_smul _ _
      _ = r • (comonadPairLinearEquiv (A := A) (B := B)) x := by
        rw [Algebra.smul_def, Algebra.smul_def,
          IsScalarTower.algebraMap_apply A B (B ⊗[A] B)]

private noncomputable def comonadTripleLinearEquiv :
    (descentComonad (A := A) (B := B)).obj
        ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) ≃ₗ[B]
      tripleRing (A := A) (B := B) := by
  let N := (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  let P := (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)
  let NP := (restrictScalars (algebraMap A B)).obj P
  letI : IsScalarTower A B N := IsScalarTower.of_compHom A B N
  letI : SMulCommClass A B N :=
    ModuleCat.sMulCommClass_mk (algebraMap A B) B
  let raw : N ⊗[A] NP ≃ₗ[B] B ⊗[A] (B ⊗[A] B) :=
    AlgebraTensorModule.congr
      (restrictedRegularToRegularLinearEquiv (A := A) (B := B))
      (restrictedComonadPairToPairLinearEquiv (A := A) (B := B))
  exact raw

private noncomputable def comonadTripleIso :
    (descentComonad (A := A) (B := B)).obj
        ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) ≅
      ModuleCat.of B (tripleRing (A := A) (B := B)) :=
  LinearEquiv.toModuleIso (comonadTripleLinearEquiv (A := A) (B := B))

private def structureMap (g : (B ⊗[A] B)ˣ) :
    ModuleCat.of B B ⟶
      (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B) :=
  ModuleCat.ofHom (structureLinearMap g) ≫
    (comonadPairIso (A := A) (B := B)).inv

@[simp]
private theorem comonadPairIso_hom_structureMap_apply
    (g : (B ⊗[A] B)ˣ) (b : B) :
    (comonadPairIso (A := A) (B := B)).hom (structureMap g b) =
      leftOverlapMap b * (g : B ⊗[A] B) := by
  change ((ModuleCat.ofHom (structureLinearMap g) ≫
    (comonadPairIso (A := A) (B := B)).inv) ≫
      (comonadPairIso (A := A) (B := B)).hom) b = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

@[simp]
private theorem comonadPairIso_inv_tmul (x y : B) :
    (comonadPairIso (A := A) (B := B)).inv (x ⊗ₜ[A] y) =
      ((show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from x) ⊗ₜ[A]
        (show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from y) :
        (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) := by
  rfl

private theorem comonad_counit_tmul
    (x y : (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :
    (descentComonad (A := A) (B := B)).ε.app (ModuleCat.of B B)
        (x ⊗ₜ[A] y) = (show B from x) * (show B from y) := by
  rfl

private theorem comonad_counit_apply
    (z : (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) :
    (descentComonad (A := A) (B := B)).ε.app (ModuleCat.of B B) z =
      (Algebra.TensorProduct.lmul' A)
        ((comonadPairIso (A := A) (B := B)).hom z) := by
  let e := comonadPairIso (A := A) (B := B)
  let w := e.hom z
  have hz : e.inv w = z := by simp only [w, Iso.hom_inv_id_apply]
  rw [← hz]
  simp only [e, Iso.inv_hom_id_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [comonadPairIso_inv_tmul]
      rw [Algebra.TensorProduct.lmul'_apply_tmul]
      exact comonad_counit_tmul
        (show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from x)
        (show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from y)
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) hx hy

private theorem comonad_delta_tmul
    (x y : (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :
    (descentComonad (A := A) (B := B)).δ.app (ModuleCat.of B B)
        (x ⊗ₜ[A] y) =
      (x ⊗ₜ[A] ((1 : B) ⊗ₜ[A] y) :
        (descentComonad (A := A) (B := B)).obj
          ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B))) := by
  rfl

@[simp]
private theorem comonadTripleIso_hom_tmul (x y z : B) :
    (comonadTripleIso (A := A) (B := B)).hom
        ((show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from x) ⊗ₜ[A]
          ((show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from y) ⊗ₜ[A]
            (show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from z)) :
          (descentComonad (A := A) (B := B)).obj
            ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B))) =
      x ⊗ₜ[A] (y ⊗ₜ[A] z) := by
  rfl

@[simp]
private theorem pairThirteen_tmul (x y : B) :
    pairThirteen (A := A) (B := B) (x ⊗ₜ[A] y) =
      x ⊗ₜ[A] ((1 : B) ⊗ₜ[A] y) := by
  simp only [pairThirteen, Algebra.TensorProduct.productMap_apply_tmul,
    firstToTriple, thirdToTriple, AlgHom.comp_apply,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

@[simp]
private theorem pairTwelve_tmul (x y : B) :
    pairTwelve (A := A) (B := B) (x ⊗ₜ[A] y) =
      x ⊗ₜ[A] (y ⊗ₜ[A] (1 : B)) := by
  simp only [pairTwelve, Algebra.TensorProduct.productMap_apply_tmul,
    firstToTriple, secondToTriple, AlgHom.comp_apply,
    Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

@[simp]
private theorem pairTwentyThree_apply (g : B ⊗[A] B) :
    pairTwentyThree (A := A) (B := B) g =
      (1 : B) ⊗ₜ[A] g := by
  exact Algebra.TensorProduct.includeRight_apply g

private theorem comonad_map_structure_tmul
    (g : (B ⊗[A] B)ˣ)
    (x y : (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :
    (descentComonad (A := A) (B := B)).map (structureMap g) (x ⊗ₜ[A] y) =
      (x ⊗ₜ[A] structureMap g y :
        (descentComonad (A := A) (B := B)).obj
          ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B))) := by
  rfl

@[simp]
private theorem comonadTripleIso_hom_outer_tmul
    (x : B)
    (z : (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) :
    (comonadTripleIso (A := A) (B := B)).hom
        ((show (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from x) ⊗ₜ[A]
          (show (restrictScalars (algebraMap A B)).obj
            ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) from z) :
          (descentComonad (A := A) (B := B)).obj
            ((descentComonad (A := A) (B := B)).obj (ModuleCat.of B B))) =
      x ⊗ₜ[A] (comonadPairIso (A := A) (B := B)).hom z := by
  rfl

private theorem comonad_delta_apply
    (z : (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) :
    (comonadTripleIso (A := A) (B := B)).hom
        ((descentComonad (A := A) (B := B)).δ.app (ModuleCat.of B B) z) =
      pairThirteen (A := A) (B := B)
        ((comonadPairIso (A := A) (B := B)).hom z) := by
  let e := comonadPairIso (A := A) (B := B)
  let w := e.hom z
  have hz : e.inv w = z := by simp only [w, Iso.hom_inv_id_apply]
  rw [← hz]
  simp only [e, Iso.inv_hom_id_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change (comonadTripleIso (A := A) (B := B)).hom
          ((descentComonad (A := A) (B := B)).δ.app (ModuleCat.of B B)
            (e.inv (x ⊗ₜ[A] y))) =
        pairThirteen (A := A) (B := B) (x ⊗ₜ[A] y)
      rw [show e = comonadPairIso (A := A) (B := B) by rfl,
        comonadPairIso_inv_tmul, comonad_delta_tmul,
        comonadTripleIso_hom_tmul, pairThirteen_tmul]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) hx hy

private theorem comonad_map_structure_apply
    (g : (B ⊗[A] B)ˣ)
    (z : (descentComonad (A := A) (B := B)).obj (ModuleCat.of B B)) :
    (comonadTripleIso (A := A) (B := B)).hom
        ((descentComonad (A := A) (B := B)).map (structureMap g) z) =
      pairTwelve (A := A) (B := B)
          ((comonadPairIso (A := A) (B := B)).hom z) *
        pairTwentyThree (A := A) (B := B) (g : B ⊗[A] B) := by
  let e := comonadPairIso (A := A) (B := B)
  let w := e.hom z
  have hz : e.inv w = z := by simp only [w, Iso.hom_inv_id_apply]
  rw [← hz]
  simp only [e, Iso.inv_hom_id_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change (comonadTripleIso (A := A) (B := B)).hom
          ((descentComonad (A := A) (B := B)).map (structureMap g)
            (e.inv (x ⊗ₜ[A] y))) =
        pairTwelve (A := A) (B := B) (x ⊗ₜ[A] y) *
          pairTwentyThree (A := A) (B := B) (g : B ⊗[A] B)
      rw [show e = comonadPairIso (A := A) (B := B) by rfl,
        comonadPairIso_inv_tmul, comonad_map_structure_tmul,
        comonadTripleIso_hom_outer_tmul,
        comonadPairIso_hom_structureMap_apply, pairTwelve_tmul,
        pairTwentyThree_apply, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [leftOverlapMap, Algebra.TensorProduct.includeLeft_apply, mul_one]
  | add x y hx hy =>
      simpa only [map_add, add_mul] using congrArg₂ (fun p q ↦ p + q) hx hy

@[simp]
private theorem pairTwelve_leftOverlapMap (b : B) :
    pairTwelve (A := A) (B := B) (leftOverlapMap b) =
      firstToTriple (A := A) (B := B) b := by
  simp only [leftOverlapMap, Algebra.TensorProduct.includeLeft_apply,
    pairTwelve_tmul, firstToTriple, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.one_def]

@[simp]
private theorem pairThirteen_leftOverlapMap (b : B) :
    pairThirteen (A := A) (B := B) (leftOverlapMap b) =
      firstToTriple (A := A) (B := B) b := by
  simp only [leftOverlapMap, Algebra.TensorProduct.includeLeft_apply,
    pairThirteen_tmul, firstToTriple, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.one_def]

private theorem structureMap_counit
    (c : MultiplicativeUnitCocycle (A := A) (B := B)) :
    structureMap c.unit ≫
        (descentComonad (A := A) (B := B)).ε.app (ModuleCat.of B B) =
      𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  rw [ModuleCat.comp_apply, comonad_counit_apply,
    comonadPairIso_hom_structureMap_apply]
  rw [map_mul]
  have hnorm := congrArg Units.val c.normalization
  change (Algebra.TensorProduct.lmul' A) (c.unit : B ⊗[A] B) = 1 at hnorm
  rw [hnorm, mul_one]
  simp only [leftOverlapMap, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  rfl

private theorem structureMap_coassoc
    (c : MultiplicativeUnitCocycle (A := A) (B := B)) :
    structureMap c.unit ≫
        (descentComonad (A := A) (B := B)).δ.app (ModuleCat.of B B) =
      structureMap c.unit ≫
        (descentComonad (A := A) (B := B)).map (structureMap c.unit) := by
  apply (cancel_mono (comonadTripleIso (A := A) (B := B)).hom).1
  simp only [Category.assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change (comonadTripleIso (A := A) (B := B)).hom
      ((descentComonad (A := A) (B := B)).δ.app (ModuleCat.of B B)
        (structureMap c.unit b)) =
    (comonadTripleIso (A := A) (B := B)).hom
      ((descentComonad (A := A) (B := B)).map (structureMap c.unit)
        (structureMap c.unit b))
  rw [comonad_delta_apply, comonad_map_structure_apply,
    comonadPairIso_hom_structureMap_apply,
    map_mul, map_mul, pairTwelve_leftOverlapMap,
    pairThirteen_leftOverlapMap]
  have hcocycle := congrArg Units.val c.cocycle
  change pairTwelve (A := A) (B := B) (c.unit : B ⊗[A] B) *
      pairTwentyThree (A := A) (B := B) (c.unit : B ⊗[A] B) =
    pairThirteen (A := A) (B := B) (c.unit : B ⊗[A] B) at hcocycle
  rw [← hcocycle]
  ac_rfl

/-- A normalized tensor-unit cocycle gives a genuine coalgebra for the module-descent comonad. -/
noncomputable def MultiplicativeUnitCocycle.toCoalgebra
    (c : MultiplicativeUnitCocycle (A := A) (B := B)) :
    (descentComonad (A := A) (B := B)).Coalgebra where
  A := ModuleCat.of B B
  a := structureMap c.unit
  counit := structureMap_counit c
  coassoc := structureMap_coassoc c

/-- The effective module descended from a normalized multiplicative tensor-unit cocycle. -/
noncomputable def MultiplicativeUnitCocycle.descendedModule
    (c : MultiplicativeUnitCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) : ModuleCat A :=
  ComonadicRankOneDescent.descendedModule (algebraMap A B) hf c.toCoalgebra

/-- The cocycle's effective descent becomes the regular rank-one module after base change. -/
noncomputable def MultiplicativeUnitCocycle.baseChangeIso
    (c : MultiplicativeUnitCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) :
    (extendScalars (algebraMap A B)).obj (c.descendedModule hf) ≅
      ModuleCat.of B B :=
  ComonadicRankOneDescent.baseChangeIso
    (algebraMap A B) hf c.toCoalgebra

/-- Over a principal ideal domain, the effective descent of a normalized multiplicative
tensor-unit cocycle is explicitly a free rank-one module. -/
noncomputable def MultiplicativeUnitCocycle.descendedModuleLinearEquivBase
    (c : MultiplicativeUnitCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) [Nontrivial B] [IsDomain A]
    [IsPrincipalIdealRing A] :
    c.descendedModule hf ≃ₗ[A] A :=
  ComonadicRankOneDescent.descendedModuleLinearEquivBase
    (algebraMap A B) hf c.toCoalgebra (Iso.refl _)

private theorem primeAway_nontrivial (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nontrivial (Localization.Away (ℓ : ℤ)) :=
  ⟨⟨0, 1, fun h ↦ by
    have h' := congrArg
      (MultiplicativeKummer.awayToRat ℓ hℓ) h
    exact (zero_ne_one : (0 : ℚ) ≠ 1)
      (by simpa only [map_zero, map_one] using h')⟩⟩

/-- Over `ℤ[1/ℓ]`, a normalized multiplicative tensor-unit cocycle for a faithfully flat
affine cover descends to the trivial line.  The proof first obtains an invertible module from
effective descent and the PID calculation, then consumes the checked Picard triviality theorem
for the prime localization. -/
noncomputable def MultiplicativeUnitCocycle.primeAwayLinearEquivBase
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    {B : Type} [CommRing B]
    [Algebra (Localization.Away (ℓ : ℤ)) B] [Nontrivial B]
    (c : MultiplicativeUnitCocycle
      (A := Localization.Away (ℓ : ℤ)) (B := B))
    (hf : (algebraMap (Localization.Away (ℓ : ℤ)) B).FaithfullyFlat) :
    c.descendedModule hf ≃ₗ[Localization.Away (ℓ : ℤ)]
      Localization.Away (ℓ : ℤ) := by
  let A := Localization.Away (ℓ : ℤ)
  letI : Nontrivial A := primeAway_nontrivial ℓ hℓ
  letI : IsDomain A := NoZeroDivisors.to_isDomain _
  letI : IsPrincipalIdealRing A :=
    MultiplicativeKummer.away_isPrincipalIdealRing ℓ hℓ
  let e : c.descendedModule hf ≃ₗ[A] A :=
    c.descendedModuleLinearEquivBase hf
  letI : Module.Invertible A (c.descendedModule hf) :=
    Module.Invertible.congr e.symm
  exact MultiplicativeKummer.awayInvertibleModuleLinearEquiv
    ℓ hℓ (c.descendedModule hf)

end AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
