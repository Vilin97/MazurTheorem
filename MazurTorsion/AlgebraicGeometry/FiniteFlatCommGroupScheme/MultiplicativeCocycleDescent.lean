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

The arithmetic theorem specializes this construction to `ℤ[1/ℓ]` and consumes the checked
Picard triviality of that ring.  The final section evaluates a represented `G_m` cocycle on a
singleton affine family at the tensor-product overlap and proves that it supplies exactly this
normalized tensor-unit data.  It does not construct refinements or gauges for arbitrary covers
and therefore does not assert an ambient `H¹(G_m)` vanishing theorem.
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

/-- Embed an algebra into the first factor of its right-associated threefold tensor product. -/
noncomputable def firstToTriple : B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.includeLeft

/-- Embed an algebra into the second factor of its right-associated threefold tensor product. -/
noncomputable def secondToTriple : B →ₐ[A] tripleRing (A := A) (B := B) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft

/-- Embed an algebra into the third factor of its right-associated threefold tensor product. -/
noncomputable def thirdToTriple : B →ₐ[A] tripleRing (A := A) (B := B) :=
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

/-! ## Represented multiplicative cocycles on a singleton affine family -/

open AffineCommGroupScheme
open CategoryTheory.PresheafOfGroups

/-- A represented multiplicative-group cocycle on the singleton family consisting of
`Spec B → Spec A`.  No covering property is needed to define the cocycle; faithful flatness is
supplied only when it is passed to effective descent. -/
abbrev RepresentedMultiplicativeOneCocycle :=
  OneCocycle
    (pointPresheaf (multiplicativeScheme A))
    (fun _ : Unit ↦ testObject (R := A) B)

/-- The first projection from the affine pair overlap `Spec (B ⊗_A B)` to `Spec B`. -/
noncomputable def singletonPairLeft :
    testObject (R := A) (B ⊗[A] B) ⟶ testObject (R := A) B :=
  testObjectMap (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)

/-- The second projection from the affine pair overlap `Spec (B ⊗_A B)` to `Spec B`. -/
noncomputable def singletonPairRight :
    testObject (R := A) (B ⊗[A] B) ⟶ testObject (R := A) B :=
  testObjectMap (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)

/-- Evaluate a represented multiplicative cocycle on the two projections of the singleton
affine pair overlap and read the resulting point as a unit. -/
noncomputable def representedOverlapUnit
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B)) :
    (B ⊗[A] B)ˣ :=
  multiplicativePointMulEquiv A (B ⊗[A] B)
    (c.ev () () singletonPairLeft singletonPairRight)

private theorem testObjectMap_comp
    {C D E : Type u} [CommRing C] [CommRing D] [CommRing E]
    [Algebra A C] [Algebra A D] [Algebra A E]
    (f : C →ₐ[A] D) (g : D →ₐ[A] E) :
    testObjectMap g ≫ testObjectMap f = testObjectMap (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  rfl

private noncomputable def singletonDiagonal :
    testObject (R := A) B ⟶ testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (Algebra.TensorProduct.lmul' A)

private theorem singletonDiagonal_pairLeft :
    singletonDiagonal (A := A) (B := B) ≫ singletonPairLeft = 𝟙 _ := by
  rw [singletonDiagonal, singletonPairLeft, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id, Spec.map_inj]
  ext b
  simp

private theorem singletonDiagonal_pairRight :
    singletonDiagonal (A := A) (B := B) ≫ singletonPairRight = 𝟙 _ := by
  rw [singletonDiagonal, singletonPairRight, testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id, Spec.map_inj]
  ext b
  simp

/-- The unit obtained from a represented singleton-family cocycle restricts to one along the
diagonal `Spec B → Spec (B ⊗_A B)`. -/
theorem representedOverlapUnit_normalization
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B)) :
    Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom
      (representedOverlapUnit c) = 1 := by
  letI : CommGroup ((multiplicative A).Point B) :=
    AffineCommGroupScheme.pointCommGroup (multiplicative A) B
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (singletonPairLeft (A := A) (B := B))
      (singletonPairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := Algebra.TensorProduct.lmul' A) (x := x)
  change Units.map (Algebra.TensorProduct.lmul' A).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = 1
  rw [← hnat]
  have hpre := c.ev_precomp () ()
    (singletonDiagonal (A := A) (B := B))
    (singletonPairLeft (A := A) (B := B))
    (singletonPairRight (A := A) (B := B))
  change singletonDiagonal (A := A) (B := B) ≫
      c.ev () () (singletonPairLeft (A := A) (B := B))
        (singletonPairRight (A := A) (B := B)) =
    c.ev () ()
      (singletonDiagonal (A := A) (B := B) ≫
        singletonPairLeft (A := A) (B := B))
      (singletonDiagonal (A := A) (B := B) ≫
        singletonPairRight (A := A) (B := B)) at hpre
  rw [singletonDiagonal_pairLeft, singletonDiagonal_pairRight] at hpre
  dsimp only [singletonDiagonal] at hpre
  have hrefl := OneCocycle.ev_refl
    (pointPresheaf (multiplicativeScheme A))
    (fun _ : Unit ↦ testObject (R := A) B) c ()
    (𝟙 (testObject (R := A) B))
  change c.ev () () (𝟙 _) (𝟙 _) = (1 : (multiplicative A).Point B) at hrefl
  change testObjectMap (Algebra.TensorProduct.lmul' A) ≫ x =
      c.ev () () (𝟙 _) (𝟙 _) at hpre
  rw [hpre, hrefl]
  exact map_one (multiplicativePointMulEquiv A B)

/-- The first projection from the singleton triple overlap to `Spec B`. -/
noncomputable def singletonTripleFirst :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) B :=
  testObjectMap (firstToTriple (A := A) (B := B))

/-- The second projection from the singleton triple overlap to `Spec B`. -/
noncomputable def singletonTripleSecond :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) B :=
  testObjectMap (secondToTriple (A := A) (B := B))

/-- The third projection from the singleton triple overlap to `Spec B`. -/
noncomputable def singletonTripleThird :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) B :=
  testObjectMap (thirdToTriple (A := A) (B := B))

private noncomputable def singletonPullTwelve :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (pairTwelve (A := A) (B := B))

private noncomputable def singletonPullTwentyThree :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (pairTwentyThree (A := A) (B := B))

private noncomputable def singletonPullThirteen :
    testObject (R := A) (tripleRing (A := A) (B := B)) ⟶
      testObject (R := A) (B ⊗[A] B) :=
  testObjectMap (pairThirteen (A := A) (B := B))

private theorem singletonPullTwelve_pairLeft :
    singletonPullTwelve (A := A) (B := B) ≫ singletonPairLeft =
      singletonTripleFirst := by
  rw [singletonPullTwelve, singletonPairLeft, singletonTripleFirst,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwelve, firstToTriple, secondToTriple]

private theorem singletonPullTwelve_pairRight :
    singletonPullTwelve (A := A) (B := B) ≫ singletonPairRight =
      singletonTripleSecond := by
  rw [singletonPullTwelve, singletonPairRight, singletonTripleSecond,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwelve, firstToTriple, secondToTriple]

private theorem singletonPullTwentyThree_pairLeft :
    singletonPullTwentyThree (A := A) (B := B) ≫ singletonPairLeft =
      singletonTripleSecond := by
  rw [singletonPullTwentyThree, singletonPairLeft, singletonTripleSecond,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwentyThree, secondToTriple]

private theorem singletonPullTwentyThree_pairRight :
    singletonPullTwentyThree (A := A) (B := B) ≫ singletonPairRight =
      singletonTripleThird := by
  rw [singletonPullTwentyThree, singletonPairRight, singletonTripleThird,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairTwentyThree, thirdToTriple]

private theorem singletonPullThirteen_pairLeft :
    singletonPullThirteen (A := A) (B := B) ≫ singletonPairLeft =
      singletonTripleFirst := by
  rw [singletonPullThirteen, singletonPairLeft, singletonTripleFirst,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairThirteen, firstToTriple, thirdToTriple]

private theorem singletonPullThirteen_pairRight :
    singletonPullThirteen (A := A) (B := B) ≫ singletonPairRight =
      singletonTripleThird := by
  rw [singletonPullThirteen, singletonPairRight, singletonTripleThird,
    testObjectMap_comp]
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _
  rw [Spec.map_inj]
  ext b
  simp [pairThirteen, firstToTriple, thirdToTriple]

/-- Pulling the represented overlap unit to factors `(1,2)` agrees with evaluating the
represented cocycle on the first and second projections of the triple overlap. -/
theorem representedOverlapUnit_pairTwelve
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B)) :
    Units.map (pairTwelve (A := A) (B := B)).toMonoidHom
        (representedOverlapUnit c) =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))
        (c.ev () () (singletonTripleFirst (A := A) (B := B))
          (singletonTripleSecond (A := A) (B := B))) := by
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (singletonPairLeft (A := A) (B := B))
      (singletonPairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pairTwelve (A := A) (B := B)) (x := x)
  change Units.map (pairTwelve (A := A) (B := B)).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp () ()
    (singletonPullTwelve (A := A) (B := B))
    (singletonPairLeft (A := A) (B := B))
    (singletonPairRight (A := A) (B := B))
  change singletonPullTwelve (A := A) (B := B) ≫ x =
    c.ev () ()
      (singletonPullTwelve (A := A) (B := B) ≫
        singletonPairLeft (A := A) (B := B))
      (singletonPullTwelve (A := A) (B := B) ≫
        singletonPairRight (A := A) (B := B)) at hpre
  rw [singletonPullTwelve_pairLeft, singletonPullTwelve_pairRight] at hpre
  dsimp only [singletonPullTwelve] at hpre
  exact congrArg
    (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))) hpre

/-- Pulling the represented overlap unit to factors `(2,3)` agrees with evaluating the
represented cocycle on the second and third projections of the triple overlap. -/
theorem representedOverlapUnit_pairTwentyThree
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B)) :
    Units.map (pairTwentyThree (A := A) (B := B)).toMonoidHom
        (representedOverlapUnit c) =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))
        (c.ev () () (singletonTripleSecond (A := A) (B := B))
          (singletonTripleThird (A := A) (B := B))) := by
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (singletonPairLeft (A := A) (B := B))
      (singletonPairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pairTwentyThree (A := A) (B := B)) (x := x)
  change Units.map (pairTwentyThree (A := A) (B := B)).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp () ()
    (singletonPullTwentyThree (A := A) (B := B))
    (singletonPairLeft (A := A) (B := B))
    (singletonPairRight (A := A) (B := B))
  change singletonPullTwentyThree (A := A) (B := B) ≫ x =
    c.ev () ()
      (singletonPullTwentyThree (A := A) (B := B) ≫
        singletonPairLeft (A := A) (B := B))
      (singletonPullTwentyThree (A := A) (B := B) ≫
        singletonPairRight (A := A) (B := B)) at hpre
  rw [singletonPullTwentyThree_pairLeft,
    singletonPullTwentyThree_pairRight] at hpre
  dsimp only [singletonPullTwentyThree] at hpre
  exact congrArg
    (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))) hpre

/-- Pulling the represented overlap unit to factors `(1,3)` agrees with evaluating the
represented cocycle on the first and third projections of the triple overlap. -/
theorem representedOverlapUnit_pairThirteen
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B)) :
    Units.map (pairThirteen (A := A) (B := B)).toMonoidHom
        (representedOverlapUnit c) =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))
        (c.ev () () (singletonTripleFirst (A := A) (B := B))
          (singletonTripleThird (A := A) (B := B))) := by
  let x : (multiplicative A).Point (B ⊗[A] B) :=
    c.ev () () (singletonPairLeft (A := A) (B := B))
      (singletonPairRight (A := A) (B := B))
  have hnat := multiplicativePointMulEquiv_testObjectMap
    (R := A) (f := pairThirteen (A := A) (B := B)) (x := x)
  change Units.map (pairThirteen (A := A) (B := B)).toMonoidHom
      (multiplicativePointMulEquiv A (B ⊗[A] B) x) = _
  rw [← hnat]
  have hpre := c.ev_precomp () ()
    (singletonPullThirteen (A := A) (B := B))
    (singletonPairLeft (A := A) (B := B))
    (singletonPairRight (A := A) (B := B))
  change singletonPullThirteen (A := A) (B := B) ≫ x =
    c.ev () ()
      (singletonPullThirteen (A := A) (B := B) ≫
        singletonPairLeft (A := A) (B := B))
      (singletonPullThirteen (A := A) (B := B) ≫
        singletonPairRight (A := A) (B := B)) at hpre
  rw [singletonPullThirteen_pairLeft, singletonPullThirteen_pairRight] at hpre
  dsimp only [singletonPullThirteen] at hpre
  exact congrArg
    (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B))) hpre

/-- Evaluate a represented `G_m` cocycle on a singleton affine overlap and package the result
as normalized tensor-unit descent data.  Normalization comes from `ev_refl`; the tensor
`(1,2)(2,3)=(1,3)` identity is exactly `OneCocycle.ev_trans` transported through the represented
point/unit equivalence. -/
noncomputable def RepresentedMultiplicativeOneCocycle.toMultiplicativeUnitCocycle
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B)) :
    MultiplicativeUnitCocycle (A := A) (B := B) where
  unit := representedOverlapUnit c
  normalization := representedOverlapUnit_normalization c
  cocycle := by
    letI : CommGroup ((multiplicative A).Point (tripleRing (A := A) (B := B))) :=
      AffineCommGroupScheme.pointCommGroup (multiplicative A)
        (tripleRing (A := A) (B := B))
    let x₁₂ : (multiplicative A).Point (tripleRing (A := A) (B := B)) :=
      c.ev () () (singletonTripleFirst (A := A) (B := B))
        (singletonTripleSecond (A := A) (B := B))
    let x₂₃ : (multiplicative A).Point (tripleRing (A := A) (B := B)) :=
      c.ev () () (singletonTripleSecond (A := A) (B := B))
        (singletonTripleThird (A := A) (B := B))
    let x₁₃ : (multiplicative A).Point (tripleRing (A := A) (B := B)) :=
      c.ev () () (singletonTripleFirst (A := A) (B := B))
        (singletonTripleThird (A := A) (B := B))
    rw [representedOverlapUnit_pairTwelve,
      representedOverlapUnit_pairTwentyThree,
      representedOverlapUnit_pairThirteen]
    change multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)) x₁₂ *
        multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)) x₂₃ =
      multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)) x₁₃
    rw [← map_mul]
    have htrans := c.ev_trans () () ()
      (singletonTripleFirst (A := A) (B := B))
      (singletonTripleSecond (A := A) (B := B))
      (singletonTripleThird (A := A) (B := B))
    change x₁₂ * x₂₃ = x₁₃ at htrans
    exact congrArg
      (multiplicativePointMulEquiv A (tripleRing (A := A) (B := B)))
      htrans

@[simp]
theorem RepresentedMultiplicativeOneCocycle.toMultiplicativeUnitCocycle_unit
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B)) :
    c.toMultiplicativeUnitCocycle.unit = representedOverlapUnit c :=
  rfl

/-- The effective `A`-module descended from a represented multiplicative cocycle on the
faithfully-flat singleton affine family `Spec B → Spec A`. -/
noncomputable def RepresentedMultiplicativeOneCocycle.descendedModule
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) : ModuleCat A :=
  c.toMultiplicativeUnitCocycle.descendedModule hf

/-- The represented cocycle's effective descent becomes the regular line after base change to
the faithfully-flat singleton cover. -/
noncomputable def RepresentedMultiplicativeOneCocycle.baseChangeIso
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) :
    (extendScalars (algebraMap A B)).obj (c.descendedModule hf) ≅
      ModuleCat.of B B :=
  c.toMultiplicativeUnitCocycle.baseChangeIso hf

/-- A represented multiplicative cocycle on a faithfully-flat singleton affine cover of
`Spec ℤ[1/ℓ]` descends to the trivial line.  This is the direct represented-cocycle consumer of
the tensor-unit comparison, comonadic effectiveness, and prime-away Picard calculation. -/
noncomputable def RepresentedMultiplicativeOneCocycle.primeAwayLinearEquivBase
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    {B : Type} [CommRing B]
    [Algebra (Localization.Away (ℓ : ℤ)) B] [Nontrivial B]
    (c : RepresentedMultiplicativeOneCocycle
      (A := Localization.Away (ℓ : ℤ)) (B := B))
    (hf : (algebraMap (Localization.Away (ℓ : ℤ)) B).FaithfullyFlat) :
    c.descendedModule hf ≃ₗ[Localization.Away (ℓ : ℤ)]
      Localization.Away (ℓ : ℤ) :=
  c.toMultiplicativeUnitCocycle.primeAwayLinearEquivBase ℓ hℓ hf

end AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
