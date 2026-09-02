import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor

open CategoryTheory ModuleCat Comonad TensorProduct

universe u
noncomputable section

namespace T

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

abbrev C :=
  (extendRestrictScalarsAdj (algebraMap A B)).toComonad

def eA :
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

def eB :
    (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[B] B where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

example :
    (C (A := A) (B := B)).obj (ModuleCat.of B B) ≃ₗ[B]
      B ⊗[A] B := by
  let N := (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B N := IsScalarTower.of_compHom A B N
  letI : SMulCommClass A B N :=
    ModuleCat.sMulCommClass_mk (algebraMap A B) B
  let raw : N ⊗[A] N ≃ₗ[B] B ⊗[A] B :=
    AlgebraTensorModule.congr (eB (A := A) (B := B))
      (eA (A := A) (B := B))
  exact raw

end T
