/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleQuasicoherent

/-!
# Finite morphisms preserve finite-type quasicoherent modules

This supplies the finite-morphism analogue of the closed-immersion theorem
in the retained AINTLIB quasicoherent-module substrate.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem pushforward_sections_module_finite_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {M : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (U : Y.affineOpens) :
    Module.Finite Γ(Y, U.1) Γ((pushforward f).obj M, U.1) := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  let a : Γ(Y, U.1) →+* Γ(X, V.1) := (f.app U.1).hom
  letI : Algebra Γ(Y, U.1) Γ(X, V.1) := a.toAlgebra
  letI : Module Γ(Y, U.1) Γ(M, V.1) :=
    ((pushforward f).obj M).val.obj (.op U.1) |>.isModule
  letI : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(M, V.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Finite Γ(Y, U.1) Γ(X, V.1) := by
    change a.Finite
    exact f.finite_app U.1 U.2
  letI : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M V
  exact Module.Finite.trans Γ(X, V.1) Γ(M, V.1)

/-- Pushforward along a finite morphism preserves finite-type
quasicoherent modules. -/
theorem isFiniteType_pushforward_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {M : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pushforward f).obj M).IsFiniteType := by
  let N := (pushforward f).obj M
  letI : N.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom f
  exact isFiniteType_of_sections_module_finite N
    (pushforward_sections_module_finite_of_isFinite f)

end AlgebraicGeometry.Scheme.Modules
