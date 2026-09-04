/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCohomologyExact
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf
import MazurTorsion.Upstream.SchemeModuleCohomologyHZero

/-!
# Linear connecting maps for scheme-module cohomology

For a short exact sequence of modules on a scheme, the long exact sequence of
the underlying additive sheaves supplies a genuine connecting homomorphism.
This file proves that homomorphism linear for the canonical action of global
functions constructed in `SchemeModuleCohomologyHZero`.

The key point is that multiplication by one global function is a morphism of
the whole short complex.  Naturality of the Ext connecting class then gives
linearity.  Thus the construction uses the existing Ext-based cohomology and
its actual long exact sequence; it does not transport an action through a
chosen cover or introduce a second connecting map.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- Multiplication by a global function on all three terms of a short complex.
The two squares commute by linearity of the coefficient morphisms. -/
def globalSmulShortComplexHom
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (r : Γ(X, ⊤)) :
    S ⟶ S :=
  ShortComplex.homMk
    (globalSmulHom S.X₁ r)
    (globalSmulHom S.X₂ r)
    (globalSmulHom S.X₃ r)
    (globalSmulHom_naturality S.f r)
    (globalSmulHom_naturality S.g r)

/-- The genuine connecting homomorphism in scheme-module cohomology.  It is
the Ext connecting map for the short exact sequence of underlying additive
sheaves. -/
noncomputable def cohomologyConnectingHom
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    H S.X₃ n₀ →+ H S.X₁ n₁ :=
  CategoryTheory.Sheaf.H.δ
    (ShortComplex.ShortExact.map_of_exact hS
      (Scheme.Modules.toSheaf X)) n₀ n₁ h

/-- The connecting homomorphism is linear over the ring of global functions
for the canonical, cover-independent cohomology actions. -/
noncomputable def cohomologyConnectingLinearMap
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    letI := globalSectionsCohomologyModule S.X₃ n₀
    letI := globalSectionsCohomologyModule S.X₁ n₁
    H S.X₃ n₀ →ₗ[Γ(X, ⊤)] H S.X₁ n₁ := by
  letI := globalSectionsCohomologyModule S.X₃ n₀
  letI := globalSectionsCohomologyModule S.X₁ n₁
  refine
    { toFun := cohomologyConnectingHom hS n₀ n₁ h
      map_add' := (cohomologyConnectingHom hS n₀ n₁ h).map_add
      map_smul' := ?_ }
  intro r x
  rw [globalSectionsCohomologyModule_smul,
    globalSectionsCohomologyModule_smul]
  let T := S.map (Scheme.Modules.toSheaf X)
  let hT : T.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS
      (Scheme.Modules.toSheaf X)
  let φ : T ⟶ T :=
    (Scheme.Modules.toSheaf X).mapShortComplex.map
      (globalSmulShortComplexHom S r)
  have hnatural :=
    CategoryTheory.Sheaf.H.δ_naturality n₀ n₁ h hT hT φ x
  change cohomologyConnectingHom hS n₀ n₁ h
      ((zariskiFunctor X n₀).map (globalSmulHom S.X₃ r) x) =
    (zariskiFunctor X n₁).map (globalSmulHom S.X₁ r)
      (cohomologyConnectingHom hS n₀ n₁ h x) at hnatural
  exact hnatural

/-- The bundled linear connecting map has the same underlying function as the
Ext connecting homomorphism. -/
theorem cohomologyConnectingLinearMap_apply
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    letI := globalSectionsCohomologyModule S.X₃ n₀
    letI := globalSectionsCohomologyModule S.X₁ n₁
    cohomologyConnectingLinearMap hS n₀ n₁ h x =
      cohomologyConnectingHom hS n₀ n₁ h x := by
  rfl

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
