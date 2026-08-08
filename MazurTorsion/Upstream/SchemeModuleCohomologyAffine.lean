/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import MazurTorsion.Upstream.SchemeModuleCohomologyHZero

/-!
# Degree-zero cohomology of affine tilde modules

This file is a concrete downstream consumer of
`SchemeModuleCohomology.hZeroEquivGlobalSections`.  Mathlib's affine
global-sections equivalence for a tilde module then recovers the original
coefficient module.

The linear version restricts the transported `Γ(Spec R, ⊤)`-action on
degree-zero cohomology along `R → Γ(Spec R, ⊤)`.  It is therefore
compatible with Mathlib's existing `R`-linear `tilde.isoTop`, and finite
generation transfers back from the coefficient module.

No positive-degree affine acyclicity statement is made here.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- On an affine scheme, the degree-zero cohomology of the tilde sheaf of a
module is the original module. -/
noncomputable def affineTildeHZeroEquiv {R : CommRingCat.{u}}
    (M : ModuleCat R) : H (tilde M) 0 ≃+ M :=
  (hZeroEquivGlobalSections (tilde M)).trans
    (tilde.isoTop M).symm.toLinearEquiv.toAddEquiv

/-- The `R`-module structure on affine tilde `H⁰`, obtained by restricting
the transported global-functions action along
`R → Γ(Spec R, ⊤)`.  As for `hZeroModule`, this is an explicit named
structure rather than a global instance. -/
@[reducible]
noncomputable def affineTildeHZeroModule {R : CommRingCat.{u}}
    (M : ModuleCat R) : Module R (H (tilde M) 0) :=
  letI := hZeroModule (tilde M)
  Module.compHom (H (tilde M) 0) (algebraMap R Γ(Spec R, ⊤))

/-- The restricted affine `R`-action and the transported global-functions
action form the expected scalar tower. -/
theorem affineTildeHZeroScalarTower {R : CommRingCat.{u}}
    (M : ModuleCat R) :
    letI := hZeroModule (tilde M)
    letI := affineTildeHZeroModule M
    IsScalarTower R Γ(Spec R, ⊤) (H (tilde M) 0) :=
  letI := hZeroModule (tilde M)
  letI := affineTildeHZeroModule M
  IsScalarTower.of_compHom R Γ(Spec R, ⊤) (H (tilde M) 0)

/-- On an affine scheme, the degree-zero cohomology/global-sections
comparison followed by `tilde.isoTop` is linear over the coefficient ring. -/
noncomputable def affineTildeHZeroLinearEquiv {R : CommRingCat.{u}}
    (M : ModuleCat R) :
    letI := hZeroModule (tilde M)
    letI := affineTildeHZeroModule M
    H (tilde M) 0 ≃ₗ[R] M := by
  letI := hZeroModule (tilde M)
  letI := affineTildeHZeroModule M
  letI := affineTildeHZeroScalarTower M
  exact
    (hZeroLinearEquivGlobalSections (tilde M)).restrictScalars R |>.trans
      (tilde.isoTop M).symm.toLinearEquiv

/-- Finite generation of a coefficient module transfers to degree-zero
cohomology of its affine tilde sheaf for the restricted global-functions
action. -/
theorem affineTildeHZero_finite {R : CommRingCat.{u}} (M : ModuleCat R)
    [Module.Finite R M] :
    letI := hZeroModule (tilde M)
    letI := affineTildeHZeroModule M
    Module.Finite R (H (tilde M) 0) := by
  letI := hZeroModule (tilde M)
  letI := affineTildeHZeroModule M
  exact Module.Finite.equiv (affineTildeHZeroLinearEquiv M).symm

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
