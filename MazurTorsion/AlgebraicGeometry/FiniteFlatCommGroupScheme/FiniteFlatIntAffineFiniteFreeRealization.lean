/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteFlatAffineRealizationExistence

/-!
# Finite-free affine models over the integers

Every finite-flat commutative group scheme over the affine base `Spec ℤ` is affine.  Its
coordinate algebra is finite and flat over `ℤ`, hence finitely generated, torsion-free, and
free.  This upgrades the existing finite-flat affine realization theorem to an actual
finite-free Hopf-coordinate model.

No classification of the resulting model is asserted here.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

/-- Every finite-flat commutative group scheme over `Spec ℤ` has an actual finite-free affine
Hopf-coordinate realization. -/
theorem exists_affineFiniteFree_realization_int
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ))) :
    ∃ A : AffineFiniteFreeCommGroupScheme ℤ, Nonempty (G ≅ A.realize) := by
  obtain ⟨A, ⟨e⟩⟩ := G.exists_affineFiniteFlat_realization
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
  have hFreeAlg :
      @Module.Free ℤ A.coordinates _ _ Algebra.toModule :=
    hModule.symm ▸ (inferInstance : Module.Free ℤ A.coordinates)
  let A' : AffineFiniteFreeCommGroupScheme ℤ :=
    ⟨A.obj, hFreeAlg, hFiniteAlg⟩
  refine ⟨A', ⟨?_⟩⟩
  exact e

/-- A chosen finite-free affine Hopf model of a geometric finite-flat group scheme over
`Spec ℤ`. -/
noncomputable def affineFiniteFreeModelInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ))) :
    AffineFiniteFreeCommGroupScheme ℤ :=
  (exists_affineFiniteFree_realization_int G).choose

/-- The actual realization isomorphism for the chosen finite-free affine model. -/
noncomputable def affineFiniteFreeModelIsoInt
    (G : FiniteFlatCommGroupScheme (Spec (.of ℤ))) :
    G ≅ (affineFiniteFreeModelInt G).realize :=
  (exists_affineFiniteFree_realization_int G).choose_spec.some

end AlgebraicGeometry.FiniteFlatCommGroupScheme
