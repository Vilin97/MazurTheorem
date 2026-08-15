/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/

import MazurTorsion.Upstream.CoherentCohomologyFinite.ProperCohomologyFromRelativeSerre
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveCoordinateMaps
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreAffineComparisons

/-!
# Finite-dimensional coherent cohomology over the rationals

This is the public boundary of the exact-pin coherent-cohomology port.  The
internal development constructs the relative Serre comparison and projective
coordinate inputs separately; this module assembles them without exposing
those implementation interfaces to downstream geometry.

The result deliberately retains the source theorem's rational base and its
canonical rationalization of the underlying integral cohomology group.  It
does not claim a field-linear comparison for an arbitrary base field.  The
named degree-one consumer below is the interface intended for genus-related
work over `ℚ`; a genuinely field-relative Jacobian consumer must first supply
the corresponding scalar comparison rather than identifying the two modules
definitionally.
-/

open CategoryTheory AlgebraicGeometry TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

variable {X : Scheme.{0}} {M : X.Modules}

noncomputable local instance facadeCohomologyAddCommGroup
    {Z : TopCat.{0}} (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Coherent cohomology of a proper rational scheme is finite after canonical
rationalization of its underlying integral cohomology group. -/
theorem finiteDimensional
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    [M.IsFiniteType] [M.IsQuasicoherent] (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) :=
  coherentCohomologyFinite_of_relativeSerreInputs
    f hasRelativeSerreAffineComparisons hasRelativeProjectiveCoordinateMaps M n

/-- The degree-one specialization consumed by genus constructions over `ℚ`. -/
theorem hOneFinite
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    [M.IsFiniteType] [M.IsQuasicoherent] :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H 1) :=
  finiteDimensional f 1

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
