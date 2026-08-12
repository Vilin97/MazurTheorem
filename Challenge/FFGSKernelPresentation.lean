/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic

/-!
# Challenge: package a finite-flat scheme-theoretic kernel

The underlying pullback kernel is compiled.  Under explicit finiteness and flatness assumptions,
construct its inherited commutative group object and certify the inclusion.  The hypotheses are
not to be removed: an arbitrary kernel is not formally flat over an arbitrary base.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCommGroupScheme

namespace MazurTheorem.Challenge

universe u

/-- A scheme-theoretic kernel known to be finite and flat admits the corresponding certified
finite-flat commutative group-scheme presentation. -/
theorem ffgs_kernelPresentation_exists_of_finite_flat
    {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)] :
    Nonempty (KernelPresentation f) := sorry

end MazurTheorem.Challenge
