/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic

/-!
# Checked bridge: package a finite-flat scheme-theoretic kernel

The BASIC API constructs the inherited commutative group object and certifies its inclusion under
explicit finiteness and flatness assumptions.  The hypotheses are not to be removed: an arbitrary
kernel is not formally flat over an arbitrary base.  This file retains the original contract as a
checked bridge.
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
    Nonempty (KernelPresentation f) :=
  AlgebraicGeometry.FiniteFlatCommGroupScheme.kernelPresentation_exists_of_finite_flat f

end MazurTheorem.Challenge
