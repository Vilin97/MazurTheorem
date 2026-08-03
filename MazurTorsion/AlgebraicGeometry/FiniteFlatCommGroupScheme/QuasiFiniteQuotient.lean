/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteKernelPresentation
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Quotient

/-!
# Fppf quotient presentations for quasi-finite flat group schemes

Mazur's four integral elementary factors occur in exact sequences of quasi-finite flat group
schemes.  This file records the exact geometric input needed from one such sequence: a supplied
quasi-finite flat quotient, an fppf projection, and an actual geometric presentation of its
kernel.  The kernel presentation gives exactness on represented points without incorrectly
asserting surjectivity on points of every test scheme.

Every existing finite-flat fppf quotient presentation embeds in this interface.  The final
compatibility theorems check that both its projection and its chosen kernel inclusion are
retained, so later quasi-finite cohomology arguments can reuse the checked finite-flat cases.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}}

/-- Underlying scheme morphism of a quasi-finite flat group-scheme morphism. -/
abbrev hom {G H : QuasiFiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    G.scheme ⟶ H.scheme :=
  CommGroupScheme.underlyingHom f.hom

/-- An fppf quotient between quasi-finite flat group schemes, with its actual geometric kernel. -/
structure FppfQuotientPresentation (G : QuasiFiniteFlatCommGroupScheme S) where
  /-- The supplied quotient object. -/
  quotient : QuasiFiniteFlatCommGroupScheme S
  /-- Projection from the middle group scheme to the quotient. -/
  project : G ⟶ quotient
  /-- Flatness of the quotient projection. -/
  project_flat : Flat (hom project)
  /-- Surjectivity of the quotient projection on underlying topological spaces. -/
  project_surjective : Surjective (hom project)
  /-- Local finite presentation of the quotient projection. -/
  project_lfp : LocallyOfFinitePresentation (hom project)
  /-- The chosen geometric kernel of the quotient projection. -/
  kernelPresentation : KernelPresentation project

namespace FppfQuotientPresentation

variable {G : QuasiFiniteFlatCommGroupScheme S}

/-- The supplied projection is an fppf cover on underlying schemes. -/
theorem project_is_fppf (D : FppfQuotientPresentation G) :
    Flat (hom D.project) ∧ Surjective (hom D.project) ∧
      LocallyOfFinitePresentation (hom D.project) :=
  ⟨D.project_flat, D.project_surjective, D.project_lfp⟩

/-- Exactness at the middle represented point functor. -/
theorem project_point_eq_one_iff (D : FppfQuotientPresentation G)
    (T : Over S) (x : CommGroupScheme.Point G.obj T) :
    mapPoint D.project T x = 1 ↔
      x ∈ Set.range (mapPoint D.kernelPresentation.inclusion T) := by
  exact D.kernelPresentation.point_mulExact T x

/-- Regard a checked finite-flat fppf quotient as a quasi-finite one. -/
noncomputable def ofFiniteFlat
    {G : FiniteFlatCommGroupScheme S}
    (D : FiniteFlatCommGroupScheme.FppfQuotientPresentation G)
    [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation D.quotient.obj.X.hom]
    [LocallyOfFinitePresentation D.kernelPresentation.kernel.obj.X.hom] :
    FppfQuotientPresentation (QuasiFiniteFlatCommGroupScheme.ofFiniteFlat G) where
  quotient := QuasiFiniteFlatCommGroupScheme.ofFiniteFlat D.quotient
  project := ofFiniteFlatMap D.project
  project_flat := D.project_flat
  project_surjective := D.project_surjective
  project_lfp := D.project_lfp
  kernelPresentation := KernelPresentation.ofFiniteFlat D.kernelPresentation

/-- The finite-flat adapter retains the original quotient projection. -/
theorem ofFiniteFlat_project
    {G : FiniteFlatCommGroupScheme S}
    (D : FiniteFlatCommGroupScheme.FppfQuotientPresentation G)
    [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation D.quotient.obj.X.hom]
    [LocallyOfFinitePresentation D.kernelPresentation.kernel.obj.X.hom] :
    (ofFiniteFlat D).project = ofFiniteFlatMap D.project :=
  rfl

/-- The finite-flat adapter retains the original geometric kernel inclusion. -/
theorem ofFiniteFlat_kernel_inclusion
    {G : FiniteFlatCommGroupScheme S}
    (D : FiniteFlatCommGroupScheme.FppfQuotientPresentation G)
    [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation D.quotient.obj.X.hom]
    [LocallyOfFinitePresentation D.kernelPresentation.kernel.obj.X.hom] :
    (ofFiniteFlat D).kernelPresentation.inclusion =
      ofFiniteFlatMap D.kernelPresentation.inclusion :=
  KernelPresentation.ofFiniteFlat_inclusion D.kernelPresentation

end FppfQuotientPresentation

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
