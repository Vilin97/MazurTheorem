/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.CategoryTheory.Sites.Limits
import MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicardDescent

/-!
# Degree and the degree-zero relative Picard sheaf

This file fixes the categorical target of the relative degree map.  On a
possibly disconnected test scheme, degree is locally constant rather than a
single integer, so the target is the fppf sheafification of the constant
integer presheaf.  The degree-zero Picard sheaf is its kernel.

`DegreeMap` records the geometric construction still required from Euler
characteristic and cohomology-and-base-change.  It is an input structure, not
an existence assertion.  The named downstream consumer is
`PicardRepresentability`.
-/

noncomputable section

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard

universe u

variable {S X : Scheme.{u}}

/-- A universe-lifted copy of the integers suitable for the large fppf
site. -/
abbrev Integer := ULift.{u + 1} ℤ

/-- The constant integer presheaf on `S`-schemes. -/
noncomputable def integerPresheaf (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.const (Over S)ᵒᵖ).obj (AddCommGrpCat.of Integer)

/-- The fppf sheaf of locally constant integer-valued functions. -/
noncomputable def integerFppfSheaf (S : Scheme.{u}) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (integerPresheaf S)

/-- A base-change-compatible degree map on the fppf relative Picard sheaf.

For a proper flat family of curves this is constructed from
`χ(L) - χ(O)` and cohomology-and-base-change. -/
structure DegreeMap (p : X ⟶ S) where
  /-- Degree as a morphism of fppf sheaves of abelian groups. -/
  hom : fppfSheaf p ⟶ integerFppfSheaf S

/-- The degree-zero relative Picard sheaf. -/
noncomputable def degreeZeroSheaf (p : X ⟶ S) (d : DegreeMap p) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  kernel d.hom

/-- The inclusion of the degree-zero relative Picard sheaf. -/
noncomputable def degreeZeroι (p : X ⟶ S) (d : DegreeMap p) :
    degreeZeroSheaf p d ⟶ fppfSheaf p :=
  kernel.ι d.hom

/-- The degree of every section of the degree-zero sheaf vanishes. -/
theorem degreeZeroι_comp_degree (p : X ⟶ S) (d : DegreeMap p) :
    degreeZeroι p d ≫ d.hom = 0 := by
  exact kernel.condition d.hom

end MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard
