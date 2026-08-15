/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.ProperCurveCohomologyFinite
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafUnitQuasicoherent
import MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced

/-!
# The cohomological genus of a curve over a field

This file defines the genus using genuine sheaf cohomology and the canonical
ground-field action induced by the structure morphism.  The definition does
not choose an affine cover, a finite morphism, a divisor, or a rational point.

The named downstream consumer is
`MazurTorsion.AlgebraicGeometry.Jacobian.LeanEval`.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian

universe u

open SchemeModuleCohomology

/-- The structure sheaf regarded as an object of the scheme's category of
modules. -/
def structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The genuine first cohomology group of the structure sheaf. -/
abbrev StructureHOne (X : Scheme.{u}) :=
  SchemeModuleCohomology.H (structureModule X) 1

/-- The canonical ground-field action on `H¹(X, O_X)`. -/
@[instance_reducible]
noncomputable def structureHOneFieldModule
    (K : Type u) [Field K] (C : Over (Spec (.of K))) :
    Module K (StructureHOne C.left) :=
  hOneCanonicalFieldModule K C.left C.hom (structureModule C.left)

/-- The cohomological genus.  `Module.finrank` is defined for every module;
the proper-curve finite-dimensionality theorem is a separate fact rather than
a hidden choice in this definition. -/
noncomputable def genus
    (K : Type u) [Field K] (C : Over (Spec (.of K))) : ℕ := by
  letI := structureHOneFieldModule K C
  exact Module.finrank K (StructureHOne C.left)

/-- Unfolding the genus gives the finite rank of genuine structure-sheaf
`H¹` for the canonical field action. -/
theorem genus_eq_finrank
    (K : Type u) [Field K] (C : Over (Spec (.of K))) :
    letI := structureHOneFieldModule K C
    genus K C = Module.finrank K (StructureHOne C.left) := by
  rfl

/-- Genuine structure-sheaf `H¹` is finite-dimensional for every proper,
smooth, geometrically irreducible relative curve.  No rational point is
needed: a nonzero maximal ideal on a standard-smooth affine chart supplies a
codimension-one point. -/
theorem structureHOne_finiteDimensional
    (K : Type u) [Field K] (C : Over (Spec (.of K)))
    [GeometricallyIrreducible C.hom] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] :
    letI := structureHOneFieldModule K C
    FiniteDimensional K (StructureHOne C.left) := by
  letI : IsIntegral C.left :=
    SmoothCurveReduced.scheme_isIntegral_of_geometricallyIrreducible_of_smoothRelativeDimension_one
      K C.left C.hom
  let x : TauCeti.AlgebraicGeometry.CodimensionOnePoint C.left :=
    Classical.choice (SmoothCurveReduced.nonempty_codimensionOnePoint K C.left C.hom)
  letI : (structureModule C.left).IsQuasicoherent :=
    CoherentCohomology.SheafUnit.unit_isQuasicoherent
      (C := C.left.Opens) (J := Opens.grothendieckTopology C.left)
      C.left.ringCatSheaf
  letI : (structureModule C.left).IsFiniteType :=
    CoherentCohomology.SheafUnit.unit_isFiniteType
      (C := C.left.Opens) (J := Opens.grothendieckTopology C.left)
      C.left.ringCatSheaf
  exact
    genuineSheafHOneCanonical_finiteDimensional_of_codimensionOnePoint
      K C.left C.hom x (structureModule C.left)

/-- A rational point supplies the codimension-one point used in the checked
finite-map-to-`P¹` proof, so the canonical structure-sheaf `H¹` action is
finite-dimensional.  The point is a proof input only; it does not occur in
the definition of `genus`. -/
theorem structureHOne_finiteDimensional_of_rationalPoint
    (K : Type u) [Field K] (C : Over (Spec (.of K)))
    [GeometricallyIrreducible C.hom] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    (P : Spec (.of K) ⟶ C.left) (hP : P ≫ C.hom = 𝟙 _) :
    letI := structureHOneFieldModule K C
    FiniteDimensional K (StructureHOne C.left) := by
  letI : IsIntegral C.left :=
    SmoothCurveReduced.scheme_isIntegral_of_geometricallyIrreducible_of_smoothRelativeDimension_one
        K C.left C.hom
  let s : SmoothCurveRationalSection K C.left C.hom :=
    { hom := P
      hom_comp := hP }
  letI : (structureModule C.left).IsQuasicoherent :=
    CoherentCohomology.SheafUnit.unit_isQuasicoherent
      (C := C.left.Opens) (J := Opens.grothendieckTopology C.left)
      C.left.ringCatSheaf
  letI : (structureModule C.left).IsFiniteType :=
    CoherentCohomology.SheafUnit.unit_isFiniteType
      (C := C.left.Opens) (J := Opens.grothendieckTopology C.left)
      C.left.ringCatSheaf
  exact
    genuineSheafHOneCanonical_finiteDimensional_of_rationalSection
      K C.left C.hom s (structureModule C.left)

end MazurTorsion.AlgebraicGeometry.Jacobian
