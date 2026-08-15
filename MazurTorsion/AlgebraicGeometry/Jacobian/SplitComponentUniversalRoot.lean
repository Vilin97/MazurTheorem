/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitMonicRootFamily
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# The universal root family on a split component

Fix a component of the degree-`d` symmetric power of `m` split étale
sheets.  Its coefficient space has one affine coordinate for every root,
grouped by sheet.  On each sheet we form the universal monic polynomial of
the corresponding multiplicity and then take the product of their root
algebras.

The resulting affine morphism is finite flat of constant rank `d`.  This is
the complete commutative-algebra calculation required on each component of
the fpqc split chart.  The named downstream consumer is the local
identification of `PointedIncidenceDescent.pointedUniversalEffectiveDivisor`.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentUniversalRoot

open SplitFiniteSymmetricQuotient
open SplitMonicRootFamily

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)

/-- Joint coefficient ring for the monic polynomials on all sheets of one
split component. -/
abbrev coefficientRing := MvPolynomial (componentRootIndex d m c) R

/-- Embed the coefficient variables belonging to one sheet into the joint
coefficient ring. -/
noncomputable def sheetCoefficientHom (j : Fin m) :
    MvPolynomial (Fin (sheetMultiplicity d m c j)) R →ₐ[R]
      coefficientRing R d m c :=
  MvPolynomial.rename fun i ↦ ⟨j, i⟩

/-- The universal monic polynomial of the prescribed multiplicity on one
sheet, with coefficients in the joint coefficient ring. -/
noncomputable def sheetPolynomial (j : Fin m) :
    Polynomial.MonicDegreeEq (coefficientRing R d m c)
      (sheetMultiplicity d m c j) :=
  (Polynomial.MonicDegreeEq.freeMonic R
    (sheetMultiplicity d m c j)).map
      (sheetCoefficientHom R d m c j).toRingHom

/-- The union of the universal root families on all sheets of one split
component. -/
noncomputable abbrev projection :=
  SplitMonicRootFamily.projection (coefficientRing R d m c) m
    (sheetMultiplicity d m c) (sheetPolynomial R d m c)

instance projection_isFinite : IsFinite (projection R d m c) := by
  dsimp only [projection]
  infer_instance

instance projection_flat : Flat (projection R d m c) := by
  dsimp only [projection]
  infer_instance

/-- The universal root family on every split component has constant rank
equal to the original symmetric-power degree. -/
theorem projection_finrank :
    (projection R d m c).finrank = fun _ ↦ d :=
  SplitMonicRootFamily.projection_finrank_of_sheetMultiplicity
    (coefficientRing R d m c) m d c (sheetPolynomial R d m c)

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentUniversalRoot
