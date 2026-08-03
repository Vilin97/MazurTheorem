/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersion

/-!
# The degree-one cotangent consumer

This module records the residue-field-honest checked handoff expected from the modular `q`-expansion
calculation.  For a cusp-normalized morphism from a modular curve to a quotient of its Jacobian,
the remaining Hecke calculation must:

* prove that the induced residue-field map is an isomorphism;
* prove that the curve cotangent space has dimension one over its actual residue field; and
* exhibit a cotangent vector whose image is nonzero (the first-coefficient calculation).

`DegreeOneCotangentCertificate.isCotangentCriterionAt` then supplies both checked first-order
conditions.  This is not yet a formal-immersion theorem: the completed-local-ring equivalence
remains an `MT-X0-INTEGRAL` obligation.  Functoriality of the underlying canonical map for the
composite modular morphism is already checked in the imported core.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory

universe u

/-- Canonical residue-field data needed by Mazur's degree-one cotangent argument.

The `detected` field is deliberately an explicit vector rather than a bare nonzero-map
assumption.  It is the downstream slot filled by a checked nonzero first `q`-coefficient. -/
structure DegreeOneCotangentCertificate
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) where
  /-- The morphism induces an isomorphism on residue fields at the selected points. -/
  residueFieldMap_isIso : IsIso (f.residueFieldMap x)
  /-- The source cotangent space has dimension one over its canonical residue field. -/
  sourceFinrank :
    Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (Scheme.Hom.sourceStalkCotangent x) = 1
  /-- A vector detected by the first-coefficient calculation. -/
  detectedVector : Scheme.Hom.targetStalkCotangent f x
  /-- The detected vector has nonzero image. -/
  detected :
    Scheme.Hom.cotangentMapAtResidue f x detectedVector ≠ 0

namespace DegreeOneCotangentCertificate

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}

/-- Detection of one cotangent vector makes the canonical semilinear map nonzero. -/
lemma cotangentMapAtResidue_ne_zero (C : DegreeOneCotangentCertificate f x) :
    Scheme.Hom.cotangentMapAtResidue f x ≠ 0 := by
  intro hzero
  apply C.detected
  rw [hzero]
  exact LinearMap.zero_apply _

/-- The modular degree-one certificate proves surjectivity of the canonical cotangent map. -/
theorem isCotangentSurjectiveAt (C : DegreeOneCotangentCertificate f x) :
    Scheme.Hom.IsCotangentSurjectiveAt f x :=
  Scheme.Hom.isCotangentSurjectiveAt_of_degreeOne f x C.residueFieldMap_isIso
    C.sourceFinrank C.cotangentMapAtResidue_ne_zero

/-- The certificate proves the residue-field and cotangent-surjectivity conditions together. -/
theorem isCotangentCriterionAt (C : DegreeOneCotangentCertificate f x) :
    Scheme.Hom.IsCotangentCriterionAt f x :=
  Scheme.Hom.isCotangentCriterionAt_of_degreeOne f x C.residueFieldMap_isIso
    C.sourceFinrank C.cotangentMapAtResidue_ne_zero

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve
