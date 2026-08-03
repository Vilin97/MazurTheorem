/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionNakayama

/-!
# The degree-one cotangent consumer

This module records the residue-field-honest checked handoff expected from the modular `q`-expansion
calculation.  For a cusp-normalized morphism from a modular curve to a quotient of its Jacobian,
the remaining Hecke calculation must:

* prove that the induced residue-field map is an isomorphism;
* prove that the curve cotangent space has dimension one over its actual residue field; and
* exhibit a cotangent vector whose image is nonzero (the first-coefficient calculation).

`DegreeOneCotangentCertificate.isCotangentCriterionAt` then supplies both checked first-order
conditions.  Its Nakayama consumers generate the source maximal ideal and prove surjectivity on
the quotient by the square of the maximal ideal.  When the two stalk maximal ideals are finite,
`DegreeOneCotangentCertificate.isFormalImmersionAt` upgrades the certificate to surjectivity on
completed local rings.  The remaining `MT-X0-INTEGRAL` work is therefore geometric: construct the
stalk finiteness instances and the modular certificate at the chosen cusp.
Functoriality of the underlying canonical map for the composite modular morphism is already
checked in the imported core.
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

/-- The degree-one modular certificate generates the source-stalk maximal ideal from the
target-stalk maximal ideal.  This is the checked Nakayama consequence used before passing to
adic completions. -/
theorem map_maximalIdeal_stalkMap_eq (C : DegreeOneCotangentCertificate f x)
    [Module.Finite (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))] :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  Scheme.Hom.map_maximalIdeal_stalkMap_eq_of_isCotangentSurjectiveAt
    f x C.isCotangentSurjectiveAt

/-- The degree-one modular certificate is already surjective on second infinitesimal
neighbourhoods. -/
theorem maximalIdealSquareQuotientMap_stalkMap_surjective
    (C : DegreeOneCotangentCertificate f x) :
    Function.Surjective
      (IsLocalRing.maximalIdealSquareQuotientMap (f.stalkMap x).hom) :=
  Scheme.Hom.maximalIdealSquareQuotientMap_stalkMap_surjective_of_isCotangentCriterionAt
    f x C.isCotangentCriterionAt

/-- With finite stalk maximal ideals, the degree-one modular certificate proves the actual
formal-immersion predicate on completed local rings. -/
theorem isFormalImmersionAt (C : DegreeOneCotangentCertificate f x)
    [Module.Finite (Y.presheaf.stalk (f x))
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))]
    [Module.Finite (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))] :
    AlgebraicGeometry.IsFormalImmersionAt f x :=
  Scheme.Hom.isFormalImmersionAt_of_isCotangentCriterionAt
    f x C.isCotangentCriterionAt

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve
