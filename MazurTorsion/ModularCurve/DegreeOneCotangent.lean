/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionNakayama
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth

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
completed local rings.  For a non-generic point of a smooth integral relative curve over a
field, Tau Ceti's checked DVR theorem now supplies the one-dimensional source cotangent space,
and smoothness supplies local Noetherianity.  Thus the remaining modular input is the actual
cusp, residue-field identification, and nonzero first `q`-coefficient.
Functoriality of the underlying canonical map for the composite modular morphism is already
checked in the imported core.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor

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

/-- If a `K`-point of the source and its image are rational in the literal residue-field sense,
then the induced residue-field map is an isomorphism.  This packages the functoriality identity
for residue fields into the exact hypothesis used by the degree-one cusp consumer. -/
theorem residueFieldMap_isIso_at_rationalPoint
    (K : Type u) [Field K] (g : Spec (.of K) ⟶ X)
    [hX : IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [hY : IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))] :
    IsIso (f.residueFieldMap (g (IsLocalRing.closedPoint K))) := by
  let a := f.residueFieldMap (g (IsLocalRing.closedPoint K))
  let b := X.descResidueField (Scheme.stalkClosedPointTo g)
  haveI : IsIso (a ≫ b) := by
    rw [← Scheme.descResidueField_stalkClosedPointTo_comp f g]
    exact hY
  exact IsIso.of_isIso_comp_right a b

/-- The cotangent space at a non-generic point of a smooth integral relative curve over a field
has dimension one over its residue field.  This discharges the geometric dimension field of the
degree-one certificate at an integral modular cusp. -/
theorem sourceFinrank_eq_one_of_smoothRelativeCurve
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (x : X) (hx : x ≠ genericPoint X) :
    Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (Scheme.Hom.sourceStalkCotangent x) = 1 := by
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_of_ne_genericPoint_of_smoothRelativeDimension_one
      K X π x hx
  exact IsLocalRing.finrank_CotangentSpace_eq_one (X.presheaf.stalk x)

/-- Build the degree-one certificate at a non-generic point of a smooth integral relative
curve.  The caller supplies only the residue-field comparison and the vector detected by the
first `q`-coefficient; the curve geometry supplies cotangent dimension one. -/
noncomputable def of_smoothRelativeCurve
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) (f : X ⟶ Y) (x : X) (hx : x ≠ genericPoint X)
    (hresidue : IsIso (f.residueFieldMap x))
    (detectedVector : Scheme.Hom.targetStalkCotangent f x)
    (detected : Scheme.Hom.cotangentMapAtResidue f x detectedVector ≠ 0) :
    DegreeOneCotangentCertificate f x where
  residueFieldMap_isIso := hresidue
  sourceFinrank := sourceFinrank_eq_one_of_smoothRelativeCurve K X π x hx
  detectedVector := detectedVector
  detected := detected

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
theorem isFormalImmersionAt_of_finiteMaximalIdeals
    (C : DegreeOneCotangentCertificate f x)
    [Module.Finite (Y.presheaf.stalk (f x))
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))]
    [Module.Finite (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))] :
    AlgebraicGeometry.IsFormalImmersionAt f x :=
  Scheme.Hom.isFormalImmersionAt_of_isCotangentCriterionAt
    f x C.isCotangentCriterionAt

/-- On locally Noetherian source and target schemes, the degree-one certificate proves the
actual formal-immersion predicate on completed local rings. This is the geometric consumer used
at the integral modular cusp. -/
theorem isFormalImmersionAt (C : DegreeOneCotangentCertificate f x)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] :
    AlgebraicGeometry.IsFormalImmersionAt f x :=
  Scheme.Hom.isFormalImmersionAt_of_isCotangentCriterionAt_of_isLocallyNoetherian
    f x C.isCotangentCriterionAt

/-- The direct degree-one formal-immersion consumer at a smooth integral curve point.  Smoothness
over the field supplies source local Noetherianity, while the target is required to be locally
Noetherian.  This is the exact endpoint filled by the modular cusp and first-coefficient
calculation. -/
theorem isFormalImmersionAt_of_smoothRelativeCurve
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X) (hx : x ≠ genericPoint X)
    (hresidue : IsIso (f.residueFieldMap x))
    (detectedVector : Scheme.Hom.targetStalkCotangent f x)
    (detected : Scheme.Hom.cotangentMapAtResidue f x detectedVector ≠ 0) :
    AlgebraicGeometry.IsFormalImmersionAt f x := by
  letI : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  let C := of_smoothRelativeCurve K X π Y f x hx hresidue detectedVector detected
  exact C.isFormalImmersionAt

/-- The rational-cusp specialization of the smooth-curve degree-one consumer.  Literal
rationality of the cusp in the source and target now supplies the residue-field comparison, so
the remaining arithmetic datum is exactly a target cotangent vector whose first coefficient is
detected nontrivially. -/
theorem isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    (detectedVector : Scheme.Hom.targetStalkCotangent f (g (IsLocalRing.closedPoint K)))
    (detected : Scheme.Hom.cotangentMapAtResidue f (g (IsLocalRing.closedPoint K))
      detectedVector ≠ 0) :
    AlgebraicGeometry.IsFormalImmersionAt f (g (IsLocalRing.closedPoint K)) := by
  exact isFormalImmersionAt_of_smoothRelativeCurve K X π Y f
    (g (IsLocalRing.closedPoint K)) hx
    (residueFieldMap_isIso_at_rationalPoint K g) detectedVector detected

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve
