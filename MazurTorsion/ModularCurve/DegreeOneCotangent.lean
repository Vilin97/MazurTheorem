/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersion

/-!
# The degree-one cotangent consumer

This module records a provisional checked handoff expected from the modular `q`-expansion
calculation.  For a cusp-normalized morphism from a modular curve to a quotient of its Jacobian,
the remaining Hecke calculation must:

* prove that the induced residue-field map is an isomorphism;
* realize the canonical stalk-cotangent map as a linear map over a chosen field `k`;
* prove that the supplied scalar realization of the curve cotangent space has dimension one; and
* exhibit a cotangent vector whose image is nonzero (the first-coefficient calculation).

`DegreeOneCotangentCertificate.isCotangentCriterionAt` then supplies both checked first-order
conditions.  This is not yet a formal-immersion theorem: compatibility of the chosen scalar
structure with the geometric residue fields and the completed-local-ring equivalence remain
`MT-X0-INTEGRAL`/`MT-X0-HECKE` obligations.  Functoriality of the underlying canonical map for
the composite modular morphism is already checked in the imported core.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory

universe u v

/-- Chosen-field linear data needed by Mazur's degree-one cotangent argument.

The `detected` field is deliberately an explicit vector rather than a bare nonzero-map
assumption.  It is the downstream slot filled by a checked nonzero first `q`-coefficient. -/
structure DegreeOneCotangentCertificate
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (k : Type v) [Field k]
    [Module k (Scheme.Hom.targetStalkCotangent f x)]
    [Module k (Scheme.Hom.sourceStalkCotangent x)] where
  /-- The morphism induces an isomorphism on residue fields at the selected points. -/
  residueFieldMap_isIso : IsIso (f.residueFieldMap x)
  /-- A chosen-field linearization of the canonical cotangent map. -/
  differential :
    Scheme.Hom.targetStalkCotangent f x →ₗ[k]
      Scheme.Hom.sourceStalkCotangent x
  /-- Forgetting the residue-field scalar structure recovers the canonical stalk map. -/
  realizesCanonical :
    ∀ z, differential z = Scheme.Hom.cotangentMapAtInt f x z
  /-- The supplied scalar realization of the source cotangent space has dimension one. -/
  sourceFinrank :
    Module.finrank k (Scheme.Hom.sourceStalkCotangent x) = 1
  /-- A vector detected by the first-coefficient calculation. -/
  detectedVector : Scheme.Hom.targetStalkCotangent f x
  /-- The detected vector has nonzero image. -/
  detected : differential detectedVector ≠ 0

namespace DegreeOneCotangentCertificate

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
  {k : Type v} [Field k]
  [Module k (Scheme.Hom.targetStalkCotangent f x)]
  [Module k (Scheme.Hom.sourceStalkCotangent x)]

/-- Detection of one cotangent vector makes the certificate's differential nonzero. -/
lemma differential_ne_zero (C : DegreeOneCotangentCertificate f x k) :
    C.differential ≠ 0 := by
  intro hzero
  apply C.detected
  rw [hzero]
  exact LinearMap.zero_apply _

/-- The modular degree-one certificate proves surjectivity of the canonical cotangent map. -/
theorem isCotangentSurjectiveAt (C : DegreeOneCotangentCertificate f x k) :
    Scheme.Hom.IsCotangentSurjectiveAt f x :=
  Scheme.Hom.isCotangentSurjectiveAt_of_degreeOne f x C.differential
    C.realizesCanonical C.sourceFinrank C.differential_ne_zero

/-- The certificate proves the residue-field and cotangent-surjectivity conditions together. -/
theorem isCotangentCriterionAt (C : DegreeOneCotangentCertificate f x k) :
    Scheme.Hom.IsCotangentCriterionAt f x :=
  ⟨C.residueFieldMap_isIso, C.isCotangentSurjectiveAt⟩

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve
