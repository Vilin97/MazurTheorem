/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersion

/-!
# Identity consumer for the stalk-cotangent interface

The identity morphism is the first concrete consumer of
`Scheme.Hom.IsCotangentSurjectiveAt`.  It checks that the chosen maximal-ideal comparison is
surjective when the canonical stalk map is the identity.  The second theorem also checks the
residue-field half of `Scheme.Hom.IsCotangentCriterionAt`.
-/

namespace AlgebraicGeometry

universe u

open CategoryTheory

namespace Scheme.Hom

/-- The identity morphism satisfies the cotangent criterion at every point. -/
theorem isCotangentSurjectiveAt_id (X : Scheme.{u}) (x : X) :
    IsCotangentSurjectiveAt (𝟙 X) x := by
  apply isCotangentSurjectiveAt_of_surjective_stalkMap
  rw [Scheme.Hom.stalkMap_id]
  exact Function.surjective_id

/-- The identity morphism satisfies both halves of the cotangent criterion. -/
theorem isCotangentCriterionAt_id (X : Scheme.{u}) (x : X) :
    IsCotangentCriterionAt (𝟙 X) x := by
  refine ⟨?_, isCotangentSurjectiveAt_id X x⟩
  rw [Scheme.residueFieldMap_id]
  exact IsIso.id _

end Scheme.Hom

end AlgebraicGeometry
