/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersion

/-!
# Identity consumers for formal completion and the stalk-cotangent interface

The identity morphism is the first concrete consumer of both the completed-local-ring map and
`Scheme.Hom.IsCotangentSurjectiveAt`.  It checks the normalization of the completion
construction as well as the chosen maximal-ideal comparison.  The final theorem also checks
the residue-field half of `Scheme.Hom.IsCotangentCriterionAt`.
-/

namespace AlgebraicGeometry

universe u

open CategoryTheory

namespace Scheme.Hom

/-- The identity morphism is a formal immersion at every point. -/
theorem isFormalImmersionAt_id (X : Scheme.{u}) (x : X) :
    IsFormalImmersionAt (𝟙 X) x := by
  rw [AlgebraicGeometry.IsFormalImmersionAt]
  change Function.Surjective
    (LocalCompletion.map (((𝟙 X : X ⟶ X).stalkMap x).hom))
  have hstalk : ((𝟙 X : X ⟶ X).stalkMap x).hom =
      RingHom.id (X.presheaf.stalk x) :=
    CommRingCat.hom_ext_iff.mp (Scheme.Hom.stalkMap_id X x)
  have hmap : LocalCompletion.map (((𝟙 X : X ⟶ X).stalkMap x).hom) =
      LocalCompletion.map (RingHom.id (X.presheaf.stalk x)) := by
    congr
  rw [hmap, LocalCompletion.map_id]
  exact Function.surjective_id

/-- The identity morphism satisfies the cotangent criterion at every point. -/
theorem isCotangentSurjectiveAt_id (X : Scheme.{u}) (x : X) :
    IsCotangentSurjectiveAt (𝟙 X) x := by
  apply isCotangentSurjectiveAt_of_surjective_stalkMap
  rw [Scheme.Hom.stalkMap_id]
  exact Function.surjective_id

/-- The canonical residue-field-semilinear cotangent map of the identity is surjective. -/
theorem cotangentMapAtResidue_id_surjective (X : Scheme.{u}) (x : X) :
    Function.Surjective (cotangentMapAtResidue (𝟙 X) x) := by
  change IsCotangentSurjectiveAt (𝟙 X) x
  exact isCotangentSurjectiveAt_id X x

/-- The identity morphism satisfies both halves of the cotangent criterion. -/
theorem isCotangentCriterionAt_id (X : Scheme.{u}) (x : X) :
    IsCotangentCriterionAt (𝟙 X) x := by
  refine ⟨?_, isCotangentSurjectiveAt_id X x⟩
  rw [Scheme.residueFieldMap_id]
  exact IsIso.id _

end Scheme.Hom

end AlgebraicGeometry
