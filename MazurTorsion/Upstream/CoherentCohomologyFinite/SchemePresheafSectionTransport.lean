/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartTripleOverlap

/-!
# Transporting scheme sections across equal opens

This small functoriality lemma is the structure-sheaf counterpart of
`module_presheaf_map_eqToIso_apply`.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/--
Restriction of structure-sheaf sections commutes with transport across
equal source and target opens.
-/
theorem schemePresheaf_map_eqToIso_apply
    {X : Scheme.{0}}
    {A B A' B' : X.Opens}
    (eA : A = A') (eB : B = B')
    (h : A ≤ B) (h' : A' ≤ B')
    (x : Γ(X, B)) :
    (eqToIso (congrArg (fun U => Γ(X, U)) eA)).hom
        (X.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE h').op
        ((eqToIso
          (congrArg (fun U => Γ(X, U)) eB)).hom x) := by
  subst A'
  subst B'
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
