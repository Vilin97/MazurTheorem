/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoSections

/-!
# Transporting module twists to projective space

The standard affine cover reconstructs projective space as the glued scheme
of its cover glue datum.  Since the canonical map from that glued scheme is
an isomorphism, it induces an equivalence of module-sheaf categories.

This file packages conjugation by that equivalence.  In particular, any
autoequivalence constructed on the glued scheme (such as scalar twisting by
the integer Serre cocycle) canonically yields an autoequivalence on
projective space.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

/-- The equivalence from module sheaves on projective space to module sheaves
on the scheme reconstructed from its standard affine cover. -/
noncomputable def projectiveToGluedModules :
    (scheme k d).Modules ≌ (glueData k d).glued.Modules :=
  pushforwardEquivalenceOfIso (cover k d).fromGlued

/-- The forward functor of `projectiveToGluedModules` is pullback along the
canonical map from the glued standard cover to projective space. -/
noncomputable def projectiveToGluedModulesFunctorIso :
    (projectiveToGluedModules k d).functor ≅
      Scheme.Modules.pullback (cover k d).fromGlued :=
  (pullbackIsoPushforwardInverse (cover k d).fromGlued).symm

/-- The inverse functor is pullback along the inverse of the canonical map
from the glued standard cover. -/
noncomputable def gluedToProjectiveModulesFunctorIso :
    (projectiveToGluedModules k d).inverse ≅
      Scheme.Modules.pullback (inv (cover k d).fromGlued) :=
  ((pullbackIsoPushforwardInverse
      (inv (cover k d).fromGlued)).trans
    (Scheme.Modules.pushforwardCongr
      (IsIso.inv_inv (f := (cover k d).fromGlued)))).symm

/-- Conjugate an autoequivalence of modules on the glued standard cover into
an autoequivalence of modules on projective space. -/
noncomputable def transportGluedModuleAutEquivalence
    (E : (glueData k d).glued.Modules ≌
      (glueData k d).glued.Modules) :
    (scheme k d).Modules ≌ (scheme k d).Modules :=
  (projectiveToGluedModules k d).trans
    (E.trans (projectiveToGluedModules k d).symm)

/-- The integer Serre cocycle defines an autoequivalence of module sheaves
on projective space. -/
noncomputable def projectiveIntegerScalarTwistEquivalence (m : ℤ) :
    (scheme k d).Modules ≌ (scheme k d).Modules :=
  transportGluedModuleAutEquivalence k d
    (gluedIntegerScalarTwistEquivalence k d m)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
