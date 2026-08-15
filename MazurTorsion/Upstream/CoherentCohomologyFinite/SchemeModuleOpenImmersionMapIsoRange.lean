/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenImmersionOverIso

/-!
# Detecting module isomorphisms on the range of an open immersion

Pullback along an open immersion differs from restriction to its open
range only by pullback along the canonical range isomorphism.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
  [IsOpenImmersion f]

/--
If a module morphism becomes an isomorphism after pullback along an
open immersion, it is already an isomorphism after restriction to the
open range.
-/
theorem isIso_pullback_opensRange_of_isIso_pullback
    {M N : Y.Modules} (α : M ⟶ N)
    [IsIso ((pullback f).map α)] :
    IsIso ((pullback f.opensRange.ι).map α) := by
  let e :
      pullback f ≅
        pullback f.opensRange.ι ⋙
          pullback f.isoOpensRange.hom :=
    pullbackCongr f.isoOpensRange_hom_ι.symm ≪≫
      (pullbackComp
        f.isoOpensRange.hom
        f.opensRange.ι).symm
  haveI hcomp :
      IsIso
        ((pullback f.opensRange.ι ⋙
          pullback f.isoOpensRange.hom).map α) :=
    (NatIso.isIso_map_iff e α).mp inferInstance
  let F := pullback f.isoOpensRange.hom
  letI :
      (restrictFunctor
        f.isoOpensRange.hom).IsEquivalence :=
    inferInstance
  letI : F.IsEquivalence := by
    exact
      Functor.isEquivalence_of_iso
        (restrictFunctorIsoPullback
          f.isoOpensRange.hom)
  change
    IsIso
      (F.map ((pullback f.opensRange.ι).map α))
    at hcomp
  exact
    isIso_of_reflects_iso
      ((pullback f.opensRange.ι).map α) F

end AlgebraicGeometry.Scheme.Modules
