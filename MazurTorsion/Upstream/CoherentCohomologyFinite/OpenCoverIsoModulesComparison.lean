/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoScalarTwistGlued
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistEquivalence

/-!
# Module-category coordinates for isomorphic open covers

Passing from the ambient scheme to the glued scheme is natural when the
chosen open cover is replaced by an isomorphic one.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- The two module-category coordinates associated to isomorphic open
covers differ by pullback along the glued-scheme comparison. -/
noncomputable def modulesToGluedCoverIsoNatIso
    (e : 𝒰 ≅ 𝒱) :
    (modulesToGluedEquivalence 𝒰).functor ≅
      (modulesToGluedEquivalence 𝒱).functor ⋙
        pullback (coverIsoGluedIso e).hom :=
  modulesToGluedEquivalenceFunctorIso 𝒰 ≪≫
    pullbackCongr
      (coverIsoGluedIso_hom_fromGlued e).symm ≪≫
    (pullbackComp
      (coverIsoGluedIso e).hom
      𝒱.fromGlued).symm ≪≫
    Functor.isoWhiskerRight
      (modulesToGluedEquivalenceFunctorIso 𝒱).symm
      (pullback (coverIsoGluedIso e).hom)

end AlgebraicGeometry.Scheme.Modules
