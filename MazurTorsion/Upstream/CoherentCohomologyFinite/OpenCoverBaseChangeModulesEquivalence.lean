/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeGluedMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistEquivalence

/-!
# Glued-cover module equivalences under base change

The equivalence between modules on a scheme and modules on the scheme
glued from an open cover is natural under base change.  This file records
the two coordinate-change isomorphisms needed to transport functorial
constructions through those equivalences.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- Passing from the glued original cover back to `S` and then pulling
back to `T` agrees with pulling back between the glued covers and then
passing back to `T`. -/
noncomputable def gluedToModulesBaseChangeNatIso :
    (modulesToGluedEquivalence 𝒰).inverse ⋙
        pullback f ≅
      pullback (baseChangeGluedMap 𝒰 f) ⋙
        (modulesToGluedEquivalence
          (𝒰.pullback₁ f)).inverse :=
  Functor.isoWhiskerRight
      (gluedToModulesEquivalenceFunctorIso 𝒰)
      (pullback f) ≪≫
    pullbackComp f (inv 𝒰.fromGlued) ≪≫
    pullbackCongr
      (inv_fromGlued_baseChangeGluedMap
        𝒰 f).symm ≪≫
    (pullbackComp
      (inv (fromGlued (𝒰.pullback₁ f)))
      (baseChangeGluedMap 𝒰 f)).symm ≪≫
    Functor.isoWhiskerLeft
      (pullback (baseChangeGluedMap 𝒰 f))
      (gluedToModulesEquivalenceFunctorIso
        (𝒰.pullback₁ f)).symm

/-- Pulling back to `T` and then passing to its glued pulled-back cover
agrees with first passing to the glued original cover and then pulling
back along the glued base-change map. -/
noncomputable def modulesToGluedBaseChangeNatIso :
    pullback f ⋙
        (modulesToGluedEquivalence
          (𝒰.pullback₁ f)).functor ≅
      (modulesToGluedEquivalence 𝒰).functor ⋙
        pullback (baseChangeGluedMap 𝒰 f) :=
  Functor.isoWhiskerLeft
      (pullback f)
      (modulesToGluedEquivalenceFunctorIso
        (𝒰.pullback₁ f)) ≪≫
    pullbackComp
      (fromGlued (𝒰.pullback₁ f)) f ≪≫
    pullbackCongr
      (baseChangeGluedMap_fromGlued 𝒰 f).symm ≪≫
    (pullbackComp
      (baseChangeGluedMap 𝒰 f)
      𝒰.fromGlued).symm ≪≫
    Functor.isoWhiskerRight
      (modulesToGluedEquivalenceFunctorIso
        𝒰).symm
      (pullback (baseChangeGluedMap 𝒰 f))

end AlgebraicGeometry.Scheme.Modules
