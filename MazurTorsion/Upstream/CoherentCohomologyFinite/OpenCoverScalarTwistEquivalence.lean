/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedEquivalence

/-!
# Scalar-twist equivalences from an open cover

An open cover reconstructs its ambient scheme from the associated glue
datum.  Transporting the glued scalar-twist equivalence through this
canonical scheme isomorphism gives an autoequivalence of module sheaves
on the original scheme.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections
open CoverDescentData

variable {X : Scheme.{0}} (𝒰 : X.OpenCover)

/--
The equivalence from modules on a scheme to modules on the scheme glued
from an open cover.
-/
noncomputable def modulesToGluedEquivalence :
    X.Modules ≌ 𝒰.gluedCover.glued.Modules :=
  pushforwardEquivalenceOfIso 𝒰.fromGlued

/--
The forward functor of `modulesToGluedEquivalence` is naturally
isomorphic to pullback along the canonical map from the glued cover.
-/
noncomputable def modulesToGluedEquivalenceFunctorIso :
    (modulesToGluedEquivalence 𝒰).functor ≅
      pullback 𝒰.fromGlued :=
  (pullbackIsoPushforwardInverse 𝒰.fromGlued).symm

/--
The inverse equivalence is naturally isomorphic to pullback along the
inverse canonical map.
-/
noncomputable def gluedToModulesEquivalenceFunctorIso :
    (modulesToGluedEquivalence 𝒰).inverse ≅
      pullback (inv 𝒰.fromGlued) :=
  ((pullbackIsoPushforwardInverse
      (inv 𝒰.fromGlued)).trans
    (pushforwardCongr
      (IsIso.inv_inv (f := 𝒰.fromGlued)))).symm

/-- Transport an autoequivalence of modules on the glued cover to the
original scheme. -/
noncomputable def transportGluedAutEquivalence
    (E : 𝒰.gluedCover.glued.Modules ≌
      𝒰.gluedCover.glued.Modules) :
    X.Modules ≌ X.Modules :=
  (modulesToGluedEquivalence 𝒰).trans
    (E.trans (modulesToGluedEquivalence 𝒰).symm)

section

variable
    (a : ∀ i j,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition 𝒰.gluedCover a)

/--
Scalar twisting by a cover-unit cocycle, transported to module sheaves
on the scheme covered by `𝒰`.
-/
noncomputable def openCoverScalarTwistEquivalence :
    X.Modules ≌ X.Modules :=
  transportGluedAutEquivalence 𝒰
    (scalarTwistGluedEquivalence
      a hself hcocycle)

/-- Forward-functor expansion through the glued cover. -/
@[simp]
theorem openCoverScalarTwistEquivalence_functor :
    (openCoverScalarTwistEquivalence
      𝒰 a hself hcocycle).functor =
      (modulesToGluedEquivalence 𝒰).functor ⋙
        (scalarTwistGluedEquivalence
          a hself hcocycle).functor ⋙
        (modulesToGluedEquivalence 𝒰).inverse :=
  rfl

/-- Object-level expansion into restriction, scalar twisting, and
gluing on the glued cover. -/
@[simp]
theorem openCoverScalarTwistEquivalence_functor_obj
    (M : X.Modules) :
    (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).functor.obj M =
      (modulesToGluedEquivalence 𝒰).inverse.obj
        ((glueFunctor (D := 𝒰.gluedCover)).obj
          ((scalarTwistFunctor
            a hself hcocycle).obj
              ((restrictionFunctor
                (D := 𝒰.gluedCover)).obj
                  ((modulesToGluedEquivalence
                    𝒰).functor.obj M)))) :=
  rfl

/--
The forward transported scalar-twist functor is naturally isomorphic
to the same construction with its first step written as geometric
pullback along `𝒰.fromGlued`.
-/
noncomputable def openCoverScalarTwistFunctorIso :
    (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).functor ≅
      (pullback 𝒰.fromGlued ⋙
        (scalarTwistGluedEquivalence
          a hself hcocycle).functor) ⋙
        (modulesToGluedEquivalence 𝒰).inverse := by
  change
    ((modulesToGluedEquivalence 𝒰).functor ⋙
        (scalarTwistGluedEquivalence
          a hself hcocycle).functor) ⋙
        (modulesToGluedEquivalence 𝒰).inverse ≅ _
  exact
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (modulesToGluedEquivalenceFunctorIso 𝒰)
        (scalarTwistGluedEquivalence
          a hself hcocycle).functor)
      (modulesToGluedEquivalence 𝒰).inverse

/-- Objectwise form of `openCoverScalarTwistFunctorIso`. -/
noncomputable def openCoverScalarTwistObjectIso
    (M : X.Modules) :
    (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).functor.obj M ≅
      (modulesToGluedEquivalence 𝒰).inverse.obj
        ((scalarTwistGluedEquivalence
          a hself hcocycle).functor.obj
            ((pullback 𝒰.fromGlued).obj M)) :=
  (openCoverScalarTwistFunctorIso
    𝒰 a hself hcocycle).app M

end

end AlgebraicGeometry.Scheme.Modules
