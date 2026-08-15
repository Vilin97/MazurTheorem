/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.LeftExact
import MazurTorsion.AlgebraicGeometry.PicardDegreeZero
import MazurTorsion.Upstream.AINTLIB.Picard.RelativePic

/-!
# The fppf sheafification of the zero-section-normalized Picard functor

The AINTLIB-derived `Scheme.Modules.picRelFunctor` is the all-degree Picard
presheaf in its zero-section-normalized kernel model.  This file passes its
additive form through Mathlib's sheafification functor on the relative fppf
site.  The result is the associated sheafification and makes no representability
or universal-line-bundle claim.

The degree-zero subfunctor is deliberately not defined here.  Its construction
requires a pullback-compatible relative degree map on arbitrary test schemes;
the available divisor degree is currently only an absolute construction for
curves over fields.  We do expose the canonical map from the kernel of that
honest absolute degree into the all-degree sheafification at the base object.
This is a checked boundary map, not a substitute relative `Pic⁰` functor.
-/

noncomputable section

universe u

open CategoryTheory Limits
open MazurTorsion.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {S E T T' : Scheme.{u}}
variable (p : E ⟶ S) (z : S ⟶ E) (hz : z ≫ p = 𝟙 S)

/-- The additive form of the zero-section-normalized relative Picard
presheaf. -/
noncomputable abbrev picRelAddPresheaf :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  picRelFunctor p z hz ⋙ CommGrpCat.toAddCommGrp

/-- The associated fppf sheafification of the all-degree normalized Picard presheaf.
It does not assert descent for the presheaf and is not a representing scheme. -/
noncomputable abbrev picRelFppfSheaf :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S)
    AddCommGrpCat.{u + 1}).obj (picRelAddPresheaf p z hz)

/-- The canonical map from normalized relative Picard classes to their fppf
sheafification. -/
noncomputable abbrev picRelToFppfSheaf :
    picRelAddPresheaf p z hz ⟶
      (sheafToPresheaf (Scheme.fppfTopology.over S)
        AddCommGrpCat.{u + 1}).obj (picRelFppfSheaf p z hz) :=
  (sheafificationAdjunction (Scheme.fppfTopology.over S)
    AddCommGrpCat.{u + 1}).unit.app _

/-- Normalize an absolute Picard class on a base change and map it into the
associated fppf sheafification. -/
noncomputable def picRelFppfClassHom (t : T ⟶ S) :
    Additive (Pic (Limits.pullback p t)) →+
      (picRelFppfSheaf p z hz).obj.obj (Opposite.op (Over.mk t)) :=
  ((picRelToFppfSheaf p z hz).app (Opposite.op (Over.mk t))).hom.comp
    (picRelProj p z hz t).toAdditive

/-- The image of a normalized Picard element in the associated fppf
sheafification commutes with arbitrary base change. -/
theorem picRelFppfClassHom_baseChange {t : T ⟶ S} {t' : T' ⟶ S}
    (g : T' ⟶ T) (hg : g ≫ t = t')
    (L : Pic (Limits.pullback p t)) :
    (picRelFppfSheaf p z hz).obj.map
        (Over.homMk g hg : Over.mk t' ⟶ Over.mk t).op
        (picRelFppfClassHom p z hz t (Additive.ofMul L)) =
      picRelFppfClassHom p z hz t'
        (Additive.ofMul (Pic.map (baseChangeMap p g hg) L)) := by
  let f := (Over.homMk g hg : Over.mk t' ⟶ Over.mk t).op
  let x : (picRelAddPresheaf p z hz).obj (Opposite.op (Over.mk t)) :=
    Additive.ofMul (picRelProj p z hz t L)
  calc
    _ = (picRelToFppfSheaf p z hz).app (Opposite.op (Over.mk t'))
          ((picRelAddPresheaf p z hz).map f x) := by
      exact ((picRelToFppfSheaf p z hz).naturality_apply f x).symm
    _ = _ := by
      apply congrArg
        ((picRelToFppfSheaf p z hz).app (Opposite.op (Over.mk t')))
      change Additive.ofMul ((picRelFunctor p z hz).map f
        (picRelProj p z hz t L)) = _
      rw [picRelFunctor_map_picRelProj]
      rfl

/-- At the identity test object, pull an absolute Picard class to the trivial
base change, normalize it, and map it into the associated fppf sheafification. -/
noncomputable def picRelFppfClassAtBaseHom :
    Additive (Pic E) →+
      (picRelFppfSheaf p z hz).obj.obj
        (Opposite.op (Over.mk (𝟙 S))) :=
  (picRelFppfClassHom p z hz (𝟙 S)).comp
    (Pic.map (Limits.pullback.fst p (𝟙 S))).toAdditive

/-- Map the kernel of the checked absolute degree of a smooth proper curve into the associated
fppf sheafification of the all-degree normalized Picard presheaf at the base object.

This is the strongest degree-zero boundary supported by the pinned APIs: its source is the
actual kernel of an absolute degree homomorphism, while its target is evaluated only at
`Spec K ⟶ Spec K`.  It does not claim that these kernels form a pullback-compatible
subpresheaf on arbitrary test schemes. -/
noncomputable def properCurveDegreeKernelToPicRelFppfAtBase
    (K : Type u) [Field K]
    (E : Scheme.{u}) [IsIntegral E] [IsNoetherian E]
    (p : E ⟶ Spec (.of K)) [IsProper p] [SmoothOfRelativeDimension 1 p]
    (z : Spec (.of K) ⟶ E) (hz : z ≫ p = 𝟙 (Spec (.of K)))
    (e : DivisorPicard.ClassEquivalence
      (TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem E) E) :
    (PicardGroup.properCurveDegreeHom K E p e).ker →+
      (picRelFppfSheaf p z hz).obj.obj
        (Opposite.op (Over.mk (𝟙 (Spec (.of K))))) :=
  (picRelFppfClassAtBaseHom p z hz).comp
    (PicardGroup.properCurveDegreeHom K E p e).ker.subtype

end AlgebraicGeometry.Scheme.Modules
