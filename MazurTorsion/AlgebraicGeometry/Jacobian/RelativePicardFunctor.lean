/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.Picard.RelativePic

/-!
# The unpointed relative Picard functor

For `p : X ⟶ S` and `t : T ⟶ S`, this file defines

`Pic(X ×[S] T) / pullback(Pic(T))`

and its contravariant functoriality in `T`.  Unlike the kernel model in the
upstream AINTLIB port, this construction does not require a section of `p`.
That distinction is necessary for a Jacobian of a curve without a rational
point.

This is only the presheaf-level quotient.  No sheafification or
representability claim is made here.  The named downstream consumer is
`RelativePicardDescent`.
-/

noncomputable section

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme

namespace MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard

universe u

open _root_.AlgebraicGeometry.Scheme.Modules

variable {S X T T' T'' : Scheme.{u}}

/-- Picard classes on the base pulled back to the base-changed family. -/
noncomputable def baseClasses (p : X ⟶ S) (t : T ⟶ S) :
    Subgroup (Pic (pullback p t)) :=
  (Pic.map (pullback.snd p t)).range

/-- The unpointed relative Picard group over `t : T ⟶ S`. -/
noncomputable abbrev group (p : X ⟶ S) (t : T ⟶ S) :=
  Pic (pullback p t) ⧸ baseClasses p t

/-- Base change carries a class pulled back from `T` to a class pulled back
from `T'`. -/
theorem map_baseClasses
    (p : X ⟶ S) {t : T ⟶ S} {t' : T' ⟶ S}
    (g : T' ⟶ T) (hg : g ≫ t = t') :
    baseClasses p t ≤
      (baseClasses p t').comap (Pic.map (baseChangeMap p g hg)) := by
  rintro L ⟨M, rfl⟩
  refine ⟨Pic.map g M, ?_⟩
  symm
  calc
    Pic.map (baseChangeMap p g hg)
        (Pic.map (pullback.snd p t) M) =
        Pic.map (baseChangeMap p g hg ≫ pullback.snd p t) M := by
          rw [Pic.map_comp]
          rfl
    _ = Pic.map (pullback.snd p t' ≫ g) M := by
          rw [baseChangeMap_snd]
    _ = Pic.map (pullback.snd p t') (Pic.map g M) := by
          rw [Pic.map_comp]
          rfl

/-- Pullback on unpointed relative Picard groups. -/
noncomputable def map
    (p : X ⟶ S) {t : T ⟶ S} {t' : T' ⟶ S}
    (g : T' ⟶ T) (hg : g ≫ t = t') :
    group p t →* group p t' :=
  QuotientGroup.map (baseClasses p t) (baseClasses p t')
    (Pic.map (baseChangeMap p g hg)) (map_baseClasses p g hg)

/-- Pullback on the relative Picard quotient is represented by pullback of
absolute Picard classes. -/
theorem map_mk
    (p : X ⟶ S) {t : T ⟶ S} {t' : T' ⟶ S}
    (g : T' ⟶ T) (hg : g ≫ t = t')
    (L : Pic (pullback p t)) :
    map p g hg (QuotientGroup.mk' (baseClasses p t) L) =
      QuotientGroup.mk' (baseClasses p t')
        (Pic.map (baseChangeMap p g hg) L) := by
  rfl

/-- The unpointed relative Picard presheaf as a contravariant functor to
commutative groups. -/
noncomputable def functor (p : X ⟶ S) :
    (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (group p T.unop.hom)
  map {T T'} g := CommGrpCat.ofHom (map p g.unop.left (Over.w g.unop))
  map_id := by
    intro T
    apply ConcreteCategory.hom_ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro L
    change map p (𝟙 T).unop.left (Over.w (𝟙 T).unop)
        (QuotientGroup.mk' (baseClasses p T.unop.hom) L) =
      QuotientGroup.mk' (baseClasses p T.unop.hom) L
    rw [map_mk, show baseChangeMap p (𝟙 T).unop.left (Over.w (𝟙 T).unop) =
        𝟙 (pullback p T.unop.hom) from baseChangeMap_id p T.unop.hom,
      Pic.map_id]
    rfl
  map_comp := by
    intro T T' T'' g g'
    apply ConcreteCategory.hom_ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro L
    change map p (g ≫ g').unop.left (Over.w (g ≫ g').unop)
        (QuotientGroup.mk' (baseClasses p T.unop.hom) L) =
      map p g'.unop.left (Over.w g'.unop)
        (map p g.unop.left (Over.w g.unop)
          (QuotientGroup.mk' (baseClasses p T.unop.hom) L))
    rw [map_mk, map_mk, map_mk,
      show baseChangeMap p (g ≫ g').unop.left (Over.w (g ≫ g').unop) =
          baseChangeMap p g'.unop.left (Over.w g'.unop) ≫
            baseChangeMap p g.unop.left (Over.w g.unop) from
        baseChangeMap_comp p g.unop.left (Over.w g.unop)
          g'.unop.left (Over.w g'.unop),
      Pic.map_comp]
    rfl

end MazurTorsion.AlgebraicGeometry.Jacobian.RelativePicard
