/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.Picard.RelativePic

/-!
# Base change of a section of a relative scheme

For a morphism `p : E ⟶ S`, a test scheme `t : T ⟶ S`, and a section of the
base change `E ×_S T ⟶ T`, this file constructs the section after a further
base change `T' ⟶ T`.  It proves both the section law and the comparison with the
canonical map `E ×_S T' ⟶ E ×_S T`.

This is the categorical part of the section-to-relative-Picard construction.  It
does not assert that pullback commutes with the ideal module of an arbitrary
closed subscheme: such a statement needs a flatness or Tor-independence
hypothesis.  For section divisors on a smooth relative curve, that later
comparison must use the relative effective Cartier divisor structure.

The declarations below are repository-local glue over the exact-pin
`RelativePic` API; they are not copied from AINTLIB.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {S E T T' : Scheme.{u}}

/-- Further base change of a section `P : T ⟶ E ×_S T` along a morphism
`g : T' ⟶ T` over `S`. -/
noncomputable def baseChangeSection (p : E ⟶ S)
    {t : T ⟶ S} (P : T ⟶ Limits.pullback p t)
    (hP : P ≫ Limits.pullback.snd p t = 𝟙 T)
    {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    T' ⟶ Limits.pullback p t' :=
  Limits.pullback.lift (g ≫ P ≫ Limits.pullback.fst p t) (𝟙 T') (by
    rw [Category.id_comp]
    calc
      (g ≫ P ≫ Limits.pullback.fst p t) ≫ p =
          g ≫ (P ≫ (Limits.pullback.fst p t ≫ p)) := by
            simp only [Category.assoc]
      _ = g ≫ (P ≫ (Limits.pullback.snd p t ≫ t)) := by
            rw [Limits.pullback.condition]
      _ = g ≫ ((P ≫ Limits.pullback.snd p t) ≫ t) := by
            rw [Category.assoc]
      _ = g ≫ t := by rw [hP, Category.id_comp]
      _ = t' := hg)

/-- A base-changed section remains a section of the second projection. -/
theorem baseChangeSection_snd (p : E ⟶ S)
    {t : T ⟶ S} (P : T ⟶ Limits.pullback p t)
    (hP : P ≫ Limits.pullback.snd p t = 𝟙 T)
    {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    baseChangeSection p P hP g hg ≫ Limits.pullback.snd p t' = 𝟙 T' :=
  Limits.pullback.lift_snd _ _ _

/-- The first projection of the canonical base-change map is unchanged. -/
theorem baseChangeMap_fst (p : E ⟶ S)
    {t : T ⟶ S} {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    baseChangeMap p g hg ≫ Limits.pullback.fst p t =
      Limits.pullback.fst p t' :=
  Limits.pullback.lift_fst _ _ _

/-- The base-changed section followed by the canonical base-change map is the
original section pulled back along `g`. -/
theorem baseChangeSection_baseChangeMap (p : E ⟶ S)
    {t : T ⟶ S} (P : T ⟶ Limits.pullback p t)
    (hP : P ≫ Limits.pullback.snd p t = 𝟙 T)
    {t' : T' ⟶ S} (g : T' ⟶ T) (hg : g ≫ t = t') :
    baseChangeSection p P hP g hg ≫ baseChangeMap p g hg = g ≫ P := by
  ext
  · rw [Category.assoc, baseChangeMap_fst]
    exact Limits.pullback.lift_fst _ _ _
  · rw [Category.assoc, baseChangeMap_snd]
    rw [← Category.assoc, baseChangeSection_snd, Category.id_comp]
    symm
    rw [Category.assoc, hP, Category.comp_id]

/-- Further base change of the distinguished zero section agrees with its direct
base change from `S`. -/
theorem baseChangeSection_baseChangeZero (p : E ⟶ S) (z : S ⟶ E)
    (hz : z ≫ p = 𝟙 S) {t : T ⟶ S} {t' : T' ⟶ S}
    (g : T' ⟶ T) (hg : g ≫ t = t') :
    baseChangeSection p (baseChangeZero p z hz t)
        (baseChangeZero_snd p z hz t) g hg =
      baseChangeZero p z hz t' := by
  ext
  · simp only [baseChangeSection, baseChangeZero, Limits.pullback.lift_fst]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ z) hg
  · exact (baseChangeSection_snd p (baseChangeZero p z hz t)
      (baseChangeZero_snd p z hz t) g hg).trans
        (baseChangeZero_snd p z hz t').symm

end AlgebraicGeometry.Scheme.Modules
