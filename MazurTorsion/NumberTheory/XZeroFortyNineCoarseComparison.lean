/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.XZeroFortyNineTransfer
import MazurTorsion.NumberTheory.XZeroFortyNineRationalCuspOpen

/-!
# Comparing the coarse `Gamma_0(49)` fibre with the explicit cubic

This module forms the actual rational fibre of a supplied global coarse
`Gamma_0(49)` space by pulling it back from `Spec Z` to `Spec Q`.  Every
rational point of the global coarse space lifts canonically to that fibre.

`RationalFiberOpenComparison` states the remaining comparison with the
explicit projective cubic at the correct geometric level: an open immersion
over `Spec Q` into the actual `D(X)` open.  Factoring through this open is
proved here to avoid both rational cusp morphisms, rather than recorded as an
extra field.  Combined with the represented two-cusp classification, such a
comparison makes both the rational fibre and the global coarse scheme empty
on `Q`-points.  The exact order-49 moduli class is a named consumer, yielding
the modular-route order-49 contradiction.

No `CoarseModuliSpace` or `RationalFiberOpenComparison` is constructed here.
In particular, the factorization through `D(X)` and open-immersion field are
honest remaining modular-geometry obligations; the already checked explicit
isogeny-tower proof of the order-49 theorem is not used to manufacture them.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
open MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

namespace MazurTorsion.XZeroFortyNine.CoarseComparison

/-- A universe-zero coarse space for the locally constant level-49 moduli
functor, suitable for comparison with the explicit rational cubic. -/
abbrev CoarseSpace :=
  ModularCurve.XZeroModuli.LocallyConstantGammaZeroFamily.CoarseModuliSpace.{0} 49

/-- The canonical morphism from the rational point to the integer base. -/
def rationalBaseMap : Spec (.of ℚ) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))

/-- The actual rational fibre of a supplied global coarse moduli scheme. -/
abbrev rationalFiber (M : CoarseSpace) : Scheme :=
  pullback (specZIsTerminal.from M.scheme) rationalBaseMap

/-- The rational fibre as a scheme over `Spec Q`. -/
noncomputable def rationalFiberOver (M : CoarseSpace) : Over (Spec (.of ℚ)) :=
  Over.mk (pullback.snd (specZIsTerminal.from M.scheme) rationalBaseMap)

/-- Lift a rational point of the global coarse scheme to its rational fibre.
Compatibility over `Spec Z` follows from terminality. -/
def rationalFiberPointMorphism (M : CoarseSpace)
    (p : Spec (.of ℚ) ⟶ M.scheme) :
    Over.mk (𝟙 (Spec (.of ℚ))) ⟶ rationalFiberOver M :=
  Over.homMk
    (pullback.lift p (𝟙 _) (by
      exact specZIsTerminal.hom_ext _ _))
    (by
      change pullback.lift p (𝟙 _) _ ≫
          pullback.snd (specZIsTerminal.from M.scheme) rationalBaseMap =
        𝟙 (Spec (.of ℚ))
      exact pullback.lift_snd _ _ _)

/-- Projecting the lifted rational-fibre point recovers the original coarse
point. -/
@[simp]
theorem rationalFiberPointMorphism_left_fst (M : CoarseSpace)
    (p : Spec (.of ℚ) ⟶ M.scheme) :
    (rationalFiberPointMorphism M p).left ≫
        pullback.fst (specZIsTerminal.from M.scheme) rationalBaseMap = p := by
  exact pullback.lift_fst _ _ _

/-- The honest comparison required between the rational fibre of the open
coarse moduli space and the rational-cusp-avoiding `D(X)` locus in the
explicit projective cubic.  The target is an actual open subscheme over
`Spec Q`, and the map is an open immersion into it. -/
structure RationalFiberOpenComparison (M : CoarseSpace) where
  /-- The comparison morphism over `Spec Q`. -/
  map : rationalFiberOver M ⟶ SchemeModel.rationalCuspAvoidingOver
  /-- The comparison identifies the coarse fibre with an open part of the
  rational-cusp-avoiding locus. -/
  map_isOpenImmersion : IsOpenImmersion map.left

namespace RationalFiberOpenComparison

/-- Composing the comparison with the inclusion of `D(X)` gives an open
immersion into the represented projective cubic. -/
theorem map_comp_rationalCuspAvoidingInclusion_isOpenImmersion
    {M : CoarseSpace} (C : RationalFiberOpenComparison M) :
    IsOpenImmersion
      (C.map.left ≫ SchemeModel.rationalCuspAvoidingInclusion) := by
  unfold SchemeModel.rationalCuspAvoidingInclusion
  exact @IsOpenImmersion.comp _ _ _ C.map.left
    SchemeModel.rationalCuspAvoidingOpen.ι C.map_isOpenImmersion
    (Scheme.Opens.instIsOpenImmersionι
      SchemeModel.rationalCuspAvoidingOpen)

/-- A rational point of the coarse fibre would give a forbidden noncuspidal
rational point of the explicit cubic. -/
theorem no_rationalFiberPoint {M : CoarseSpace}
    (C : RationalFiberOpenComparison M)
    (p : Over.mk (𝟙 (Spec (.of ℚ))) ⟶ rationalFiberOver M) : False :=
  SchemeModel.not_isNoncuspidal _
    (SchemeModel.comp_rationalCuspAvoidingInclusion_isNoncuspidal
      (p ≫ C.map).left)

/-- The supplied open comparison makes the rational fibre empty on
`Q`-points. -/
theorem rationalFiberPoints_isEmpty {M : CoarseSpace}
    (C : RationalFiberOpenComparison M) :
    IsEmpty (Over.mk (𝟙 (Spec (.of ℚ))) ⟶ rationalFiberOver M) :=
  ⟨C.no_rationalFiberPoint⟩

/-- Every rational point of the global coarse space lifts to the rational
fibre, so the supplied comparison makes these points empty as well. -/
theorem coarseRationalPoints_isEmpty {M : CoarseSpace}
    (C : RationalFiberOpenComparison M) :
    IsEmpty (Spec (.of ℚ) ⟶ M.scheme) := by
  constructor
  intro p
  exact C.no_rationalFiberPoint (rationalFiberPointMorphism M p)

/-- Send a rational point of the global coarse scheme through its rational
fibre and the explicit open comparison. -/
def pointOnScheme {M : CoarseSpace} (C : RationalFiberOpenComparison M)
    (p : Spec (.of ℚ) ⟶ M.scheme) :
    Spec (.of ℚ) ⟶ SchemeModel.scheme :=
  (rationalFiberPointMorphism M p ≫ C.map).left ≫
    SchemeModel.rationalCuspAvoidingInclusion

/-- Points sent through the comparison avoid both represented cusps. -/
theorem pointOnScheme_isNoncuspidal {M : CoarseSpace}
    (C : RationalFiberOpenComparison M)
    (p : Spec (.of ℚ) ⟶ M.scheme) :
    SchemeModel.IsNoncuspidal (pointOnScheme C p) :=
  SchemeModel.comp_rationalCuspAvoidingInclusion_isNoncuspidal _

/-- The exact-order-49 family classifies to the explicit projective cubic
through a supplied coarse space and rational-fibre comparison. -/
def pointOfOrderFortyNineTorsion
    {M : CoarseSpace} (C : RationalFiberOpenComparison M)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (hP : addOrderOf P = 49) :
    Spec (.of ℚ) ⟶ SchemeModel.scheme :=
  pointOnScheme C (coarseModuliPointOfOrderFortyNineTorsion M E P hP)

/-- The modular point attached to exact order-49 torsion is noncuspidal once
the supplied comparison is available. -/
theorem pointOfOrderFortyNineTorsion_isNoncuspidal
    {M : CoarseSpace} (C : RationalFiberOpenComparison M)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (hP : addOrderOf P = 49) :
    SchemeModel.IsNoncuspidal
      (pointOfOrderFortyNineTorsion C E P hP) :=
  pointOnScheme_isNoncuspidal C _

/-- The modular-route order-49 endpoint: a coarse space and its honest open
rational-fibre comparison with the explicit cubic exclude exact order 49. -/
theorem rationalPoint_addOrderOf_ne_fortyNine_of_coarseOpenComparison
    {M : CoarseSpace} (C : RationalFiberOpenComparison M)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) : addOrderOf P ≠ 49 := by
  intro hP
  exact C.no_rationalFiberPoint
    (rationalFiberPointMorphism M
      (coarseModuliPointOfOrderFortyNineTorsion M E P hP))

end RationalFiberOpenComparison
end MazurTorsion.XZeroFortyNine.CoarseComparison
