/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentOverlapCast
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarOverlapAssembly

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

lemma appIso_inv_comp_transport
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (hV : f ''ᵁ U = V) (hW : g ''ᵁ V = W)
    (hC : (f ≫ g) ''ᵁ U = W)
    (z : Γ(X, U)) :
    (Z.presheaf.mapIso (eqToIso hW).op).inv.hom
        ((g.appIso V).inv.hom
          ((Y.presheaf.mapIso (eqToIso hV).op).inv.hom
            ((f.appIso U).inv.hom z))) =
      (Z.presheaf.mapIso (eqToIso hC).op).inv.hom
        (((f ≫ g).appIso U).inv.hom z) := by
  subst V
  subst W
  simp only [Scheme.Hom.comp_appIso, Iso.trans_inv,
    ConcreteCategory.comp_apply]
  simp

lemma appIso_inv_congr_transport
    {X Y : Scheme} {f g : X ⟶ Y}
    (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (U : X.Opens) (W : Y.Opens)
    (hf : f ''ᵁ U = W) (hg : g ''ᵁ U = W)
    (z : Γ(X, U)) :
    (Y.presheaf.mapIso (eqToIso hf).op).inv.hom
        ((f.appIso U).inv.hom z) =
      (Y.presheaf.mapIso (eqToIso hg).op).inv.hom
        ((g.appIso U).inv.hom z) := by
  subst g
  simp

def pairUnitSectionToAmbientDirect
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    Γ(scheme ℚ d, laurentOpen ℚ d I) :=
  ((scheme ℚ d).presheaf.mapIso
      (eqToIso (pairPreimageLaurentOpen_image d I i j)).op).inv.hom
    (((integerPairOverlapMap ℚ d i.1 j.1).appIso
      (pairPreimageLaurentOpen d I i j)).inv.hom z)

lemma pairUnitSectionToAmbientViaFirstChart_eq_direct
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    pairUnitSectionToAmbientViaFirstChart d I i j z =
      pairUnitSectionToAmbientDirect d I i j z := by
  unfold pairUnitSectionToAmbientViaFirstChart
    pairUnitSectionToAmbientDirect integerPairOverlapMap
  exact appIso_inv_comp_transport
    (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
    (standardChart ℚ i.1).ι
    (pairPreimageLaurentOpen d I i j)
    (chartPreimageLaurentOpen ℚ d I i)
    (laurentOpen ℚ d I)
    (firstOverlapMap_image_pairPreimage d I i j)
    (chartPreimageLaurentOpen_image ℚ d I i)
    (pairPreimageLaurentOpen_image d I i j)
    z

def pairUnitSectionToAmbientSecondDirect
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    Γ(scheme ℚ d, laurentOpen ℚ d I) :=
  ((scheme ℚ d).presheaf.mapIso
      (eqToIso
        (integerSecondPairOverlapMap_image d I i j)).op).inv.hom
    (((integerSecondPairOverlapMap d i.1 j.1).appIso
      (pairPreimageLaurentOpen d I i j)).inv.hom z)

lemma pairUnitSectionToAmbientViaSecondChart_eq_direct
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    pairUnitSectionToAmbientViaSecondChart d I i j z =
      pairUnitSectionToAmbientSecondDirect d I i j z := by
  unfold pairUnitSectionToAmbientViaSecondChart
    pairUnitSectionToAmbientSecondDirect
    integerSecondPairOverlapMap
  exact appIso_inv_comp_transport
    (typedIntegerSecondOverlapMap ℚ d i.1 j.1)
    (standardChart ℚ j.1).ι
    (pairPreimageLaurentOpen d I i j)
    (chartPreimageLaurentOpen ℚ d I j)
    (laurentOpen ℚ d I)
    (secondOverlapMap_image_pairPreimage d I i j)
    (chartPreimageLaurentOpen_image ℚ d I j)
    (integerSecondPairOverlapMap_image d I i j)
    z

lemma pairUnitSectionToAmbientDirect_eq_secondDirect
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    pairUnitSectionToAmbientDirect d I i j z =
      pairUnitSectionToAmbientSecondDirect d I i j z := by
  unfold pairUnitSectionToAmbientDirect
    pairUnitSectionToAmbientSecondDirect
  exact (appIso_inv_congr_transport
    (integerSecondPairOverlapMap_eq_first d i.1 j.1)
    (pairPreimageLaurentOpen d I i j)
    (laurentOpen ℚ d I)
    (integerSecondPairOverlapMap_image d I i j)
    (pairPreimageLaurentOpen_image d I i j)
    z).symm

lemma pairUnitSectionToAmbient_chart_independent
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    pairUnitSectionToAmbientViaFirstChart d I i j z =
      pairUnitSectionToAmbientViaSecondChart d I i j z := by
  exact
    (pairUnitSectionToAmbientViaFirstChart_eq_direct
      d I i j z).trans <|
      (pairUnitSectionToAmbientDirect_eq_secondDirect
        d I i j z).trans <|
        (pairUnitSectionToAmbientViaSecondChart_eq_direct
          d I i j z).symm

lemma pairUnitSectionToAmbientViaSecondChart_mul
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z w : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    pairUnitSectionToAmbientViaSecondChart d I i j (z * w) =
      pairUnitSectionToAmbientViaSecondChart d I i j z *
        pairUnitSectionToAmbientViaSecondChart d I i j w := by
  unfold pairUnitSectionToAmbientViaSecondChart
  let F :=
    ((scheme ℚ d).presheaf.mapIso
      (eqToIso (chartPreimageLaurentOpen_image
        ℚ d I j)).op).inv.hom.comp
      (((standardChart ℚ j.1).ι.appIso
        (chartPreimageLaurentOpen ℚ d I j)).inv.hom.comp
        (((standardChart ℚ j.1).toScheme.presheaf.mapIso
          (eqToIso (secondOverlapMap_image_pairPreimage
            d I i j)).op).inv.hom.comp
          ((typedIntegerSecondOverlapMap ℚ d i.1 j.1).appIso
            (pairPreimageLaurentOpen d I i j)).inv.hom))
  change F (z * w) = F z * F w
  exact F.map_mul z w

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
