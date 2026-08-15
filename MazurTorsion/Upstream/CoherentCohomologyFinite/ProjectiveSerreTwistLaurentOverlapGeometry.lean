/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafPullbackUnitSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentChartIndependence

/-!
# Integer Serre-twist sections on Laurent chart overlaps

This file realizes a Laurent-open section on a scheme-theoretic pair
overlap and proves that the first projective chart leg recovers the
ordinary Laurent coordinate in that chart.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

/-- The first projection from a pair overlap to its exposed standard
chart.  Naming this map keeps the public `Fin` index out of reducibility
checks for the dependent glued-cover index. -/
def typedIntegerPairOverlapScheme
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) : Scheme :=
  (glueData k d).V (i, j)

def typedIntegerFirstOverlapMap
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    typedIntegerPairOverlapScheme k d i j ⟶
      (standardChart k i).toScheme :=
  (glueData k d).f i j

instance typedIntegerFirstOverlapMap_isOpenImmersion
    (k : Type) [CommRing k] (d : ℕ) (i j : Fin (d + 1)) :
    IsOpenImmersion (typedIntegerFirstOverlapMap k d i j) := by
  change IsOpenImmersion
    (pullback.fst (standardChart k i).ι (standardChart k j).ι)
  infer_instance

/-- The chart trivialization with both source and target written using
the exposed standard chart. -/
def typedIntegerChartHom
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (i : Fin (d + 1)) :
    (Scheme.Modules.pullback (standardChart k i).ι).obj
        (OInt k d m) ⟶
      SheafOfModules.unit (standardChart k i).toScheme.ringCatSheaf :=
  (integerChartIso k d m i).hom

/-- The pullback-unit comparison with the exposed overlap scheme in its
target. -/
def typedIntegerFirstPullbackUnitHom
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    (Scheme.Modules.pullback
      (typedIntegerFirstOverlapMap k d i j)).obj
        (SheafOfModules.unit
          (standardChart k i).toScheme.ringCatSheaf) ⟶
      SheafOfModules.unit
        (typedIntegerPairOverlapScheme k d i j).ringCatSheaf :=
  (pullbackUnitIso (typedIntegerFirstOverlapMap k d i j)).hom

/-- The pair-overlap scheme mapped to projective space through its first
chart. -/
def integerPairOverlapMap
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    typedIntegerPairOverlapScheme k d i j ⟶ scheme k d :=
  typedIntegerFirstOverlapMap k d i j ≫ (standardChart k i).ι

instance integerPairOverlapMap_isOpenImmersion
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    IsOpenImmersion (integerPairOverlapMap k d i j) := by
  dsimp only [integerPairOverlapMap]
  infer_instance

lemma integerPairOverlapMap_opensRange
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    (integerPairOverlapMap k d i j).opensRange =
      standardChart k i ⊓ standardChart k j := by
  apply TopologicalSpace.Opens.ext
  change Set.range
      ((pullback.fst (standardChart k i).ι (standardChart k j).ι ≫
        (standardChart k i).ι).base) =
    (standardChart k i ⊓ standardChart k j : (scheme k d).Opens)
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  change
    Set.range ⇑(standardChart k i).ι ∩
        Set.range ⇑(standardChart k j).ι =
      (standardChart k i : Set _) ∩
        (standardChart k j : Set _)
  exact congrArg₂ (· ∩ ·)
    (Scheme.Opens.range_ι (standardChart k i))
    (Scheme.Opens.range_ι (standardChart k j))

/-- The preimage of a Laurent open on the pair-overlap scheme. -/
def pairPreimageLaurentOpen
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    (typedIntegerPairOverlapScheme ℚ d i.1 j.1).Opens :=
  integerPairOverlapMap ℚ d i.1 j.1 ⁻¹ᵁ
    laurentOpen ℚ d I

lemma pairPreimageLaurentOpen_image
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    integerPairOverlapMap ℚ d i.1 j.1 ''ᵁ
        pairPreimageLaurentOpen d I i j =
      laurentOpen ℚ d I := by
  rw [pairPreimageLaurentOpen,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    integerPairOverlapMap_opensRange,
    inf_eq_right]
  exact le_inf
    (laurentOpen_le_standardChart ℚ d I i)
    (laurentOpen_le_standardChart ℚ d I j)

lemma pairPreimageLaurentOpen_eq_firstChartPreimage
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    pairPreimageLaurentOpen d I i j =
      typedIntegerFirstOverlapMap ℚ d i.1 j.1 ⁻¹ᵁ
        chartPreimageLaurentOpen ℚ d I i := by
  unfold pairPreimageLaurentOpen
    chartPreimageLaurentOpen integerPairOverlapMap
  rw [Scheme.Hom.comp_preimage]

lemma firstOverlapMap_opensRange
    (d : ℕ) (i j : Fin (d + 1)) :
    (typedIntegerFirstOverlapMap ℚ d i j).opensRange =
      (standardChart ℚ i).ι ⁻¹ᵁ standardChart ℚ j := by
  change
    (pullback.fst (standardChart ℚ i).ι
      (standardChart ℚ j).ι).opensRange =
        (standardChart ℚ i).ι ⁻¹ᵁ standardChart ℚ j
  rw [Scheme.Hom.opensRange_pullbackFst]
  congr 1
  apply TopologicalSpace.Opens.ext
  exact Scheme.Opens.range_ι (standardChart ℚ j)

lemma firstOverlapMap_image_pairPreimage
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    typedIntegerFirstOverlapMap ℚ d i.1 j.1 ''ᵁ
        pairPreimageLaurentOpen d I i j =
      chartPreimageLaurentOpen ℚ d I i := by
  rw [pairPreimageLaurentOpen_eq_firstChartPreimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    firstOverlapMap_opensRange, inf_eq_right]
  exact Scheme.Hom.preimage_mono (standardChart ℚ i.1).ι
    (laurentOpen_le_standardChart ℚ d I j)

/-- Restrict an ambient twist section to a standard chart. -/
def ambientSectionToIntegerChartRestriction
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((OInt ℚ d m).restrict (standardChart ℚ i.1).ι,
      chartPreimageLaurentOpen ℚ d I i) :=
  ((OInt ℚ d m).restrictAppIso
      (standardChart ℚ i.1).ι
      (chartPreimageLaurentOpen ℚ d I i)).inv.hom
    (((OInt ℚ d m).presheaf.mapIso
      (eqToIso (chartPreimageLaurentOpen_image
        ℚ d I i)).op).hom.hom x)

/-- The same chart restriction in the pullback presentation. -/
def integerChartPullbackSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((Scheme.Modules.pullback
        (standardChart ℚ i.1).ι).obj (OInt ℚ d m),
      chartPreimageLaurentOpen ℚ d I i) :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (standardChart ℚ i.1).ι).hom.app
        (OInt ℚ d m)).app
    (chartPreimageLaurentOpen ℚ d I i)
    (ambientSectionToIntegerChartRestriction d m I i x)

/-- Restrict the chart pullback further to the pair overlap. -/
def integerFirstOverlapRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ(((Scheme.Modules.pullback (standardChart ℚ i.1).ι).obj
        (OInt ℚ d m)).restrict
          (typedIntegerFirstOverlapMap ℚ d i.1 j.1),
      pairPreimageLaurentOpen d I i j) :=
  (((Scheme.Modules.pullback
      (standardChart ℚ i.1).ι).obj
        (OInt ℚ d m)).restrictAppIso
          (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
          (pairPreimageLaurentOpen d I i j)).inv.hom
    ((((Scheme.Modules.pullback
        (standardChart ℚ i.1).ι).obj
          (OInt ℚ d m)).presheaf.mapIso
        (eqToIso
          (firstOverlapMap_image_pairPreimage d I i j)).op).hom.hom
      (integerChartPullbackSection d m I i x))

/-- Present the preceding restriction as a pullback along the first
overlap map. -/
def integerFirstOverlapPullbackSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((Scheme.Modules.pullback
        (typedIntegerFirstOverlapMap ℚ d i.1 j.1)).obj
          ((Scheme.Modules.pullback (standardChart ℚ i.1).ι).obj
            (OInt ℚ d m)),
      pairPreimageLaurentOpen d I i j) :=
  (((Scheme.Modules.restrictFunctorIsoPullback
      (typedIntegerFirstOverlapMap ℚ d i.1 j.1)).hom.app
        ((Scheme.Modules.pullback
          (standardChart ℚ i.1).ι).obj
            (OInt ℚ d m))).app
      (pairPreimageLaurentOpen d I i j)
      (integerFirstOverlapRestrictionSection d m I i j x))

/-- The induced section of the direct projective-overlap pullback. -/
def integerPairOverlapSectionViaFirstChart
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    IntegerOverlapSection ℚ d m i.1 j.1
      (pairPreimageLaurentOpen d I i j) :=
  ((Scheme.Modules.pullbackComp
      (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
      (standardChart ℚ i.1).ι).hom.app
        (OInt ℚ d m)).app
    (pairPreimageLaurentOpen d I i j)
    (integerFirstOverlapPullbackSection d m I i j x)

/-- Apply the chart trivialization before the first-overlap pullback
comparison. -/
def integerFirstChartUnitRestrictionSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((standardChart ℚ i.1).toScheme,
      typedIntegerFirstOverlapMap ℚ d i.1 j.1 ''ᵁ
        pairPreimageLaurentOpen d I i j) :=
  ((Scheme.Modules.restrictFunctor
    (typedIntegerFirstOverlapMap ℚ d i.1 j.1)).map
      (typedIntegerChartHom ℚ d m i.1)).app
    (pairPreimageLaurentOpen d I i j)
    (integerFirstOverlapRestrictionSection d m I i j x)

/-- The unit-module section in the chosen chart frame. -/
def integerChartUnitSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ(SheafOfModules.unit (standardChart ℚ i.1).toScheme.ringCatSheaf,
      chartPreimageLaurentOpen ℚ d I i) :=
  (typedIntegerChartHom ℚ d m i.1).app
    (chartPreimageLaurentOpen ℚ d I i)
    (integerChartPullbackSection d m I i x)

lemma integerFirstChartUnitRestrictionSection_transport
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    (((standardChart ℚ i.1).toScheme.presheaf.mapIso
      (eqToIso
        (firstOverlapMap_image_pairPreimage d I i j)).op).inv.hom
        (integerFirstChartUnitRestrictionSection d m I i j x)) =
      integerChartUnitSection d m I i x := by
  unfold integerFirstChartUnitRestrictionSection
    integerFirstOverlapRestrictionSection
    integerChartUnitSection
  exact moduleHom_mapIso_inv_hom_app_mapIso_hom
    (typedIntegerChartHom ℚ d m i.1)
    (firstOverlapMap_image_pairPreimage d I i j)
    (integerChartPullbackSection d m I i x)

/-- Transport a regular function on the pair overlap back to the ambient
Laurent open through the first chart. -/
def pairUnitSectionToAmbientViaFirstChart
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (z : Γ(typedIntegerPairOverlapScheme ℚ d i.1 j.1,
      pairPreimageLaurentOpen d I i j)) :
    Γ(scheme ℚ d, laurentOpen ℚ d I) :=
  ((scheme ℚ d).presheaf.mapIso
      (eqToIso (chartPreimageLaurentOpen_image
        ℚ d I i)).op).inv.hom
    (((standardChart ℚ i.1).ι.appIso
      (chartPreimageLaurentOpen ℚ d I i)).inv.hom
      (((standardChart ℚ i.1).toScheme.presheaf.mapIso
        (eqToIso
          (firstOverlapMap_image_pairPreimage d I i j)).op).inv.hom
        (((typedIntegerFirstOverlapMap ℚ d i.1 j.1).appIso
          (pairPreimageLaurentOpen d I i j)).inv.hom z)))

/-- The first projective scalar leg with its overlap projection written
through the typed compatibility map used in this file. -/
def typedProjectiveIntegerFirstScalarLeg
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (i j : Fin (d + 1)) :=
  projectiveIntegerFirstChartLeg k d m i j ≫
    typedIntegerFirstPullbackUnitHom k d i j

lemma typedIntegerFirstPullbackUnitHom_app
    (k : Type) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1))
    (W : (typedIntegerPairOverlapScheme k d i j).Opens)
    (y : Γ((standardChart k i).toScheme,
      typedIntegerFirstOverlapMap k d i j ''ᵁ W)) :
    (typedIntegerFirstPullbackUnitHom k d i j).app W
        (((Scheme.Modules.restrictFunctorIsoPullback
          (typedIntegerFirstOverlapMap k d i j)).hom.app
            (SheafOfModules.unit
              (standardChart k i).toScheme.ringCatSheaf)).app W y) =
      ((typedIntegerFirstOverlapMap k d i j).appIso W).hom y := by
  exact restrictFunctorIsoPullback_unit_app
    (typedIntegerFirstOverlapMap k d i j) W y

/-- The ambient regular function obtained from the first projective
scalar leg. -/
def projectiveFirstAmbientCoordinate
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ(scheme ℚ d, laurentOpen ℚ d I) :=
  pairUnitSectionToAmbientViaFirstChart d I i j
    ((typedProjectiveIntegerFirstScalarLeg ℚ d m i.1 j.1).app
      (pairPreimageLaurentOpen d I i j)
      (integerPairOverlapSectionViaFirstChart d m I i j x))

lemma projectiveIntegerFirstChartLeg_pullbackComp_hom_app
    (d : ℕ) (m : ℤ) (i j : Fin (d + 1))
    (W : (typedIntegerPairOverlapScheme ℚ d i j).Opens)
    (z : Γ((Scheme.Modules.pullback
        (typedIntegerFirstOverlapMap ℚ d i j)).obj
          ((Scheme.Modules.pullback
            (standardChart ℚ i).ι).obj
              (OInt ℚ d m)), W)) :
    (projectiveIntegerFirstChartLeg ℚ d m i j).app W
        (((Scheme.Modules.pullbackComp
          (typedIntegerFirstOverlapMap ℚ d i j)
          (standardChart ℚ i).ι).hom.app
            (OInt ℚ d m)).app W z) =
      ((Scheme.Modules.pullback
        (typedIntegerFirstOverlapMap ℚ d i j)).map
          (typedIntegerChartHom ℚ d m i)).app W z := by
  unfold projectiveIntegerFirstChartLeg
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  apply congrArg (fun y =>
    ((Scheme.Modules.pullback
      (typedIntegerFirstOverlapMap ℚ d i j)).map
        (typedIntegerChartHom ℚ d m i)).app W y)
  change
    (sectionsAddEquivOfIsoAt
      ((Scheme.Modules.pullbackComp
        (typedIntegerFirstOverlapMap ℚ d i j)
        (standardChart ℚ i).ι).app
          (OInt ℚ d m)) W).symm
      ((sectionsAddEquivOfIsoAt
        ((Scheme.Modules.pullbackComp
          (typedIntegerFirstOverlapMap ℚ d i j)
          (standardChart ℚ i).ι).app
            (OInt ℚ d m)) W) z) = z
  exact (sectionsAddEquivOfIsoAt
    ((Scheme.Modules.pullbackComp
      (typedIntegerFirstOverlapMap ℚ d i j)
      (standardChart ℚ i).ι).app
        (OInt ℚ d m)) W).symm_apply_apply z

lemma projectiveFirstScalarSection_eq_appIso
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    (typedProjectiveIntegerFirstScalarLeg
      ℚ d m i.1 j.1).app
        (pairPreimageLaurentOpen d I i j)
        (integerPairOverlapSectionViaFirstChart d m I i j x) =
      ((typedIntegerFirstOverlapMap ℚ d i.1 j.1).appIso
        (pairPreimageLaurentOpen d I i j)).hom
        (integerFirstChartUnitRestrictionSection d m I i j x) := by
  unfold integerPairOverlapSectionViaFirstChart
    typedProjectiveIntegerFirstScalarLeg
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  change
    (typedIntegerFirstPullbackUnitHom ℚ d i.1 j.1).app
        (pairPreimageLaurentOpen d I i j)
        ((projectiveIntegerFirstChartLeg ℚ d m i.1 j.1).app
          (pairPreimageLaurentOpen d I i j)
          (((Scheme.Modules.pullbackComp
            (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
            (standardChart ℚ i.1).ι).hom.app
              (OInt ℚ d m)).app
            (pairPreimageLaurentOpen d I i j)
            (integerFirstOverlapPullbackSection d m I i j x))) = _
  rw [projectiveIntegerFirstChartLeg_pullbackComp_hom_app]
  unfold integerFirstOverlapPullbackSection
  have hnat :=
    restrictFunctorIsoPullback_hom_app_naturality
      (typedIntegerFirstOverlapMap ℚ d i.1 j.1)
      (typedIntegerChartHom ℚ d m i.1)
      (pairPreimageLaurentOpen d I i j)
      (integerFirstOverlapRestrictionSection d m I i j x)
  exact (congrArg
    (fun z =>
      (typedIntegerFirstPullbackUnitHom ℚ d i.1 j.1).app
        (pairPreimageLaurentOpen d I i j) z)
    hnat).trans
      (typedIntegerFirstPullbackUnitHom_app ℚ d i.1 j.1
        (pairPreimageLaurentOpen d I i j)
        (integerFirstChartUnitRestrictionSection d m I i j x))

/-- The first projective overlap coordinate agrees with the Laurent-open
coordinate defined directly from the chosen chart trivialization. -/
lemma projectiveFirstAmbientCoordinate_eq_chart
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1)))
    (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    projectiveFirstAmbientCoordinate d m I i j x =
      integerChartLaurentSectionsAddEquiv d m I i x := by
  unfold projectiveFirstAmbientCoordinate
    pairUnitSectionToAmbientViaFirstChart
  rw [projectiveFirstScalarSection_eq_appIso]
  rw [Iso.hom_inv_id_apply]
  rw [integerFirstChartUnitRestrictionSection_transport]
  unfold integerChartUnitSection
    integerChartPullbackSection
    ambientSectionToIntegerChartRestriction
    integerChartLaurentSectionsAddEquiv
    integerChartRestrictIso
    sectionsAddEquivOfIsoAt
    unitSectionsAddEquivAt
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
