/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentScalarGeometry
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistPairLaurentFraction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartRatioTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartTripleOverlap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartPairScalarCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistSectionCechComparison

/-!
# Laurent coordinate transitions for integer Serre twists

This file combines the projective overlap scalar calculation with the
homogeneous Laurent model.  It identifies the inverse transition scalar
with the chart-change monomial and proves chart independence for every
integer twist.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

/-- The first scalar overlap section attached to a Laurent-open section. -/
def integerFirstScalarPairSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((glueData ℚ d).V (i.1, j.1),
      pairPreimageLaurentOpen d I i j) :=
  (projectiveIntegerFirstScalarLeg ℚ d m i.1 j.1).app
    (pairPreimageLaurentOpen d I i j)
    (integerPairOverlapSectionViaFirstChart d m I i j x)

/-- The complete raw second scalar overlap section, including the
inverse transition endomorphism. -/
def integerRawSecondScalarPairSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((glueData ℚ d).V (i.1, j.1),
      pairPreimageLaurentOpen d I i j) :=
  ((((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation
          ℚ d i.1 j.1)).inv.app
        (OInt ℚ d m) ≫
      projectiveIntegerSecondChartLegCore
        ℚ d m i.1 j.1) ≫
    ((pullbackUnitIso
        ((glueData ℚ d).t i.1 j.1 ≫
          (glueData ℚ d).f j.1 i.1)).hom ≫
      endomorphism
        (((overlapUnit ℚ d i.1 j.1) ^ m).inv))).app
    (pairPreimageLaurentOpen d I i j)
    (integerPairOverlapSectionViaFirstChart d m I i j x))

/-- The raw second-chart overlap section before the inverse transition
scalar is applied. -/
def integerRawSecondUnscaledPairSection
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    Γ((glueData ℚ d).V (i.1, j.1),
      pairPreimageLaurentOpen d I i j) :=
  (projectiveIntegerSecondChartLegCore
        ℚ d m i.1 j.1 ≫
      (pullbackUnitIso
        (integerSecondOverlapMap ℚ d i.1 j.1)).hom).app
    (pairPreimageLaurentOpen d I i j)
    (((Scheme.Modules.pullbackCongr
      (projectiveIntegerOverlapEquation
        ℚ d i.1 j.1)).inv.app
        (OInt ℚ d m)).app
      (pairPreimageLaurentOpen d I i j)
      (integerPairOverlapSectionViaFirstChart
        d m I i j x))

lemma rawSecondUnscaledAmbient_eq_chart
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    pairUnitSectionToAmbientViaSecondChart d I i j
      ((projectiveIntegerSecondChartLegCore
          ℚ d m i.1 j.1 ≫
        (pullbackUnitIso
          (integerSecondOverlapMap ℚ d i.1 j.1)).hom).app
        (pairPreimageLaurentOpen d I i j)
        (((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation
            ℚ d i.1 j.1)).inv.app
            (OInt ℚ d m)).app
          (pairPreimageLaurentOpen d I i j)
          (integerPairOverlapSectionViaFirstChart
            d m I i j x))) =
      integerChartLaurentSectionsAddEquiv d m I j x := by
  rw [rawCast_firstPairSection_eq_secondPairSection]
  exact projectiveSecondChartAmbientCoordinate_eq_chart
    d m I i j x

/-- The inverse integer transition scalar, restricted from the full
scheme-theoretic overlap to the Laurent preimage. -/
def integerInverseTransitionSectionOnPair
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I) :
    Γ((glueData ℚ d).V (i.1, j.1),
      pairPreimageLaurentOpen d I i j) :=
  ((glueData ℚ d).V (i.1, j.1)).presheaf.map
      (homOfLE le_top).op
    (((overlapUnit ℚ d i.1 j.1) ^ m).inv)

/-- The first scalar leg, transported through the second overlap map,
is the ambient Laurent coordinate computed in chart `i`. -/
lemma firstScalarAmbient_eq_chart
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    pairUnitSectionToAmbientViaSecondChart d I i j
        ((projectiveIntegerFirstScalarLeg
          ℚ d m i.1 j.1).app
          (pairPreimageLaurentOpen d I i j)
          (integerPairOverlapSectionViaFirstChart
            d m I i j x)) =
      integerChartLaurentSectionsAddEquiv d m I i x := by
  calc
    _ = projectiveFirstAmbientCoordinate d m I i j x := by
      unfold projectiveFirstAmbientCoordinate
      exact (pairUnitSectionToAmbient_chart_independent
        d I i j _).symm
    _ = _ :=
      projectiveFirstAmbientCoordinate_eq_chart d m I i j x

private theorem eq_trans_two
    {α : Sort*} {a₀ a₁ a₂ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) :
    a₀ = a₂ :=
  h₀.trans h₁

lemma moduleHom_four_comp_app
    {X : Scheme}
    {M₀ M₁ M₂ M₃ M₄ : X.Modules}
    (f₀ : M₀ ⟶ M₁) (f₁ : M₁ ⟶ M₂)
    (f₂ : M₂ ⟶ M₃) (f₃ : M₃ ⟶ M₄)
    (U : X.Opens) (x : Γ(M₀, U)) :
    (((f₀ ≫ f₁) ≫ (f₂ ≫ f₃)).app U x) =
      f₃.app U (f₂.app U (f₁.app U (f₀.app U x))) := by
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]

lemma moduleHom_comp_app_apply
    {X : Scheme}
    {M₀ M₁ M₂ : X.Modules}
    (f₀ : M₀ ⟶ M₁) (f₁ : M₁ ⟶ M₂)
    (U : X.Opens) (x : Γ(M₀, U)) :
    (f₀ ≫ f₁).app U x =
      f₁.app U (f₀.app U x) := by
  simp only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]

/-- Transport the raw overlap equality before evaluating its final
scalar endomorphism. -/
def rawScalarAmbientBeforeEvaluation
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChart d I i j)
    (projectiveIntegerFirstScalar_eq_rawSecondScalar_app
      ℚ d m i.1 j.1
      (pairPreimageLaurentOpen d I i j)
      (integerPairOverlapSectionViaFirstChart d m I i j x))

/-- Reassociate the raw composite so that its final scalar endomorphism
is exposed as an application. -/
def rawScalarAmbientNormalize
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChart d I i j)
    (moduleHom_four_comp_app
      ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation
          ℚ d i.1 j.1)).inv.app
        (OInt ℚ d m))
      (projectiveIntegerSecondChartLegCore
        ℚ d m i.1 j.1)
      (pullbackUnitIso
        (integerSecondOverlapMap ℚ d i.1 j.1)).hom
      (endomorphism
        (((overlapUnit ℚ d i.1 j.1) ^ m).inv))
      (pairPreimageLaurentOpen d I i j)
      (integerPairOverlapSectionViaFirstChart d m I i j x))

/-- Transport evaluation of the final overlap scalar endomorphism. -/
def rawScalarAmbientEvaluation
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChart d I i j)
    (endomorphism_app
      (((overlapUnit ℚ d i.1 j.1) ^ m).inv)
      (Opposite.op (pairPreimageLaurentOpen d I i j))
      ((pullbackUnitIso
        (integerSecondOverlapMap ℚ d i.1 j.1)).hom.app
        (pairPreimageLaurentOpen d I i j)
        ((projectiveIntegerSecondChartLegCore
          ℚ d m i.1 j.1).app
          (pairPreimageLaurentOpen d I i j)
          (((Scheme.Modules.pullbackCongr
            (projectiveIntegerOverlapEquation
              ℚ d i.1 j.1)).inv.app
              (OInt ℚ d m)).app
            (pairPreimageLaurentOpen d I i j)
            (integerPairOverlapSectionViaFirstChart
              d m I i j x)))))

/-- Regroup the unscaled nested applications into the named two-map
composite before using multiplicativity of ambient transport. -/
def rawScalarAmbientUnscaledNormalize
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  congrArg
    (pairUnitSectionToAmbientViaSecondChart d I i j)
    (congrArg
      (fun z => z *
        integerInverseTransitionSectionOnPair d m I i j)
      (moduleHom_comp_app_apply
        (projectiveIntegerSecondChartLegCore
          ℚ d m i.1 j.1)
        (pullbackUnitIso
          (integerSecondOverlapMap ℚ d i.1 j.1)).hom
        (pairPreimageLaurentOpen d I i j)
        (((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation
            ℚ d i.1 j.1)).inv.app
            (OInt ℚ d m)).app
          (pairPreimageLaurentOpen d I i j)
          (integerPairOverlapSectionViaFirstChart
            d m I i j x))).symm)

/-- Multiplicativity of ambient transport, specialized to the two raw
factors in the integer overlap calculation. -/
def rawScalarAmbientMultiplication
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  pairUnitSectionToAmbientViaSecondChart_mul d I i j
    (show Γ((glueData ℚ d).V (i.1, j.1),
        pairPreimageLaurentOpen d I i j) from
      ((projectiveIntegerSecondChartLegCore
          ℚ d m i.1 j.1 ≫
        (pullbackUnitIso
          (integerSecondOverlapMap ℚ d i.1 j.1)).hom).app
        (pairPreimageLaurentOpen d I i j)
        (((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation
            ℚ d i.1 j.1)).inv.app
            (OInt ℚ d m)).app
          (pairPreimageLaurentOpen d I i j)
          (integerPairOverlapSectionViaFirstChart
            d m I i j x))))
    (integerInverseTransitionSectionOnPair d m I i j)

/-- Replace the unscaled raw factor by its chart-`j` ambient
coordinate after multiplication by the common transition factor. -/
def rawSecondAmbientMul_eq_chartMul
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  congrArg
    (fun z => z *
      pairUnitSectionToAmbientViaSecondChart d I i j
        (integerInverseTransitionSectionOnPair d m I i j))
    (rawSecondUnscaledAmbient_eq_chart d m I i j x)

private theorem eq_trans_seven
    {α : Sort*} {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : α}
    (h₀ : a₀ = a₁) (h₁ : a₁ = a₂) (h₂ : a₂ = a₃)
    (h₃ : a₃ = a₄) (h₄ : a₄ = a₅) (h₅ : a₅ = a₆)
    (h₆ : a₆ = a₇) :
    a₀ = a₇ :=
  h₀.trans (h₁.trans
    (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))))

/-- Opaque assembly of the five adjacent ambient-coordinate steps. -/
def integerChartAmbientCoordinateTransitionRaw
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :=
  eq_trans_seven
    (firstScalarAmbient_eq_chart d m I i j x).symm
    (rawScalarAmbientBeforeEvaluation d m I i j x)
    (rawScalarAmbientNormalize d m I i j x)
    (rawScalarAmbientEvaluation d m I i j x)
    (rawScalarAmbientUnscaledNormalize d m I i j x)
    (rawScalarAmbientMultiplication d m I i j x)
    (rawSecondAmbientMul_eq_chartMul d m I i j x)

/-- Before identifying the transition scalar with its Laurent monomial,
the overlap calculation already says that the chart-`i` coordinate is
the chart-`j` coordinate times the transported inverse transition. -/
theorem integerChartAmbientCoordinate_eq_mul_transition
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt ℚ d m, laurentOpen ℚ d I)) :
    integerChartLaurentSectionsAddEquiv d m I i x =
      integerChartLaurentSectionsAddEquiv d m I j x *
        pairUnitSectionToAmbientViaSecondChart d I i j
          (integerInverseTransitionSectionOnPair d m I i j) :=
  integerChartAmbientCoordinateTransitionRaw d m I i j x

lemma appIso_inv_global_restriction_transport
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) (W B : Y.Opens)
    (hW : f ''ᵁ U = W)
    (hB : f ''ᵁ (⊤ : X.Opens) = B)
    (hWB : W ≤ B) (s : Γ(X, ⊤)) :
    (Y.presheaf.mapIso (eqToIso hW).op).inv.hom
        ((f.appIso U).inv.hom
          (X.presheaf.map
            (homOfLE
              (show U ≤ (⊤ : X.Opens) from le_top)).op s)) =
      Y.presheaf.map (homOfLE hWB).op
        ((Y.presheaf.mapIso (eqToIso hB).op).inv.hom
          ((f.appIso ⊤).inv.hom s)) := by
  rw [appIso_inv_restriction]
  exact presheafMapIsoSymm_restriction
    hB hW
    (Scheme.Hom.image_mono f
      (show U ≤ (⊤ : X.Opens) from le_top))
    hWB
    ((f.appIso ⊤).inv.hom s)

lemma integerPairOverlapMap_image_top_product
    (d : ℕ) (i j : Fin (d + 1)) :
    integerPairOverlapMap ℚ d i j ''ᵁ
        (⊤ : (typedIntegerPairOverlapScheme ℚ d i j).Opens) =
      Proj.basicOpen (homogeneousGrading ℚ d)
        (coordinate ℚ i * coordinate ℚ j) := by
  rw [Scheme.Hom.image_top_eq_opensRange,
    integerPairOverlapMap_opensRange]
  change
    Proj.basicOpen (homogeneousGrading ℚ d) (coordinate ℚ i) ⊓
        Proj.basicOpen (homogeneousGrading ℚ d) (coordinate ℚ j) =
      Proj.basicOpen (homogeneousGrading ℚ d)
        (coordinate ℚ i * coordinate ℚ j)
  exact (Proj.basicOpen_mul
    (homogeneousGrading ℚ d)
    (coordinate ℚ i) (coordinate ℚ j)).symm

lemma opens_ι_appIso_inv_topIso_inv_transport
    {X : Scheme.{0}} (U : X.Opens) (r : Γ(X, U)) :
    (eqToIso (congrArg (fun W => Γ(X, W))
      U.ι_image_top)).hom
        ((U.ι.appIso ⊤).inv.hom (U.topIso.inv r)) = r := by
  have htop :
      (eqToIso (congrArg (fun W => Γ(X, W))
        U.ι_image_top)).hom = U.topIso.hom := by
    rw [Γ_eqToIso_hom_eq_presheaf_map U.ι_image_top]
    symm
    exact Scheme.Opens.topIso_hom U
  rw [htop, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv]
  exact U.topIso.inv_hom_id_apply r

lemma appIso_inv_iso_comp_opens_top
    {A X : Scheme.{0}} (U : X.Opens) (e : A ≅ U.toScheme)
    (hC :
      (e.hom ≫ U.ι) ''ᵁ (⊤ : A.Opens) = U)
    (r : Γ(X, U)) :
    (X.presheaf.mapIso (eqToIso hC).op).inv.hom
        (((e.hom ≫ U.ι).appIso ⊤).inv.hom
          (e.hom.appTop (U.topIso.inv r))) = r := by
  rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom]
  let ho :
      (e.hom ≫ U.ι) ''ᵁ (⊤ : A.Opens) =
        U.ι ''ᵁ (⊤ : U.toScheme.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso]
  have hnat :=
    appIso_inv_natural_iso_over e U.ι (U.topIso.inv r)
  calc
    _ = (eqToIso (congrArg (fun W => Γ(X, W))
          (ho.trans U.ι_image_top))).hom
        (((e.hom ≫ U.ι).appIso ⊤).inv.hom
          (e.hom.appTop (U.topIso.inv r))) := by
      rw [show hC = ho.trans U.ι_image_top from
        Subsingleton.elim _ _]
    _ = (eqToIso (congrArg (fun W => Γ(X, W))
          U.ι_image_top)).hom
        ((eqToIso (congrArg (fun W => Γ(X, W)) ho)).hom
          (((e.hom ≫ U.ι).appIso ⊤).inv.hom
            (e.hom.appTop (U.topIso.inv r)))) :=
      by
        let z :=
          ((e.hom ≫ U.ι).appIso ⊤).inv.hom
            (e.hom.appTop (U.topIso.inv r))
        exact (ConcreteCategory.congr_hom
          (Γ_eqToIso_hom_trans ho U.ι_image_top) z).symm
    _ = (eqToIso (congrArg (fun W => Γ(X, W))
          U.ι_image_top)).hom
        ((U.ι.appIso ⊤).inv.hom (U.topIso.inv r)) := by
      exact congrArg
        (eqToIso (congrArg (fun W => Γ(X, W))
          U.ι_image_top)).hom hnat
    _ = r :=
      opens_ι_appIso_inv_topIso_inv_transport U r

/-- Transport the projective overlap ratio from the scheme-theoretic
overlap to its product basic-open image. -/
def overlapUnitAmbientPairSection
    (d : ℕ) (i j : Fin (d + 1)) :
    Γ(scheme ℚ d,
      Proj.basicOpen (homogeneousGrading ℚ d)
        (coordinate ℚ i * coordinate ℚ j)) :=
  ((scheme ℚ d).presheaf.mapIso
      (eqToIso
        (integerPairOverlapMap_image_top_product d i j)).op).inv.hom
    (((integerPairOverlapMap ℚ d i j).appIso ⊤).inv.hom
      (overlapUnit ℚ d i j).val)

lemma overlapUnitAmbientPairSection_eq_away
    (d : ℕ) (i j : Fin (d + 1)) :
    overlapUnitAmbientPairSection d i j =
      Proj.awayToSection (homogeneousGrading ℚ d)
        (coordinate ℚ i * coordinate ℚ j)
        (awayFraction ℚ d i j) := by
  let B : (scheme ℚ d).Opens :=
    Proj.basicOpen (homogeneousGrading ℚ d)
      (coordinate ℚ i * coordinate ℚ j)
  let e : typedIntegerPairOverlapScheme ℚ d i j ≅ B :=
    openOverlapToBasicOpenIso ℚ d i j
  let w : Γ(scheme ℚ d, B) :=
    Proj.awayToSection (homogeneousGrading ℚ d)
      (coordinate ℚ i * coordinate ℚ j)
      (awayFraction ℚ d i j)
  have hmap :
      integerPairOverlapMap ℚ d i j = e.hom ≫ B.ι := by
    dsimp only [e, B]
    rw [openOverlapToBasicOpenIso_hom]
    exact (overlapHom_comp_ι ℚ d i j).symm
  have hcomp :
      (e.hom ≫ B.ι) ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme ℚ d i j).Opens) = B := by
    calc
      (e.hom ≫ B.ι) ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme ℚ d i j).Opens) =
          B.ι ''ᵁ (e.hom ''ᵁ ⊤) :=
        Scheme.Hom.comp_image e.hom B.ι ⊤
      _ = B.ι ''ᵁ ⊤ := by
        congr 1
        rw [Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso]
      _ = B := B.ι_image_top
  have hunit :
      (overlapUnit ℚ d i j).val =
        e.hom.appTop (B.topIso.inv w) := by
    dsimp only [e, B, w]
    rw [openOverlapToBasicOpenIso_hom]
    exact overlapUnit_val_eq ℚ d i j
  unfold overlapUnitAmbientPairSection
  change
    ((scheme ℚ d).presheaf.mapIso
        (eqToIso
          (integerPairOverlapMap_image_top_product d i j)).op).inv.hom
      (((integerPairOverlapMap ℚ d i j).appIso ⊤).inv.hom
        (overlapUnit ℚ d i j).val) = w
  calc
    _ = ((scheme ℚ d).presheaf.mapIso
          (eqToIso hcomp).op).inv.hom
        (((e.hom ≫ B.ι).appIso ⊤).inv.hom
          (overlapUnit ℚ d i j).val) := by
      exact appIso_inv_congr_transport hmap
        (⊤ : (typedIntegerPairOverlapScheme ℚ d i j).Opens) B
        (integerPairOverlapMap_image_top_product d i j)
        hcomp (overlapUnit ℚ d i j).val
    _ = ((scheme ℚ d).presheaf.mapIso
          (eqToIso hcomp).op).inv.hom
        (((e.hom ≫ B.ι).appIso ⊤).inv.hom
          (e.hom.appTop (B.topIso.inv w))) := by
      exact congrArg
        (fun z =>
          ((scheme ℚ d).presheaf.mapIso
            (eqToIso hcomp).op).inv.hom
            (((e.hom ≫ B.ι).appIso ⊤).inv.hom z))
        hunit
    _ = w :=
      appIso_inv_iso_comp_opens_top B e hcomp w

lemma overlapRingHomAmbientPairSection_eq_away
    (d : ℕ) (i j : Fin (d + 1))
    (a : HomogeneousLocalization.Away
      (homogeneousGrading ℚ d)
      (coordinate ℚ i * coordinate ℚ j)) :
    ((scheme ℚ d).presheaf.mapIso
        (eqToIso
          (integerPairOverlapMap_image_top_product d i j)).op).inv.hom
      (((integerPairOverlapMap ℚ d i j).appIso ⊤).inv.hom
        (overlapRingHom ℚ d i j a)) =
      Proj.awayToSection (homogeneousGrading ℚ d)
        (coordinate ℚ i * coordinate ℚ j) a := by
  let B : (scheme ℚ d).Opens :=
    Proj.basicOpen (homogeneousGrading ℚ d)
      (coordinate ℚ i * coordinate ℚ j)
  let e : typedIntegerPairOverlapScheme ℚ d i j ≅ B :=
    openOverlapToBasicOpenIso ℚ d i j
  let w : Γ(scheme ℚ d, B) :=
    Proj.awayToSection (homogeneousGrading ℚ d)
      (coordinate ℚ i * coordinate ℚ j) a
  have hmap :
      integerPairOverlapMap ℚ d i j = e.hom ≫ B.ι := by
    dsimp only [e, B]
    rw [openOverlapToBasicOpenIso_hom]
    exact (overlapHom_comp_ι ℚ d i j).symm
  have hcomp :
      (e.hom ≫ B.ι) ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme ℚ d i j).Opens) = B := by
    calc
      (e.hom ≫ B.ι) ''ᵁ
          (⊤ : (typedIntegerPairOverlapScheme ℚ d i j).Opens) =
          B.ι ''ᵁ (e.hom ''ᵁ ⊤) :=
        Scheme.Hom.comp_image e.hom B.ι ⊤
      _ = B.ι ''ᵁ ⊤ := by
        congr 1
        rw [Scheme.Hom.image_top_eq_opensRange,
          Scheme.Hom.opensRange_of_isIso]
      _ = B := B.ι_image_top
  have hsection :
      overlapRingHom ℚ d i j a =
        e.hom.appTop (B.topIso.inv w) := by
    dsimp only [e, B, w, overlapRingHom]
    rw [openOverlapToBasicOpenIso_hom]
    rfl
  change
    ((scheme ℚ d).presheaf.mapIso
        (eqToIso
          (integerPairOverlapMap_image_top_product d i j)).op).inv.hom
      (((integerPairOverlapMap ℚ d i j).appIso ⊤).inv.hom
        (overlapRingHom ℚ d i j a)) = w
  calc
    _ = ((scheme ℚ d).presheaf.mapIso
          (eqToIso hcomp).op).inv.hom
        (((e.hom ≫ B.ι).appIso ⊤).inv.hom
          (overlapRingHom ℚ d i j a)) := by
      exact appIso_inv_congr_transport hmap
        (⊤ : (typedIntegerPairOverlapScheme ℚ d i j).Opens) B
        (integerPairOverlapMap_image_top_product d i j)
        hcomp (overlapRingHom ℚ d i j a)
    _ = ((scheme ℚ d).presheaf.mapIso
          (eqToIso hcomp).op).inv.hom
        (((e.hom ≫ B.ι).appIso ⊤).inv.hom
          (e.hom.appTop (B.topIso.inv w))) := by
      exact congrArg
        (fun z =>
          ((scheme ℚ d).presheaf.mapIso
            (eqToIso hcomp).op).inv.hom
            (((e.hom ≫ B.ι).appIso ⊤).inv.hom z))
        hsection
    _ = w :=
      appIso_inv_iso_comp_opens_top B e hcomp w

lemma overlapUnit_zpow_inv_val_eq
    (d : ℕ) (m : ℤ) (i j : Fin (d + 1)) :
    (((overlapUnit ℚ d i j) ^ m).inv :
      Γ((glueData ℚ d).V (i, j), ⊤)) =
      overlapRingHom ℚ d i j
        ((((awayUnit ℚ d i j) ^ m)⁻¹).val) := by
  unfold overlapUnit
  change
    ((((Units.map (overlapRingHom ℚ d i j).toMonoidHom)
        (awayUnit ℚ d i j) ^ m)⁻¹).val) =
      ((Units.map (overlapRingHom ℚ d i j).toMonoidHom)
        (((awayUnit ℚ d i j) ^ m)⁻¹)).val
  rw [← map_zpow, ← map_inv]

lemma laurentOpen_le_pairProduct
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) :
    laurentOpen ℚ d I ≤
      Proj.basicOpen (homogeneousGrading ℚ d)
        (coordinate ℚ i.1 * coordinate ℚ j.1) := by
  rw [Proj.basicOpen_mul]
  exact le_inf
    (laurentOpen_le_standardChart ℚ d I i)
    (laurentOpen_le_standardChart ℚ d I j)

lemma inverseTransitionAmbient_eq_productAwayRestriction
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I) :
    pairUnitSectionToAmbientViaSecondChart d I i j
        (integerInverseTransitionSectionOnPair d m I i j) =
      (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_le_pairProduct d I i j)).op
        (Proj.awayToSection (homogeneousGrading ℚ d)
          (coordinate ℚ i.1 * coordinate ℚ j.1)
          ((((awayUnit ℚ d i.1 j.1) ^ m)⁻¹).val)) := by
  let U := pairPreimageLaurentOpen d I i j
  let B : (scheme ℚ d).Opens :=
    Proj.basicOpen (homogeneousGrading ℚ d)
      (coordinate ℚ i.1 * coordinate ℚ j.1)
  let a :
      HomogeneousLocalization.Away
        (homogeneousGrading ℚ d)
        (coordinate ℚ i.1 * coordinate ℚ j.1) :=
    ((((awayUnit ℚ d i.1 j.1) ^ m)⁻¹).val)
  calc
    _ = pairUnitSectionToAmbientViaFirstChart d I i j
        (integerInverseTransitionSectionOnPair d m I i j) :=
      (pairUnitSectionToAmbient_chart_independent d I i j _).symm
    _ = pairUnitSectionToAmbientDirect d I i j
        (integerInverseTransitionSectionOnPair d m I i j) :=
      pairUnitSectionToAmbientViaFirstChart_eq_direct d I i j _
    _ = (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_le_pairProduct d I i j)).op
        (((scheme ℚ d).presheaf.mapIso
          (eqToIso
            (integerPairOverlapMap_image_top_product
              d i.1 j.1)).op).inv.hom
          (((integerPairOverlapMap ℚ d i.1 j.1).appIso ⊤).inv.hom
            (((overlapUnit ℚ d i.1 j.1) ^ m).inv))) := by
      unfold pairUnitSectionToAmbientDirect
        integerInverseTransitionSectionOnPair
      exact appIso_inv_global_restriction_transport
        (integerPairOverlapMap ℚ d i.1 j.1)
        U (laurentOpen ℚ d I) B
        (pairPreimageLaurentOpen_image d I i j)
        (integerPairOverlapMap_image_top_product d i.1 j.1)
        (laurentOpen_le_pairProduct d I i j)
        (((overlapUnit ℚ d i.1 j.1) ^ m).inv)
    _ = (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_le_pairProduct d I i j)).op
        (Proj.awayToSection (homogeneousGrading ℚ d)
          (coordinate ℚ i.1 * coordinate ℚ j.1) a) := by
      apply congrArg
        ((scheme ℚ d).presheaf.map
          (homOfLE
            (laurentOpen_le_pairProduct d I i j)).op).hom
      rw [overlapUnit_zpow_inv_val_eq]
      exact overlapRingHomAmbientPairSection_eq_away
        d i.1 j.1 a

lemma cast_productInverseTransition_eq_pairChartChange
    (d : ℕ) (m : ℤ) (i j : Fin (d + 1))
    (hij : i ≠ j) :
    RingEquiv.cast
        (variableProduct_coordinatePair (k := ℚ) hij).symm
        ((((awayUnit ℚ d i j) ^ m)⁻¹).val) =
      chartChangeFraction d (coordinatePair i j)
        (coordinatePairLeft i j)
        (coordinatePairRight i j) m := by
  rw [← awayUnitOnCoordinatePair_zpow_inv_eq_chartChangeFraction
    i j hij m]
  rw [awayUnitOnCoordinatePair_eq_map_awayUnit i j hij]
  change
    RingEquiv.cast
        (variableProduct_coordinatePair (k := ℚ) hij).symm
        ((((awayUnit ℚ d i j) ^ m)⁻¹).val) =
      (((Units.map
          (RingEquiv.cast
            (variableProduct_coordinatePair
              (k := ℚ) hij).symm).toMonoidHom
          (awayUnit ℚ d i j) ^ m)⁻¹).val)
  rw [← map_zpow, ← map_inv]
  rfl

lemma degreeZeroAmbientSectionsLinearEquiv_single_chartChange
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (i j : ↥I) :
    degreeZeroAmbientSection d I
        (Finsupp.single
          (chartChangeAdmissibleExponent d I i j m) 1) =
      Proj.awayToSection (homogeneousGrading ℚ d)
        (variableProduct (k := ℚ) I)
        (chartChangeFraction d I i j m) := by
  change
    Proj.awayToSection (homogeneousGrading ℚ d)
        (variableProduct (k := ℚ) I)
        (degreeZeroFractionLinearEquiv (k := ℚ) I
          (Finsupp.single
            (chartChangeAdmissibleExponent d I i j m) 1)) =
      _
  rw [degreeZeroFractionLinearEquiv_single_chartChange]

lemma restriction_pairSingle_chartChange
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I) :
    restriction (R := ℚ) (coordinatePair_subset i j)
        (Finsupp.single
          (chartChangeAdmissibleExponent d
            (coordinatePair i.1 j.1)
            (coordinatePairLeft i.1 j.1)
            (coordinatePairRight i.1 j.1) m) 1) =
      Finsupp.single
        (chartChangeAdmissibleExponent d I i j m) 1 := by
  apply (degreeZeroFractionLinearEquiv (k := ℚ) I).injective
  rw [degreeZeroFractionLinearEquiv_restriction]
  rw [degreeZeroFractionLinearEquiv_single_chartChange,
    degreeZeroFractionLinearEquiv_single_chartChange]
  exact homogeneousAwayRestriction_pairChartChangeFraction i j m

lemma productAwayRestriction_eq_chartChangeAmbient
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (i j : ↥I) (hij : i.1 ≠ j.1) :
    (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_le_pairProduct d I i j)).op
        (Proj.awayToSection (homogeneousGrading ℚ d)
          (coordinate ℚ i.1 * coordinate ℚ j.1)
          ((((awayUnit ℚ d i.1 j.1) ^ m)⁻¹).val)) =
      degreeZeroAmbientSection d I
        (Finsupp.single
          (chartChangeAdmissibleExponent d I i j m) 1) := by
  let P := coordinatePair i.1 j.1
  let hPI : P ⊆ I := coordinatePair_subset i j
  let hvar :
      variableProduct (k := ℚ) P =
        coordinate ℚ i.1 * coordinate ℚ j.1 :=
    variableProduct_coordinatePair (k := ℚ) hij
  let B : (scheme ℚ d).Opens :=
    Proj.basicOpen (homogeneousGrading ℚ d)
      (coordinate ℚ i.1 * coordinate ℚ j.1)
  let eBP : B = laurentOpen ℚ d P :=
    congrArg
      (Proj.basicOpen (homogeneousGrading ℚ d))
      hvar.symm
  let a :
      HomogeneousLocalization.Away
        (homogeneousGrading ℚ d)
        (coordinate ℚ i.1 * coordinate ℚ j.1) :=
    ((((awayUnit ℚ d i.1 j.1) ^ m)⁻¹).val)
  let fP :
      MonomialModule (ι := Fin (d + 1)) ℚ 0 P :=
    Finsupp.single
      (chartChangeAdmissibleExponent d P
        (coordinatePairLeft i.1 j.1)
        (coordinatePairRight i.1 j.1) m) 1
  letI : Nonempty ↥P := ⟨coordinatePairLeft i.1 j.1⟩
  have hpair :
      ((scheme ℚ d).presheaf.mapIso
          (eqToIso eBP).op).inv.hom
        (Proj.awayToSection (homogeneousGrading ℚ d)
          (coordinate ℚ i.1 * coordinate ℚ j.1) a) =
      degreeZeroAmbientSection d P fP := by
    rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom]
    unfold degreeZeroAmbientSection
    calc
      _ = Proj.awayToSection (homogeneousGrading ℚ d)
          (variableProduct (k := ℚ) P)
          (RingEquiv.cast hvar.symm a) := by
        exact awayToSection_cast ℚ d
          (coordinate ℚ i.1 * coordinate ℚ j.1)
          (variableProduct (k := ℚ) P)
          hvar.symm a
      _ = Proj.awayToSection (homogeneousGrading ℚ d)
          (variableProduct (k := ℚ) P)
          (chartChangeFraction d P
            (coordinatePairLeft i.1 j.1)
            (coordinatePairRight i.1 j.1) m) := by
        rw [cast_productInverseTransition_eq_pairChartChange
          d m i.1 j.1 hij]
      _ = Proj.awayToSection (homogeneousGrading ℚ d)
          (variableProduct (k := ℚ) P)
          (degreeZeroFractionLinearEquiv (k := ℚ) P fP) := by
        exact (degreeZeroAmbientSectionsLinearEquiv_single_chartChange
          d m P
          (coordinatePairLeft i.1 j.1)
          (coordinatePairRight i.1 j.1)).symm
  have hnat :=
    presheafMapIsoSymm_restriction
      eBP rfl
      (laurentOpen_le_pairProduct d I i j)
      (laurentOpen_mono ℚ d hPI)
      (Proj.awayToSection (homogeneousGrading ℚ d)
        (coordinate ℚ i.1 * coordinate ℚ j.1) a)
  calc
    _ = (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_mono ℚ d hPI)).op
        (((scheme ℚ d).presheaf.mapIso
          (eqToIso eBP).op).inv.hom
          (Proj.awayToSection (homogeneousGrading ℚ d)
            (coordinate ℚ i.1 * coordinate ℚ j.1) a)) := by
      simpa [a] using hnat
    _ = (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_mono ℚ d hPI)).op
        (degreeZeroAmbientSection d P fP) := by
      exact congrArg
        ((scheme ℚ d).presheaf.map
          (homOfLE (laurentOpen_mono ℚ d hPI)).op).hom
        hpair
    _ = degreeZeroAmbientSection d I
        (restriction (R := ℚ) hPI fP) :=
      (degreeZeroAmbientSectionsLinearEquiv_restriction
        d hPI fP).symm
    _ = _ := by
      rw [restriction_pairSingle_chartChange d m I i j]

lemma inverseTransitionAmbient_eq_chartChange
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (i j : ↥I) (hij : i.1 ≠ j.1) :
    pairUnitSectionToAmbientViaSecondChart d I i j
        (integerInverseTransitionSectionOnPair d m I i j) =
      degreeZeroAmbientSection d I
        (Finsupp.single
          (chartChangeAdmissibleExponent d I i j m) 1) :=
  (inverseTransitionAmbient_eq_productAwayRestriction
    d m I i j).trans
    (productAwayRestriction_eq_chartChangeAmbient
      d m I i j hij)

lemma integerChartPairCompatible_of_ambientCoordinate_eq
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] (i j : ↥I)
    (x : letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I)))
    (h :
      integerChartLaurentSectionsAddEquiv d m I i x =
        integerChartLaurentSectionsAddEquiv d m I j x *
          degreeZeroAmbientSection d I
            (Finsupp.single
              (chartChangeAdmissibleExponent d I i j m) 1)) :
    IntegerChartPairCompatible d m I i j x := by
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  unfold IntegerChartPairCompatible
    integerChartDegreeZeroLaurentCoordinate
  change
    (degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
        (integerChartLaurentSectionsAddEquiv d m I i x) =
      monomialModuleChartChangeLinearEquiv I i j m
        ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
          (integerChartLaurentSectionsAddEquiv d m I j x))
  apply (degreeZeroAmbientSectionsLinearEquiv d I).injective
  calc
    _ = integerChartLaurentSectionsAddEquiv d m I i x :=
      (degreeZeroAmbientSectionsLinearEquiv d I).apply_symm_apply _
    _ = integerChartLaurentSectionsAddEquiv d m I j x *
        degreeZeroAmbientSection d I
          (Finsupp.single
            (chartChangeAdmissibleExponent d I i j m) 1) := h
    _ = degreeZeroAmbientSection d I
          (Finsupp.single
            (chartChangeAdmissibleExponent d I i j m) 1) *
        integerChartLaurentSectionsAddEquiv d m I j x := mul_comm _ _
    _ = degreeZeroAmbientSection d I
          (Finsupp.single
            (chartChangeAdmissibleExponent d I i j m) 1) *
        degreeZeroAmbientSection d I
          ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
            (integerChartLaurentSectionsAddEquiv d m I j x)) := by
      exact congrArg
        (fun z => degreeZeroAmbientSection d I
          (Finsupp.single
            (chartChangeAdmissibleExponent d I i j m) 1) * z)
        ((degreeZeroAmbientSectionsLinearEquiv d I).apply_symm_apply _).symm
    _ = _ :=
      (degreeZeroAmbientSectionsLinearEquiv_chartChange d I i j m
        ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
          (integerChartLaurentSectionsAddEquiv d m I j x))).symm

lemma integerChartPairCompatible_of_ne
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (i j : ↥I) (hij : i.1 ≠ j.1)
    (x : letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I))) :
    IntegerChartPairCompatible d m I i j x := by
  apply integerChartPairCompatible_of_ambientCoordinate_eq
  exact (integerChartAmbientCoordinate_eq_mul_transition
    d m I i j x).trans
    (congrArg
      (fun z =>
        integerChartLaurentSectionsAddEquiv d m I j x * z)
      (inverseTransitionAmbient_eq_chartChange
        d m I i j hij))

lemma integerChartLaurentSectionsLinearEquiv_eq
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I))) :
    integerChartLaurentSectionsLinearEquiv d m I i x =
      integerChartLaurentSectionsLinearEquiv d m I j x := by
  by_cases hij : i.1 = j.1
  · have hij' : i = j := Subtype.ext hij
    subst j
    rfl
  · letI : Nonempty ↥I := ⟨i⟩
    exact integerChartLaurentSectionsLinearEquiv_chart_independent
      d m I i j x
      (integerChartPairCompatible_of_ne d m I i j hij x)

/-- Laurent coordinates for every integer Serre twist are independent
of the chosen standard chart. -/
theorem integerChartCoordinatesIndependent
    (d : ℕ) (m : ℤ) :
    IntegerChartCoordinatesIndependent d m where
  coordinate_eq I i j x :=
    integerChartLaurentSectionsLinearEquiv_eq d m I i j x

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
