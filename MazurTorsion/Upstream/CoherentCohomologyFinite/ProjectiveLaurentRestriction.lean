/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentSections

open CategoryTheory AlgebraicGeometry
open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

lemma variableProduct_mul_complement
    {k : Type} [CommRing k] {d : ℕ}
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    variableProduct (k := k) I *
        variableProduct (k := k) (J \ I) =
      variableProduct (k := k) J := by
  classical
  simpa [variableProduct, mul_comm] using
    Finset.prod_sdiff hIJ
      (f := fun i : Fin (d + 1) =>
        (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) k))

def homogeneousAwayRestriction
    {k : Type} [CommRing k] {d : ℕ}
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    HomogeneousLocalization.Away
        (homogeneousGrading k d) (variableProduct (k := k) I) →+*
      HomogeneousLocalization.Away
        (homogeneousGrading k d) (variableProduct (k := k) J) :=
  HomogeneousLocalization.awayMap
    (homogeneousGrading k d)
    (variableProduct_mem_degreeCard (J \ I))
    (variableProduct_mul_complement hIJ).symm

def localizationAwayRestriction
    {k : Type} [CommRing k] {d : ℕ}
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    Localization.Away (variableProduct (k := k) I) →+*
      Localization.Away (variableProduct (k := k) J) :=
  Localization.awayLift
    (algebraMap
      (MvPolynomial (Fin (d + 1)) k)
      (Localization.Away (variableProduct (k := k) J)))
    (variableProduct (k := k) I)
    (isUnit_of_dvd_unit
      (map_dvd _
        ⟨variableProduct (k := k) (J \ I),
          (variableProduct_mul_complement hIJ).symm⟩)
      (IsLocalization.Away.algebraMap_isUnit
        (variableProduct (k := k) J)))

lemma homogeneousAwayRestriction_val
    {k : Type} [CommRing k] {d : ℕ}
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J)
    (x : HomogeneousLocalization.Away
      (homogeneousGrading k d) (variableProduct (k := k) I)) :
    (homogeneousAwayRestriction (k := k) hIJ x).val =
      localizationAwayRestriction hIJ x.val := by
  exact HomogeneousLocalization.val_awayMap _ _ _ _

lemma localizationToLaurent_restriction
    {k : Type} [CommRing k] {d : ℕ}
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    (localizationToLaurent (k := k) J).comp
        (localizationAwayRestriction hIJ) =
      localizationToLaurent (k := k) I := by
  apply IsLocalization.ringHom_ext
    (R := MvPolynomial (Fin (d + 1)) k)
    (S := Localization.Away (variableProduct (k := k) I))
    (Submonoid.powers (variableProduct (k := k) I))
  apply DFunLike.ext _ _
  intro p
  simp only [RingHom.coe_comp, Function.comp_apply,
    localizationToLaurent_algebraMap]
  change
    localizationToLaurent (k := k) J
        (localizationAwayRestriction hIJ
          (algebraMap
            (MvPolynomial (Fin (d + 1)) k)
            (Localization.Away
              (variableProduct (k := k) I)) p)) =
      polynomialToLaurent p
  rw [show
      localizationAwayRestriction hIJ
          (algebraMap
            (MvPolynomial (Fin (d + 1)) k)
            (Localization.Away
              (variableProduct (k := k) I)) p) =
        algebraMap
          (MvPolynomial (Fin (d + 1)) k)
          (Localization.Away
            (variableProduct (k := k) J)) p by
    exact IsLocalization.lift_eq _ _]
  exact localizationToLaurent_algebraMap J p

lemma homogeneousAwayToLaurent_restriction
    {k : Type} [CommRing k] {d : ℕ}
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J)
    (x : HomogeneousLocalization.Away
      (homogeneousGrading k d) (variableProduct (k := k) I)) :
    homogeneousAwayToLaurent (k := k) (d := d) J
        (homogeneousAwayRestriction (k := k) hIJ x) =
      homogeneousAwayToLaurent (k := k) (d := d) I x := by
  change localizationToLaurent (k := k) J
      (homogeneousAwayRestriction (k := k) hIJ x).val =
    localizationToLaurent (k := k) I x.val
  rw [homogeneousAwayRestriction_val]
  change
    ((localizationToLaurent (k := k) J).comp
      (localizationAwayRestriction hIJ)) x.val =
      localizationToLaurent (k := k) I x.val
  rw [localizationToLaurent_restriction]

lemma admissibleExponentLinearMap_restriction
    {k : Type} [CommRing k] {d : ℕ}
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J)
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    admissibleExponentLinearMap (k := k) J
        (restriction (R := k) hIJ f) =
      admissibleExponentLinearMap (k := k) I f := by
  have hmaps :
      (admissibleExponentLinearMap (k := k) J).comp
          (restriction (R := k) hIJ) =
        admissibleExponentLinearMap (k := k) I := by
    apply Finsupp.lhom_ext
    intro a r
    rw [LinearMap.comp_apply, restriction_single]
    simp only [admissibleExponentLinearMap_apply,
      Finsupp.embDomain_single]
    rfl
  exact DFunLike.congr_fun hmaps f

lemma degreeZeroFractionLinearEquiv_restriction
    {k : Type} [CommRing k]
    {d : ℕ} {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J)
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    degreeZeroFractionLinearEquiv (k := k) J
        (restriction (R := k) hIJ f) =
      homogeneousAwayRestriction (k := k) hIJ
        (degreeZeroFractionLinearEquiv (k := k) I f) := by
  apply homogeneousAwayToLaurent_injective J
  rw [homogeneousAwayToLaurent_restriction]
  change
    homogeneousAwayToLaurent (k := k) (d := d) J
        (degreeZeroFractionLinearMap (k := k) J
          (restriction (R := k) hIJ f)) =
      homogeneousAwayToLaurent (k := k) (d := d) I
        (degreeZeroFractionLinearMap (k := k) I f)
  change
    homogeneousAwayToLaurentLinearMap (k := k) (d := d) J
        (degreeZeroFractionLinearMap (k := k) J
          (restriction (R := k) hIJ f)) =
      homogeneousAwayToLaurentLinearMap (k := k) (d := d) I
        (degreeZeroFractionLinearMap (k := k) I f)
  rw [homogeneousAwayToLaurent_comp_fractionLinearMap,
    homogeneousAwayToLaurent_comp_fractionLinearMap,
    ← admissibleExponentLinearMap_apply,
    ← admissibleExponentLinearMap_apply,
    admissibleExponentLinearMap_restriction]

lemma admissibleExponentShiftEquiv_exponentInclusion
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {I J : Finset ι} (hIJ : I ⊆ J)
    (j : ↥I) (m : ℤ)
    (a : AdmissibleExponent (ι := ι) 0 I) :
    admissibleExponentShiftEquiv J ⟨j.1, hIJ j.2⟩ m
        (exponentInclusion hIJ a) =
      exponentInclusion hIJ
        (admissibleExponentShiftEquiv I j m a) := by
  rfl

lemma monomialModuleShiftLinearEquiv_restriction
    {k ι : Type} [CommSemiring k] [Fintype ι] [LinearOrder ι]
    {I J : Finset ι} (hIJ : I ⊆ J)
    (j : ↥I) (m : ℤ)
    (f : MonomialModule (ι := ι) k 0 I) :
    monomialModuleShiftLinearEquiv J ⟨j.1, hIJ j.2⟩ m
        (restriction (R := k) hIJ f) =
      restriction (R := k) hIJ
        (monomialModuleShiftLinearEquiv I j m f) := by
  have hmaps :
      (monomialModuleShiftLinearEquiv J
          ⟨j.1, hIJ j.2⟩ m : _ ≃ₗ[k] _).toLinearMap.comp
          (restriction (R := k) (d := 0) hIJ) =
        (restriction (R := k) (d := m) hIJ).comp
          (monomialModuleShiftLinearEquiv I j m).toLinearMap := by
    apply Finsupp.lhom_ext
    intro a r
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      restriction_single]
    change
      Finsupp.domLCongr
          (admissibleExponentShiftEquiv J
            ⟨j.1, hIJ j.2⟩ m)
          (Finsupp.single (exponentInclusion hIJ a) r) =
        restriction (R := k) hIJ
          (Finsupp.domLCongr
            (admissibleExponentShiftEquiv I j m)
            (Finsupp.single a r))
    rw [Finsupp.domLCongr_single,
      Finsupp.domLCongr_single, restriction_single]
    rw [admissibleExponentShiftEquiv_exponentInclusion]
  exact DFunLike.congr_fun hmaps f

lemma homogeneousAwayRestriction_degreeZeroFraction
    {k : Type} [CommRing k]
    {d : ℕ} {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J)
    (a : AdmissibleExponent (ι := Fin (d + 1)) 0 I) :
    homogeneousAwayRestriction (k := k) hIJ
        (degreeZeroFraction (k := k) I a) =
      degreeZeroFraction (k := k) J
        (exponentInclusion hIJ a) := by
  apply homogeneousAwayToLaurent_injective J
  rw [homogeneousAwayToLaurent_degreeZeroFraction]
  change localizationToLaurent (k := k) J
      (homogeneousAwayRestriction (k := k) hIJ
        (degreeZeroFraction (k := k) I a)).val = _
  rw [homogeneousAwayRestriction_val]
  change
    ((localizationToLaurent (k := k) J).comp
      (localizationAwayRestriction hIJ))
        (degreeZeroFraction (k := k) I a).val = _
  rw [localizationToLaurent_restriction]
  exact homogeneousAwayToLaurent_degreeZeroFraction I a

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
