/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentChartChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentLinear

/-!
# Chart independence of Laurent coordinates for integer Serre twists

The geometric overlap equation for `𝒪(m)` says that the degree-zero
representatives in two standard-chart frames differ by the monomial
`X_j^m X_i⁻ᵐ`.  This file isolates the final algebraic step: that monomial
is exactly the reindexing called `monomialModuleChartChangeLinearEquiv`,
and after restoring homogeneous degree `m` the two representatives agree.
-/

open CategoryTheory AlgebraicGeometry


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

/-- The Laurent monomial `X_j^m X_i⁻ᵐ` which changes from the `j`-frame
to the `i`-frame. -/
def chartChangeLaurentMonomial
    {k : Type} [Semiring k]
    (d : ℕ) (i j : Fin (d + 1)) (m : ℤ) :
    LaurentAlgebra k (Fin (d + 1)) :=
  AddMonoidAlgebra.single
    (coordinateShift j m - coordinateShift i m) (1 : k)

/-- Forgetting admissibility turns chart change into multiplication by
`X_j^m X_i⁻ᵐ` in the full Laurent algebra. -/
lemma admissibleExponentLinearMap_chartChange
    {k : Type} [CommRing k]
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (m : ℤ)
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    admissibleExponentLinearMap (k := k) I
        (monomialModuleChartChangeLinearEquiv
          (k := k) I i j m f) =
      chartChangeLaurentMonomial (k := k) d i.1 j.1 m *
        admissibleExponentLinearMap (k := k) I f := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [chartChangeLaurentMonomial]
  | single_add a r f ha hr ih =>
      simp only [map_add, mul_add, ih]
      congr 1
      rw [monomialModuleChartChangeLinearEquiv,
        Finsupp.domLCongr_single,
        admissibleExponentLinearMap_apply,
        Finsupp.embDomain_single,
        admissibleExponentLinearMap_apply,
        Finsupp.embDomain_single,
        chartChangeLaurentMonomial,
        AddMonoidAlgebra.ofCoeff_single]
      change
        AddMonoidAlgebra.single
            (admissibleExponentChartChangeEquiv I i j m a).1 r =
          AddMonoidAlgebra.single
              (coordinateShift j.1 m - coordinateShift i.1 m) 1 *
            AddMonoidAlgebra.single a.1 r
      rw [AddMonoidAlgebra.single_mul_single]
      congr 1
      · dsimp [admissibleExponentChartChangeEquiv,
          admissibleExponentEmbedding]
        module
      · simp

/-- The degree-zero admissible exponent of the inverse Serre transition
monomial `X_j^m X_i⁻ᵐ`. -/
def chartChangeAdmissibleExponent
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (m : ℤ) :
    AdmissibleExponent (ι := Fin (d + 1)) 0 I :=
  admissibleExponentChartChangeEquiv I i j m
    ⟨0, ProjectiveExponent.totalDegree_zero, by
      simp [ProjectiveExponent.AdmissibleOn]⟩

/-- The inverse transition monomial as a degree-zero homogeneous fraction
on the Laurent open indexed by `I`. -/
def chartChangeFraction
    {k : Type} [CommRing k]
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (m : ℤ) :
    HomogeneousLocalization.Away
      (homogeneousGrading k d)
      (variableProduct (k := k) I) :=
  degreeZeroFraction (k := k) I
    (chartChangeAdmissibleExponent d I i j m)

@[simp]
lemma homogeneousAwayToLaurent_chartChangeFraction
    {k : Type} [CommRing k]
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (m : ℤ) :
    homogeneousAwayToLaurent (k := k) (d := d) I
        (chartChangeFraction (k := k) d I i j m) =
      chartChangeLaurentMonomial (k := k) d i.1 j.1 m := by
  rw [chartChangeFraction,
    homogeneousAwayToLaurent_degreeZeroFraction]
  congr 1
  dsimp [chartChangeAdmissibleExponent,
    admissibleExponentChartChangeEquiv,
    chartChangeLaurentMonomial]
  simp only [zero_add]

/-- Under the homogeneous-fraction model, chart change is multiplication
by the inverse Serre transition fraction. -/
lemma degreeZeroFractionLinearEquiv_chartChange
    {k : Type} [CommRing k]
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (m : ℤ)
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    degreeZeroFractionLinearEquiv (k := k) I
        (monomialModuleChartChangeLinearEquiv
          (k := k) I i j m f) =
      chartChangeFraction (k := k) d I i j m *
        degreeZeroFractionLinearEquiv (k := k) I f := by
  apply homogeneousAwayToLaurent_injective I
  change
    homogeneousAwayToLaurent (k := k) (d := d) I
        (degreeZeroFractionLinearMap (k := k) I
          (monomialModuleChartChangeLinearEquiv
            (k := k) I i j m f)) =
      homogeneousAwayToLaurent (k := k) (d := d) I
        (chartChangeFraction (k := k) d I i j m *
          degreeZeroFractionLinearMap (k := k) I f)
  rw [map_mul, homogeneousAwayToLaurent_chartChangeFraction]
  rw [show
      homogeneousAwayToLaurent (k := k) (d := d) I
          (degreeZeroFractionLinearMap (k := k) I
            (monomialModuleChartChangeLinearEquiv
              (k := k) I i j m f)) =
        AddMonoidAlgebra.ofCoeff
          (Finsupp.embDomain (admissibleExponentEmbedding I)
            (monomialModuleChartChangeLinearEquiv
              (k := k) I i j m f)) from
      homogeneousAwayToLaurent_comp_fractionLinearMap
        I (monomialModuleChartChangeLinearEquiv
          (k := k) I i j m f)]
  rw [show
      homogeneousAwayToLaurent (k := k) (d := d) I
          (degreeZeroFractionLinearMap (k := k) I f) =
        AddMonoidAlgebra.ofCoeff
          (Finsupp.embDomain (admissibleExponentEmbedding I) f) from
      homogeneousAwayToLaurent_comp_fractionLinearMap I f]
  simpa only [admissibleExponentLinearMap_apply] using
    admissibleExponentLinearMap_chartChange d I i j m f

/-- The basis monomial of the inverse transition maps to the named
homogeneous transition fraction. -/
lemma degreeZeroFractionLinearEquiv_single_chartChange
    {k : Type} [CommRing k]
    (d : ℕ) (I : Finset (Fin (d + 1)))
    (i j : ↥I) (m : ℤ) :
    degreeZeroFractionLinearEquiv (k := k) I
        (Finsupp.single
          (chartChangeAdmissibleExponent d I i j m) (1 : k)) =
      chartChangeFraction (k := k) d I i j m := by
  change
    degreeZeroFractionLinearMap (k := k) I
        (Finsupp.single
          (chartChangeAdmissibleExponent d I i j m) (1 : k)) =
      chartChangeFraction (k := k) d I i j m
  rw [degreeZeroFractionLinearMap_single, one_smul]
  rfl

/-- On regular functions of a Laurent open, chart change is multiplication
by the ambient inverse-transition section. -/
lemma degreeZeroAmbientSectionsLinearEquiv_chartChange
    (d : ℕ) (I : Finset (Fin (d + 1)))
    [Nonempty ↥I] (i j : ↥I) (m : ℤ)
    (f : MonomialModule (ι := Fin (d + 1)) ℚ 0 I) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
      Geometric.sectionsModule
        (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
        (laurentOpen ℚ d I)
    (degreeZeroAmbientSectionsLinearEquiv d I).toFun
        (monomialModuleChartChangeLinearEquiv I i j m f) =
      (degreeZeroAmbientSectionsLinearEquiv d I).toFun
          (Finsupp.single
            (chartChangeAdmissibleExponent d I i j m) 1) *
      (degreeZeroAmbientSectionsLinearEquiv d I).toFun f := by
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  change
    Proj.awayToSection
        (homogeneousGrading ℚ d)
        (variableProduct (k := ℚ) I)
        (degreeZeroFractionLinearEquiv (k := ℚ) I
          (monomialModuleChartChangeLinearEquiv I i j m f)) =
      Proj.awayToSection
          (homogeneousGrading ℚ d)
          (variableProduct (k := ℚ) I)
          (degreeZeroFractionLinearEquiv (k := ℚ) I
            (Finsupp.single
              (chartChangeAdmissibleExponent d I i j m) 1)) *
        Proj.awayToSection
          (homogeneousGrading ℚ d)
          (variableProduct (k := ℚ) I)
          (degreeZeroFractionLinearEquiv (k := ℚ) I f)
  rw [degreeZeroFractionLinearEquiv_chartChange,
    degreeZeroFractionLinearEquiv_single_chartChange,
    map_mul]

/-- The chart-change identity with the coefficient ring fixed explicitly.
This small wrapper is useful in later dependent section expressions, where
leaving the coefficient parameter implicit can make elaboration choose a
coordinate type instead. -/
lemma monomialModuleShift_chartChange_explicit
    {k ι : Type} [Semiring k] [Fintype ι] [LinearOrder ι]
    (I : Finset ι) (i j : ↥I) (m : ℤ)
    (g : MonomialModule (ι := ι) k 0 I) :
    monomialModuleShiftLinearEquiv (k := k) I i m
        (monomialModuleChartChangeLinearEquiv
          (k := k) I i j m g) =
      monomialModuleShiftLinearEquiv (k := k) I j m g := by
  have hmaps :
      (monomialModuleShiftLinearEquiv
          (k := k) I i m).toLinearMap.comp
          (monomialModuleChartChangeLinearEquiv
            (k := k) I i j m).toLinearMap =
        (monomialModuleShiftLinearEquiv
          (k := k) I j m).toLinearMap := by
    apply Finsupp.lhom_ext
    intro a r
    rw [LinearMap.comp_apply]
    change
      Finsupp.domLCongr (admissibleExponentShiftEquiv I i m)
          (Finsupp.domLCongr
            (admissibleExponentChartChangeEquiv I i j m)
            (Finsupp.single a r)) =
        Finsupp.domLCongr (admissibleExponentShiftEquiv I j m)
          (Finsupp.single a r)
    rw [Finsupp.domLCongr_single, Finsupp.domLCongr_single,
      Finsupp.domLCongr_single, admissibleExponentShift_chartChange]
  exact DFunLike.congr_fun hmaps g

/-- At degree zero, changing the chart before restoring degree is
equivalent to changing the frame of the homogeneous representative. -/
lemma monomialModuleShift_eq_iff_chartChange
    {k ι : Type} [Semiring k] [Fintype ι] [LinearOrder ι]
    (I : Finset ι) (i j : ↥I) (m : ℤ)
    (f g : MonomialModule (ι := ι) k 0 I) :
    monomialModuleShiftLinearEquiv (k := k) I i m f =
        monomialModuleShiftLinearEquiv (k := k) I j m g ↔
      f = monomialModuleChartChangeLinearEquiv
        (k := k) I i j m g := by
  constructor
  · intro h
    apply (monomialModuleShiftLinearEquiv
      (k := k) I i m).injective
    exact h.trans
      (monomialModuleShift_chartChange_explicit I i j m g).symm
  · rintro rfl
    exact monomialModuleShift_chartChange_explicit I i j m g

/-- The degree-zero Laurent coordinate of an integer-twist section in a
chosen standard-chart frame. -/
def integerChartDegreeZeroLaurentCoordinate
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I)) →ₗ[ℚ]
      MonomialModule (ι := Fin (d + 1)) ℚ 0 I := by
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Nonempty ↥I := ⟨j⟩
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  letI : Module ℚ Γ(OInt ℚ d m, laurentOpen ℚ d I) := by
    change Module ℚ
      ((Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I)))
    infer_instance
  exact
    (degreeZeroAmbientSectionsLinearEquiv d I).symm.toLinearMap.comp
      (addEquivToRatLinearEquiv
        (integerChartLaurentSectionsAddEquiv d m I j)).toLinearMap

/-- Pair-overlap compatibility in Laurent coordinates: the two
degree-zero chart representatives differ by the inverse Serre transition
monomial `X_j^m X_i⁻ᵐ`. -/
def IntegerChartPairCompatible
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I))) : Prop :=
  integerChartDegreeZeroLaurentCoordinate d m I i x =
    monomialModuleChartChangeLinearEquiv I i j m
      (integerChartDegreeZeroLaurentCoordinate d m I j x)

/-- The precise algebraic endpoint of the geometric pair-overlap
calculation: inverse-transition compatibility is equivalent to
chart-independent degree-`m` Laurent coordinates. -/
lemma integerChartPairCompatible_iff_laurentCoordinates_eq
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I))) :
    IntegerChartPairCompatible d m I i j x ↔
      integerChartLaurentSectionsLinearEquiv d m I i x =
        integerChartLaurentSectionsLinearEquiv d m I j x := by
  letI : Nonempty ↥I := ⟨i⟩
  dsimp [IntegerChartPairCompatible,
    integerChartDegreeZeroLaurentCoordinate,
    integerChartLaurentSectionsLinearEquiv]
  exact
    (monomialModuleShift_eq_iff_chartChange I i j m
      ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
        (integerChartLaurentSectionsAddEquiv d m I i x))
      ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
        (integerChartLaurentSectionsAddEquiv d m I j x))).symm

/-- A convenient forward form used after proving the geometric overlap
equation. -/
lemma integerChartLaurentSectionsLinearEquiv_chart_independent
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I)))
    (h : IntegerChartPairCompatible d m I i j x) :
    integerChartLaurentSectionsLinearEquiv d m I i x =
      integerChartLaurentSectionsLinearEquiv d m I j x :=
  (integerChartPairCompatible_iff_laurentCoordinates_eq
    d m I i j x).mp h

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
