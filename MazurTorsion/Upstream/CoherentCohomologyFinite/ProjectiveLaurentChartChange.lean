/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentRestriction

open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

/--
Change the degree-zero Laurent exponent from the frame at `j` to the
frame at `i`.  Both coordinates occur in the open, so admissibility away
from the open is unchanged.
-/
def admissibleExponentChartChangeEquiv
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (i j : ↥I) (m : ℤ) :
    AdmissibleExponent (ι := ι) 0 I ≃
      AdmissibleExponent (ι := ι) 0 I where
  toFun a :=
    ⟨a.1 + coordinateShift j.1 m - coordinateShift i.1 m,
      by
        rw [ProjectiveExponent.totalDegree_sub,
          ProjectiveExponent.totalDegree_add,
          a.2.1, coordinateShift_totalDegree,
          coordinateShift_totalDegree]
        simp,
      by
        rw [ProjectiveExponent.admissibleOn_iff_nonnegative_outside]
        intro x hx
        have hxi : x ≠ i.1 := fun h => hx (h ▸ i.2)
        have hxj : x ≠ j.1 := fun h => hx (h ▸ j.2)
        have hax :=
          (ProjectiveExponent.admissibleOn_iff_nonnegative_outside
            a.1 I).mp a.2.2 x hx
        simpa [coordinateShift, hxi, hxj] using hax⟩
  invFun b :=
    ⟨b.1 + coordinateShift i.1 m - coordinateShift j.1 m,
      by
        rw [ProjectiveExponent.totalDegree_sub,
          ProjectiveExponent.totalDegree_add,
          b.2.1, coordinateShift_totalDegree,
          coordinateShift_totalDegree]
        simp,
      by
        rw [ProjectiveExponent.admissibleOn_iff_nonnegative_outside]
        intro x hx
        have hxi : x ≠ i.1 := fun h => hx (h ▸ i.2)
        have hxj : x ≠ j.1 := fun h => hx (h ▸ j.2)
        have hbx :=
          (ProjectiveExponent.admissibleOn_iff_nonnegative_outside
            b.1 I).mp b.2.2 x hx
        simpa [coordinateShift, hxi, hxj] using hbx⟩
  left_inv a := by
    apply Subtype.ext
    module
  right_inv b := by
    apply Subtype.ext
    module

/-- Reindex degree-zero Laurent monomials under a change of chart frame. -/
def monomialModuleChartChangeLinearEquiv
    {k ι : Type} [Semiring k] [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (i j : ↥I) (m : ℤ) :
    MonomialModule (ι := ι) k 0 I ≃ₗ[k]
      MonomialModule (ι := ι) k 0 I :=
  Finsupp.domLCongr (admissibleExponentChartChangeEquiv I i j m)

lemma admissibleExponentShift_chartChange
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (i j : ↥I) (m : ℤ)
    (a : AdmissibleExponent (ι := ι) 0 I) :
    admissibleExponentShiftEquiv I i m
        (admissibleExponentChartChangeEquiv I i j m a) =
      admissibleExponentShiftEquiv I j m a := by
  apply Subtype.ext
  dsimp [admissibleExponentChartChangeEquiv,
    admissibleExponentShiftEquiv]
  module

/--
Changing the degree-zero chart frame and then restoring homogeneous degree
is independent of the frame.
-/
lemma monomialModuleShift_chartChange
    {k ι : Type} [Semiring k] [Fintype ι] [LinearOrder ι]
    (I : Finset ι) (i j : ↥I) (m : ℤ)
    (f : MonomialModule (ι := ι) k 0 I) :
    monomialModuleShiftLinearEquiv (k := k) I i m
        (monomialModuleChartChangeLinearEquiv (k := k) I i j m f) =
      monomialModuleShiftLinearEquiv (k := k) I j m f := by
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
  exact DFunLike.congr_fun hmaps f

lemma admissibleExponentChartChange_exponentInclusion
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {I J : Finset ι} (hIJ : I ⊆ J)
    (i j : ↥I) (m : ℤ)
    (a : AdmissibleExponent (ι := ι) 0 I) :
    admissibleExponentChartChangeEquiv J
        ⟨i.1, hIJ i.2⟩ ⟨j.1, hIJ j.2⟩ m
        (exponentInclusion hIJ a) =
      exponentInclusion hIJ
        (admissibleExponentChartChangeEquiv I i j m a) := by
  rfl

/-- Frame change commutes with restriction to a smaller intersection. -/
lemma monomialModuleChartChange_restriction
    {k ι : Type} [CommSemiring k] [Fintype ι] [LinearOrder ι]
    {I J : Finset ι} (hIJ : I ⊆ J)
    (i j : ↥I) (m : ℤ)
    (f : MonomialModule (ι := ι) k 0 I) :
    monomialModuleChartChangeLinearEquiv (k := k) J
        ⟨i.1, hIJ i.2⟩ ⟨j.1, hIJ j.2⟩ m
        (restriction (R := k) hIJ f) =
      restriction (R := k) hIJ
        (monomialModuleChartChangeLinearEquiv (k := k) I i j m f) := by
  have hmaps :
      (monomialModuleChartChangeLinearEquiv (k := k) J
        ⟨i.1, hIJ i.2⟩ ⟨j.1, hIJ j.2⟩ m).toLinearMap.comp
          (restriction (R := k) (d := 0) hIJ) =
        (restriction (R := k) (d := 0) hIJ).comp
          (monomialModuleChartChangeLinearEquiv
            (k := k) I i j m).toLinearMap := by
    apply Finsupp.lhom_ext
    intro a r
    rw [LinearMap.comp_apply, LinearMap.comp_apply, restriction_single]
    change
      Finsupp.domLCongr
          (admissibleExponentChartChangeEquiv J
            ⟨i.1, hIJ i.2⟩ ⟨j.1, hIJ j.2⟩ m)
          (Finsupp.single (exponentInclusion hIJ a) r) =
        restriction (R := k) hIJ
          (Finsupp.domLCongr
            (admissibleExponentChartChangeEquiv I i j m)
            (Finsupp.single a r))
    rw [Finsupp.domLCongr_single, Finsupp.domLCongr_single,
      restriction_single,
      admissibleExponentChartChange_exponentInclusion]
  exact DFunLike.congr_fun hmaps f

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
