/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechComplex
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechComplex
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentLinear

/-!
# The standard-cover Čech complex of an integer Serre twist

On every nonempty intersection in the standard affine cover of projective
space, an integer Serre twist has a Laurent-monomial coordinate model.  This
file packages the normalized Čech complex in those coordinates and identifies
it with the explicit Laurent Čech complex.

The geometric input is isolated in
`standardCoverOIntSimplexSectionsLinearEquiv`; the rest of the construction is
the generic finite-subset Čech construction and Laurent restriction algebra.
-/

open CategoryTheory AlgebraicGeometry


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

/-- A canonical chart in a nonempty simplex of the standard projective cover. -/
def standardCoverSimplexChosenVertex
    {d q : ℕ} (I : Simplex (ι := Fin (d + 1)) q) : ↥I.1 := by
  have hcard : 0 < I.1.card := by
    rw [I.2]
    omega
  let hI : I.1.Nonempty := Finset.card_pos.mp hcard
  exact ⟨I.1.min' hI, Finset.min'_mem I.1 hI⟩

/-- Sections of `O(m)` on a standard-cover simplex, expressed in Laurent
coordinates using the canonical chart of that simplex. -/
def standardCoverOIntSimplexSectionsLinearEquiv
    (d : ℕ) (m : ℤ) {q : ℕ}
    (I : Simplex (ι := Fin (d + 1)) q) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I.1)) ≃ₗ[ℚ]
      MonomialModule (ι := Fin (d + 1)) ℚ m I.1 :=
  integerChartLaurentSectionsLinearEquiv
    d m I.1 (standardCoverSimplexChosenVertex I)

/-- Functoriality of Laurent restriction, in the pointwise form required by
the generic finite-subset Čech construction. -/
lemma standardCoverLaurentRestriction_comp
    (d : ℕ) (m : ℤ)
    {I J K : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : MonomialModule (ι := Fin (d + 1)) ℚ m I) :
    restriction (R := ℚ) hJK (restriction (R := ℚ) hIJ x) =
      restriction (R := ℚ) (hIJ.trans hJK) x := by
  exact LinearMap.congr_fun
    (restriction_comp (R := ℚ) (d := m) hIJ hJK) x

/-- The normalized standard-cover Čech complex of `O(m)` on `P^d_ℚ`, in the
Laurent coordinates supplied by the local trivializations. -/
def standardCoverOIntCechComplex
    (d : ℕ) (m : ℤ) :
    CochainComplex (ModuleCat ℚ) ℕ :=
  finiteSubsetCechComplex
    (fun I : Finset (Fin (d + 1)) =>
      MonomialModule (ι := Fin (d + 1)) ℚ m I)
    (fun {_ _} hIJ => restriction (R := ℚ) hIJ)
    (standardCoverLaurentRestriction_comp d m)

/-- The dependent direct sum presentation of Laurent cochains is linearly
equivalent to the sigma-indexed `Finsupp` presentation. -/
def finiteSubsetLaurentCochainLinearEquiv
    (d q : ℕ) (m : ℤ) :
    FiniteSubsetCochain
        (fun I : Finset (Fin (d + 1)) =>
          MonomialModule (ι := Fin (d + 1)) ℚ m I) q ≃ₗ[ℚ]
      Cochain (ι := Fin (d + 1)) ℚ m q :=
  (sigmaFinsuppLequivDFinsupp ℚ).symm

@[simp]
lemma finiteSubsetLaurentCochainLinearEquiv_single
    (d q : ℕ) (m : ℤ)
    (I : Simplex (ι := Fin (d + 1)) q)
    (a : AdmissibleExponent (ι := Fin (d + 1)) m I.1)
    (r : ℚ) :
    finiteSubsetLaurentCochainLinearEquiv d q m
        (DFinsupp.single I (Finsupp.single a r)) =
      Finsupp.single ⟨I, a⟩ r := by
  apply (sigmaFinsuppLequivDFinsupp ℚ).injective
  simp [finiteSubsetLaurentCochainLinearEquiv]

lemma finiteSubsetLaurentCochainLinearEquiv_differential
    (d q : ℕ) (m : ℤ) :
    (finiteSubsetLaurentCochainLinearEquiv d (q + 1) m).toLinearMap.comp
        (finiteSubsetDifferential
          (fun I : Finset (Fin (d + 1)) =>
            MonomialModule (ι := Fin (d + 1)) ℚ m I)
          (fun {_ _} hIJ => restriction (R := ℚ) hIJ) q) =
      (differential (ι := Fin (d + 1)) (R := ℚ) m q).comp
        (finiteSubsetLaurentCochainLinearEquiv d q m).toLinearMap := by
  apply DFinsupp.lhom_ext
  intro I x
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x y hx hy =>
      simp only [DFinsupp.single_add, map_add, hx, hy]
  | single a r =>
      have hsource :
          finiteSubsetLaurentCochainLinearEquiv d q m
              (DFinsupp.single I (Finsupp.single a r)) =
            Finsupp.single ⟨I, a⟩ r :=
        finiteSubsetLaurentCochainLinearEquiv_single d q m I a r
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      apply Eq.trans
        (b := differential (ι := Fin (d + 1)) (R := ℚ) m q
          (Finsupp.single ⟨I, a⟩ r))
      · rw [
          differential_single, basisCoboundary,
          Finset.smul_sum,
          finiteSubsetDifferential_component,
          finiteSubsetComponentDifferential,
          LinearMap.sum_apply, map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [LinearMap.smul_apply, LinearMap.comp_apply,
          DFinsupp.lsingle_apply, restriction_single,
          map_smul]
        have htarget :
            finiteSubsetLaurentCochainLinearEquiv d (q + 1) m
                (DFinsupp.single (I.insert j.1 j.2)
                  (Finsupp.single
                    (exponentInclusion (I.subset_insert j.1 j.2) a) r)) =
              Finsupp.single
                ⟨I.insert j.1 j.2,
                  exponentInclusion (I.subset_insert j.1 j.2) a⟩ r :=
          finiteSubsetLaurentCochainLinearEquiv_single
            d (q + 1) m _ _ r
        calc
          _ = insertionSign (R := ℚ) I.1 j.1 •
              Finsupp.single
                ⟨I.insert j.1 j.2,
                  exponentInclusion (I.subset_insert j.1 j.2) a⟩ r :=
            congrArg
              (fun z => insertionSign (R := ℚ) I.1 j.1 • z)
              htarget
          _ = _ := by
            rw [Finsupp.smul_single', Finsupp.smul_single']
            congr 1
            exact mul_comm _ _
      · exact congrArg
          (differential (ι := Fin (d + 1)) (R := ℚ) m q)
          hsource.symm

/-- The Laurent-coordinate standard-cover complex is the explicit Laurent
Čech complex used in the cohomology computation. -/
def standardCoverOIntCechComplexIsoLaurent
    (d : ℕ) (m : ℤ) :
    standardCoverOIntCechComplex d m ≅
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech.laurentCechComplex
        (ι := Fin (d + 1)) (R := ℚ) m :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (finiteSubsetLaurentCochainLinearEquiv d q m).toModuleIso)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      simp only [standardCoverOIntCechComplex,
        finiteSubsetCechComplex, CochainComplex.of_d,
        MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech.laurentCechComplex_d]
      apply ModuleCat.hom_ext
      exact
        (finiteSubsetLaurentCochainLinearEquiv_differential d i m).symm)

end

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
