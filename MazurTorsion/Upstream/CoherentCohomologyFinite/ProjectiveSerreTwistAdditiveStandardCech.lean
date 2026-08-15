/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechComplex
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechAdditiveVanishing
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentRestriction

/-!
# The additive Laurent model of the standard projective Čech complex

Over an arbitrary commutative coefficient ring, the geometric
trivializations of an integer Serre twist are naturally available as
additive equivalences.  This file therefore develops the algebraic
standard-cover complex in the category of canonical `ℤ`-modules.

Its restriction maps are the underlying additive maps of Laurent
localization.  The integer alternating signs agree with the corresponding
coefficient-ring signs, so the resulting complex is isomorphic to the
additive Laurent Čech complex.
-/

open CategoryTheory


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι k : Type*} [Fintype ι] [LinearOrder ι]

/-- Integer Čech signs act as the corresponding signs in any commutative
coefficient ring. -/
lemma insertionSign_int_smul_eq_ring
    [CommRing k]
    {M : Type*} [AddCommGroup M] [Module k M]
    (I : Finset ι) (j : ι) (x : M) :
    insertionSign (R := ℤ) I j • x =
      insertionSign (R := k) I j • x := by
  rw [← Int.cast_smul_eq_zsmul k]
  congr 1
  simp [insertionSign]

/-- Laurent restriction regarded only as a `ℤ`-linear map. -/
noncomputable def additiveRestriction
    [CommRing k] {d : ℤ}
    {I J : Finset ι} (hIJ : I ⊆ J) :
    MonomialModule (ι := ι) k d I →ₗ[ℤ]
      MonomialModule (ι := ι) k d J :=
  (restriction (R := k) hIJ).toAddMonoidHom.toIntLinearMap

@[simp]
lemma additiveRestriction_apply
    [CommRing k] {d : ℤ}
    {I J : Finset ι} (hIJ : I ⊆ J)
    (x : MonomialModule (ι := ι) k d I) :
    additiveRestriction (k := k) (d := d) hIJ x =
      restriction (R := k) hIJ x :=
  rfl

/-- Functoriality of additive Laurent restriction. -/
lemma additiveRestriction_comp
    [CommRing k] {d : ℤ}
    {I J K : Finset ι}
    (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : MonomialModule (ι := ι) k d I) :
    additiveRestriction (k := k) (d := d) hJK
        (additiveRestriction (k := k) (d := d) hIJ x) =
      additiveRestriction (k := k) (d := d)
        (hIJ.trans hJK) x :=
  LinearMap.congr_fun
    (restriction_comp (R := k) (d := d) hIJ hJK) x

/--
The finite-subset Laurent-coordinate complex with only its additive
structure retained.
-/
noncomputable def additiveStandardLaurentCechComplex
    [CommRing k] (d : ℤ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  finiteSubsetCechComplex
    (R := ℤ)
    (fun I : Finset ι =>
      MonomialModule (ι := ι) k d I)
    (fun {_ _} hIJ =>
      additiveRestriction (k := k) (d := d) hIJ)
    (additiveRestriction_comp (k := k) (d := d))

/--
The dependent finite-subset cochain presentation is additively
equivalent to the sigma-indexed Laurent cochain presentation.
-/
noncomputable def additiveFiniteSubsetLaurentCochainLinearEquiv
    [CommRing k] (d : ℤ) (q : ℕ) :
    FiniteSubsetCochain
        (fun I : Finset ι =>
          MonomialModule (ι := ι) k d I) q ≃ₗ[ℤ]
      Cochain (ι := ι) k d q :=
  ((sigmaFinsuppLequivDFinsupp k).symm :
    FiniteSubsetCochain
        (fun I : Finset ι =>
          MonomialModule (ι := ι) k d I) q ≃ₗ[k]
      Cochain (ι := ι) k d q).toAddEquiv.toIntLinearEquiv

@[simp]
lemma additiveFiniteSubsetLaurentCochainLinearEquiv_single
    [CommRing k] (d : ℤ) (q : ℕ)
    (I : Simplex (ι := ι) q)
    (a : AdmissibleExponent (ι := ι) d I.1)
    (r : k) :
    additiveFiniteSubsetLaurentCochainLinearEquiv
        (ι := ι) (k := k) d q
        (DFinsupp.single I (Finsupp.single a r)) =
      Finsupp.single ⟨I, a⟩ r := by
  apply (sigmaFinsuppLequivDFinsupp k).injective
  simp [additiveFiniteSubsetLaurentCochainLinearEquiv]

/-- The additive cochain equivalence intertwines the two Laurent
differentials. -/
lemma additiveFiniteSubsetLaurentCochainLinearEquiv_differential
    [CommRing k] (d : ℤ) (q : ℕ) :
    (additiveFiniteSubsetLaurentCochainLinearEquiv
      (ι := ι) (k := k) d (q + 1)).toLinearMap.comp
        (finiteSubsetDifferential
          (R := ℤ)
          (fun I : Finset ι =>
            MonomialModule (ι := ι) k d I)
          (fun {_ _} hIJ =>
            additiveRestriction (k := k) (d := d) hIJ) q) =
      (additiveDifferential
        (ι := ι) (R := k) d q).comp
        (additiveFiniteSubsetLaurentCochainLinearEquiv
          (ι := ι) (k := k) d q).toLinearMap := by
  apply DFinsupp.lhom_ext
  intro I x
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x y hx hy =>
      simp only [DFinsupp.single_add, map_add, hx, hy]
  | single a r =>
      have hsource :
          additiveFiniteSubsetLaurentCochainLinearEquiv
              (ι := ι) (k := k) d q
              (DFinsupp.single I (Finsupp.single a r)) =
            Finsupp.single ⟨I, a⟩ r :=
        additiveFiniteSubsetLaurentCochainLinearEquiv_single
          (ι := ι) (k := k) d q I a r
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      apply Eq.trans
        (b := differential (ι := ι) (R := k) d q
          (Finsupp.single ⟨I, a⟩ r))
      · rw [finiteSubsetDifferential_component,
          finiteSubsetComponentDifferential,
          LinearMap.sum_apply, map_sum,
          differential_single, basisCoboundary,
          Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [LinearMap.smul_apply, LinearMap.comp_apply,
          DFinsupp.lsingle_apply,
          additiveRestriction_apply, restriction_single,
          map_smul]
        have htarget :
            additiveFiniteSubsetLaurentCochainLinearEquiv
                (ι := ι) (k := k) d (q + 1)
                (DFinsupp.single (I.insert j.1 j.2)
                  (Finsupp.single
                    (exponentInclusion
                      (I.subset_insert j.1 j.2) a) r)) =
              Finsupp.single
                ⟨I.insert j.1 j.2,
                  exponentInclusion
                    (I.subset_insert j.1 j.2) a⟩ r :=
          additiveFiniteSubsetLaurentCochainLinearEquiv_single
            (ι := ι) (k := k) d (q + 1) _ _ r
        calc
          _ = insertionSign (R := ℤ) I.1 j.1 •
              Finsupp.single
                ⟨I.insert j.1 j.2,
                  exponentInclusion
                    (I.subset_insert j.1 j.2) a⟩ r :=
            congrArg
              (fun z =>
                insertionSign (R := ℤ) I.1 j.1 • z)
              htarget
          _ = insertionSign (R := k) I.1 j.1 •
              Finsupp.single
                ⟨I.insert j.1 j.2,
                  exponentInclusion
                    (I.subset_insert j.1 j.2) a⟩ r :=
            insertionSign_int_smul_eq_ring
              (k := k) I.1 j.1 _
          _ = _ := by
            rw [Finsupp.smul_single',
              Finsupp.smul_single']
            congr 1
            exact mul_comm _ _
      · exact congrArg
          (differential (ι := ι) (R := k) d q)
          hsource.symm

/--
The additive finite-subset Laurent complex is the explicit additive
Laurent Čech complex.
-/
noncomputable def additiveStandardLaurentCechComplexIso
    [CommRing k] (d : ℤ) :
    additiveStandardLaurentCechComplex
        (ι := ι) (k := k) d ≅
      additiveLaurentCechComplex
        (ι := ι) (R := k) d :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q =>
      (additiveFiniteSubsetLaurentCochainLinearEquiv
        (ι := ι) (k := k) d q).toModuleIso)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      simp only [additiveStandardLaurentCechComplex,
        finiteSubsetCechComplex, CochainComplex.of_d,
        additiveLaurentCechComplex_d]
      apply ModuleCat.hom_ext
      exact
        (additiveFiniteSubsetLaurentCochainLinearEquiv_differential
          (ι := ι) (k := k) d i).symm)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
