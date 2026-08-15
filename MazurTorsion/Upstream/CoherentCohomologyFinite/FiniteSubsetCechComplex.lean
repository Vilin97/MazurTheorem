/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCech
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Finite-subset Čech complexes

This file packages the normalized Čech complex of a finite family of modules.
Degree `q` is the dependent direct sum over subsets of cardinality `q + 1`,
and the differential is the alternating sum of the restriction maps.

The proof that the differential squares to zero pairs the two orders of
adjoining distinct vertices.  It is independent of the geometric source of
the modules and restriction maps.
-/

open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

noncomputable section

variable [CommRing R]
variable (A : Finset ι → Type*)
variable [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
variable (res : ∀ {I J : Finset ι}, I ⊆ J → A I →ₗ[R] A J)

omit [Fintype ι] [LinearOrder ι] in
private lemma smul_res_heq_neg_of_eq
    {I J K : Finset ι}
    (hIJ : I ⊆ J) (hIK : I ⊆ K) (hJK : J = K)
    (a b : R) (hab : a = -b) (x : A I) :
    a • res hIJ x ≍ -(b • res hIK x) := by
  subst K
  apply heq_of_eq
  rw [hab]
  simp

/-- Normalized degree-`q` cochains, indexed by `(q + 1)`-element subsets. -/
abbrev FiniteSubsetCochain (q : ℕ) :=
  Π₀ I : Simplex (ι := ι) q, A I.1

/-- Adjoin an ordered pair of missing vertices to a simplex. -/
def Simplex.insertPair {q : ℕ}
    (I : Simplex (ι := ι) q)
    (p : SecondMissingPair I.1) :
    Simplex (ι := ι) (q + 1 + 1) :=
  (I.insert p.1.1 p.1.2).insert p.2.1 p.2.2

omit [Fintype ι] in
@[simp]
lemma Simplex.insertPair_val {q : ℕ}
    (I : Simplex (ι := ι) q)
    (p : SecondMissingPair I.1) :
    (I.insertPair p).1 =
      Insert.insert p.2.1 (Insert.insert p.1.1 I.1) :=
  rfl

omit [Fintype ι] in
lemma Simplex.insertPair_swap {q : ℕ}
    (I : Simplex (ι := ι) q)
    (p : SecondMissingPair I.1) :
    I.insertPair p = I.insertPair p.swap := by
  apply Subtype.ext
  simp only [Simplex.insertPair_val,
    SecondMissingPair.swap_first,
    SecondMissingPair.swap_second]
  exact Finset.insert_comm _ _ _

omit [Fintype ι] in
lemma Simplex.subset_insertPair {q : ℕ}
    (I : Simplex (ι := ι) q)
    (p : SecondMissingPair I.1) :
    I.1 ⊆ (I.insertPair p).1 :=
  (I.subset_insert p.1.1 p.1.2).trans
    ((I.insert p.1.1 p.1.2).subset_insert p.2.1 p.2.2)

/-- The contribution to the Čech differential from one source simplex. -/
noncomputable def finiteSubsetComponentDifferential (q : ℕ)
    (I : Simplex (ι := ι) q) :
    A I.1 →ₗ[R] FiniteSubsetCochain A (q + 1) :=
  ∑ j : MissingVertex I.1,
    insertionSign (R := R) I.1 j.1 •
      ((DFinsupp.lsingle
        (R := R) (M := fun J : Simplex (ι := ι) (q + 1) => A J.1)
        (I.insert j.1 j.2)).comp
          (res (I.subset_insert j.1 j.2)))

/-- The alternating normalized Čech differential. -/
noncomputable def finiteSubsetDifferential (q : ℕ) :
    FiniteSubsetCochain A q →ₗ[R]
      FiniteSubsetCochain A (q + 1) :=
  (DFinsupp.lsum R) (finiteSubsetComponentDifferential A res q)

noncomputable def finiteSubsetSecondTerm
    {q : ℕ} (I : Simplex (ι := ι) q)
    (x : A I.1) (p : SecondMissingPair I.1) :
    FiniteSubsetCochain A (q + 1 + 1) :=
  DFinsupp.single (I.insertPair p) <|
    (insertionSign (R := R) I.1 p.1.1 *
      insertionSign (R := R)
        (Insert.insert p.1.1 I.1) p.2.1) •
      res (I.subset_insertPair p) x

omit [Fintype ι] in
lemma finiteSubsetSecondTerm_add_swap
    {q : ℕ} (I : Simplex (ι := ι) q)
    (x : A I.1) (p : SecondMissingPair I.1) :
    finiteSubsetSecondTerm A res I x p +
      finiteSubsetSecondTerm A res I x p.swap = 0 := by
  unfold finiteSubsetSecondTerm
  rw [← eq_neg_iff_add_eq_zero, ← DFinsupp.single_neg]
  apply (DFinsupp.single_eq_single_iff _ _ _ _).2
  left
  refine ⟨I.insertPair_swap p, ?_⟩
  apply smul_res_heq_neg_of_eq A res
    (I.subset_insertPair p)
    (I.subset_insertPair p.swap)
    (congrArg Subtype.val (I.insertPair_swap p))
  exact insertionSign_pair_swap (R := R) p

lemma finiteSubsetDifferential_component
    (q : ℕ) (I : Simplex (ι := ι) q) (x : A I.1) :
    finiteSubsetDifferential A res q
        (DFinsupp.single I x) =
      finiteSubsetComponentDifferential A res q I x := by
  exact DFinsupp.lsum_single R
    (finiteSubsetComponentDifferential A res q) I x

lemma finiteSubsetDifferential_componentDifferential
    (hres : ∀ {I J K : Finset ι}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      res hJK (res hIJ x) = res (hIJ.trans hJK) x)
    (q : ℕ) (I : Simplex (ι := ι) q) (x : A I.1) :
    finiteSubsetDifferential A res (q + 1)
        (finiteSubsetComponentDifferential A res q I x) =
      ∑ p : SecondMissingPair I.1,
        finiteSubsetSecondTerm A res I x p := by
  rw [finiteSubsetComponentDifferential, LinearMap.sum_apply,
    map_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [LinearMap.smul_apply, map_smul, LinearMap.comp_apply,
    DFinsupp.lsingle_apply,
    finiteSubsetDifferential_component,
    finiteSubsetComponentDifferential,
    LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [LinearMap.smul_apply, smul_smul]
  let k' : MissingVertex (Insert.insert j.1 I.1) :=
    ⟨k.1, k.2⟩
  change
    _ =
      finiteSubsetSecondTerm A res I x
        ⟨j, k'⟩
  rw [LinearMap.comp_apply, DFinsupp.lsingle_apply,
    finiteSubsetSecondTerm]
  rw [← DFinsupp.single_smul]
  congr 1
  simp only [k', Simplex.coe_insert]
  apply congrArg
  exact hres
    (I.subset_insert j.1 j.2)
    ((I.insert j.1 j.2).subset_insert k.1 k.2)
    x

theorem finiteSubsetDifferential_comp
    (hres : ∀ {I J K : Finset ι}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      res hJK (res hIJ x) = res (hIJ.trans hJK) x)
    (q : ℕ) :
    (finiteSubsetDifferential A res (q + 1)).comp
        (finiteSubsetDifferential A res q) = 0 := by
  apply DFinsupp.lhom_ext
  intro I x
  change
    finiteSubsetDifferential A res (q + 1)
        (finiteSubsetDifferential A res q (DFinsupp.single I x)) =
      0
  rw [finiteSubsetDifferential_component,
    finiteSubsetDifferential_componentDifferential A res hres]
  apply Finset.sum_involution
    (fun p _ => SecondMissingPair.swap p)
  · intro p _
    exact finiteSubsetSecondTerm_add_swap A res I x p
  · intro p _ _
    exact p.swap_ne
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact p.swap_swap

/-- The normalized Čech cochain complex of a finite contravariant section
system, written covariantly in inclusions of index sets. -/
noncomputable def finiteSubsetCechComplex
    (hres : ∀ {I J K : Finset ι}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      res hJK (res hIJ x) = res (hIJ.trans hJK) x) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R (FiniteSubsetCochain A q))
    (fun q => ModuleCat.ofHom (finiteSubsetDifferential A res q))
    (fun q => by
      apply ModuleCat.hom_ext
      exact finiteSubsetDifferential_comp A res hres q)

end

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
