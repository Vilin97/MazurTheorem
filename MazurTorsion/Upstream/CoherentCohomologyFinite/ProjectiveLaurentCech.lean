/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCechExponents

/-!
# The Laurent monomial Čech complex of projective space

This file gives an algebraic model for the homogeneous pieces of the
standard affine-cover Čech complex of projective space.  On a simplex `I`,
the degree-`d` term is the free module on signed exponent vectors of total
degree `d` whose negative support is contained in `I`.  Restriction along
`I ⊆ J` is the basis inclusion.

The cochain module is presented as a `Finsupp` on pairs `(I,a)`.  This makes
both the basis and the direct-sum decomposition by exponent vectors
explicit.  The differential is the usual alternating sum over adjoining
one vertex.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open scoped BigOperators

namespace ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/--
Signed degree-`d` exponents which occur on the Laurent chart indexed by
`I`.
-/
abbrev AdmissibleExponent (d : ℤ) (I : Finset ι) :=
  {a : ProjectiveExponent ι //
    ProjectiveExponent.totalDegree a = d ∧
      ProjectiveExponent.AdmissibleOn a I}

/-- The degree-`d` Laurent monomial module on the simplex `I`. -/
abbrev MonomialModule (R : Type*) [Semiring R]
    (d : ℤ) (I : Finset ι) :=
  AdmissibleExponent (ι := ι) d I →₀ R

/-- The monomials form the distinguished basis of a Laurent chart term. -/
noncomputable def monomialBasis [CommSemiring R] (d : ℤ) (I : Finset ι) :
    Module.Basis (AdmissibleExponent (ι := ι) d I) R
      (MonomialModule (ι := ι) R d I) :=
  Finsupp.basisSingleOne

/-- Inclusion of admissible exponent indices along an inclusion of simplices. -/
def exponentInclusion {d : ℤ} {I J : Finset ι} (hIJ : I ⊆ J) :
    AdmissibleExponent (ι := ι) d I →
      AdmissibleExponent (ι := ι) d J :=
  fun a =>
    ⟨a.1, a.2.1,
      ProjectiveExponent.AdmissibleOn.mono a.2.2 hIJ⟩

omit [LinearOrder ι] in
lemma exponentInclusion_injective {d : ℤ} {I J : Finset ι}
    (hIJ : I ⊆ J) :
    Function.Injective
      (exponentInclusion (ι := ι) (d := d) hIJ) := by
  intro a b h
  apply Subtype.ext
  exact congrArg
    (fun x : AdmissibleExponent (ι := ι) d J => x.1) h

omit [LinearOrder ι] in
@[simp]
lemma exponentInclusion_val {d : ℤ} {I J : Finset ι}
    (hIJ : I ⊆ J)
    (a : AdmissibleExponent (ι := ι) d I) :
    (exponentInclusion hIJ a).1 = a.1 :=
  rfl

/--
Restriction from a smaller standard intersection to a larger one.  On
monomial bases this is the evident inclusion.
-/
noncomputable def restriction [CommSemiring R] {d : ℤ} {I J : Finset ι}
    (hIJ : I ⊆ J) :
    MonomialModule (ι := ι) R d I →ₗ[R]
      MonomialModule (ι := ι) R d J :=
  Finsupp.lmapDomain R R
    (exponentInclusion (ι := ι) (d := d) hIJ)

omit [LinearOrder ι] in
@[simp]
lemma restriction_single [CommSemiring R] {d : ℤ}
    {I J : Finset ι} (hIJ : I ⊆ J)
    (a : AdmissibleExponent (ι := ι) d I) (r : R) :
    restriction (R := R) hIJ (Finsupp.single a r) =
      Finsupp.single (exponentInclusion hIJ a) r := by
  simp [restriction, Finsupp.lmapDomain_apply]

omit [LinearOrder ι] in
@[simp]
lemma restriction_id [CommSemiring R] {d : ℤ} (I : Finset ι) :
    restriction (R := R) (d := d)
        (show I ⊆ I from fun _ h => h) =
      (LinearMap.id :
        MonomialModule (ι := ι) R d I →ₗ[R]
          MonomialModule (ι := ι) R d I) := by
  rw [restriction, ← Finsupp.lmapDomain_id]
  congr 1

omit [LinearOrder ι] in
lemma restriction_comp [CommSemiring R] {d : ℤ}
    {I J K : Finset ι} (hIJ : I ⊆ J) (hJK : J ⊆ K) :
    (restriction (R := R) (d := d) hJK).comp
        (restriction (R := R) (d := d) hIJ) =
      restriction (R := R) (d := d) (hIJ.trans hJK) := by
  rw [restriction, restriction, restriction,
    ← Finsupp.lmapDomain_comp]
  congr 1

/-- A `q`-simplex is a set of exactly `q+1` coordinate indices. -/
abbrev Simplex (q : ℕ) :=
  {I : Finset ι // I.card = q + 1}

/-- Add a missing vertex to a simplex. -/
def Simplex.insert {q : ℕ} (I : Simplex (ι := ι) q)
    (j : ι) (hj : j ∉ I.1) :
    Simplex (ι := ι) (q + 1) :=
  ⟨Insert.insert j I.1, by
    rw [Finset.card_insert_of_notMem hj, I.2]⟩

omit [Fintype ι] in
@[simp]
lemma Simplex.coe_insert {q : ℕ} (I : Simplex (ι := ι) q)
    (j : ι) (hj : j ∉ I.1) :
    (I.insert j hj).1 = Insert.insert j I.1 :=
  rfl

omit [Fintype ι] in
lemma Simplex.subset_insert {q : ℕ}
    (I : Simplex (ι := ι) q) (j : ι) (hj : j ∉ I.1) :
    I.1 ⊆ (I.insert j hj).1 :=
  Finset.subset_insert j I.1

/-- Remove a vertex from a nonempty simplex. -/
def Simplex.erase {q : ℕ}
    (J : Simplex (ι := ι) (q + 1))
    (j : ι) (hj : j ∈ J.1) :
    Simplex (ι := ι) q :=
  ⟨J.1.erase j, by
    rw [Finset.card_erase_of_mem hj, J.2]
    omega⟩

omit [Fintype ι] in
@[simp]
lemma Simplex.coe_erase {q : ℕ}
    (J : Simplex (ι := ι) (q + 1))
    (j : ι) (hj : j ∈ J.1) :
    (J.erase j hj).1 = J.1.erase j :=
  rfl

/--
The basis index of the degree-`q` Laurent Čech cochains: a simplex and an
admissible degree-`d` exponent on it.
-/
abbrev BasisIndex (d : ℤ) (q : ℕ) :=
  Σ I : Simplex (ι := ι) q,
    AdmissibleExponent (ι := ι) d I.1

/-- Degree-`q`, homogeneous degree-`d` Laurent Čech cochains. -/
abbrev Cochain (R : Type*) [Semiring R] (d : ℤ) (q : ℕ) :=
  BasisIndex (ι := ι) d q →₀ R

/-- The pair `(simplex, monomial)` is the distinguished cochain basis. -/
noncomputable def cochainBasis [CommSemiring R] (d : ℤ) (q : ℕ) :
    Module.Basis (BasisIndex (ι := ι) d q) R
      (Cochain (ι := ι) R d q) :=
  Finsupp.basisSingleOne

/--
The cochain module is the finite product of its Laurent chart modules.
This is the simplexwise direct-sum decomposition.
-/
noncomputable def cochainEquivPi [CommSemiring R] (d : ℤ) (q : ℕ) :
    Cochain (ι := ι) R d q ≃ₗ[R]
      (∀ I : Simplex (ι := ι) q,
        MonomialModule (ι := ι) R d I.1) :=
  Finsupp.sigmaFinsuppLEquivPiFinsupp R

omit [LinearOrder ι] in
@[simp]
lemma cochainEquivPi_apply [CommSemiring R]
    (d : ℤ) (q : ℕ) (c : Cochain (ι := ι) R d q)
    (I : Simplex (ι := ι) q)
    (a : AdmissibleExponent (ι := ι) d I.1) :
    cochainEquivPi d q c I a = c ⟨I, a⟩ := by
  rfl

/-- All signed exponent vectors of homogeneous degree `d`. -/
abbrev HomogeneousExponent (d : ℤ) :=
  {a : ProjectiveExponent ι //
    ProjectiveExponent.totalDegree a = d}

/-- The degree-`q` simplices on which a fixed exponent occurs. -/
abbrev SimplexForExponent {d : ℤ}
    (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :=
  {I : Simplex (ι := ι) q //
    ProjectiveExponent.AdmissibleOn a.1 I.1}

/--
Reindex cochain basis pairs from `(simplex, exponent)` to
`(exponent, admissible simplex)`.
-/
def basisIndexEquivExponent (d : ℤ) (q : ℕ) :
    BasisIndex (ι := ι) d q ≃
      Σ a : HomogeneousExponent (ι := ι) d,
        SimplexForExponent (ι := ι) a q where
  toFun p :=
    ⟨⟨p.2.1, p.2.2.1⟩, ⟨p.1, p.2.2.2⟩⟩
  invFun p :=
    ⟨p.2.1, ⟨p.1.1, p.1.2, p.2.2⟩⟩
  left_inv p := by
    cases p with
    | mk I a =>
      rfl
  right_inv p := by
    cases p with
    | mk a I =>
      rfl

/--
Exponentwise direct-sum decomposition of Laurent Čech cochains.

For a fixed exponent `a`, the summand is the free module on the simplices
which contain its negative support.
-/
noncomputable def cochainEquivExponentDirectSum [CommSemiring R]
    (d : ℤ) (q : ℕ) :
    Cochain (ι := ι) R d q ≃ₗ[R]
      Π₀ a : HomogeneousExponent (ι := ι) d,
        SimplexForExponent (ι := ι) a q →₀ R :=
  (Finsupp.mapDomain.linearEquiv R R
      (basisIndexEquivExponent (ι := ι) d q)).trans
    (sigmaFinsuppLequivDFinsupp R)

/-- The number of vertices of `I` which occur before `j`. -/
def insertionPosition (I : Finset ι) (j : ι) : ℕ :=
  (I.filter fun i => i < j).card

/-- The sign attached to adjoining `j` to the ordered simplex `I`. -/
def insertionSign [CommRing R] (I : Finset ι) (j : ι) : R :=
  (-1 : R) ^ insertionPosition I j

omit [Fintype ι] in
lemma insertionPosition_insert_of_lt {I : Finset ι} {j k : ι}
    (hjI : j ∉ I) (hjk : j < k) :
    insertionPosition (Insert.insert j I) k =
      insertionPosition I k + 1 := by
  rw [insertionPosition, insertionPosition,
    Finset.filter_insert, if_pos hjk,
    Finset.card_insert_of_notMem]
  simp [hjI]

omit [Fintype ι] in
lemma insertionPosition_insert_of_not_lt {I : Finset ι}
    {j k : ι} (hjk : ¬j < k) :
    insertionPosition (Insert.insert j I) k =
      insertionPosition I k := by
  rw [insertionPosition, insertionPosition,
    Finset.filter_insert, if_neg hjk]

omit [Fintype ι] in
/--
The two orders of adjoining distinct vertices carry opposite total signs.
-/
lemma insertionSign_mul_swap [CommRing R] {I : Finset ι}
    {j k : ι} (hjI : j ∉ I) (hkI : k ∉ I) (hjk : j ≠ k) :
    insertionSign (R := R) I j *
        insertionSign (R := R) (Insert.insert j I) k =
      -(insertionSign (R := R) I k *
        insertionSign (R := R) (Insert.insert k I) j) := by
  rcases lt_or_gt_of_ne hjk with hjk' | hkj'
  · rw [insertionSign, insertionSign, insertionSign, insertionSign,
      insertionPosition_insert_of_lt hjI hjk',
      insertionPosition_insert_of_not_lt (not_lt_of_ge hjk'.le),
      pow_succ]
    ring
  · rw [insertionSign, insertionSign, insertionSign, insertionSign,
      insertionPosition_insert_of_not_lt (not_lt_of_ge hkj'.le),
      insertionPosition_insert_of_lt hkI hkj',
      pow_succ]
    ring

/-- Vertices which may be adjoined to `I`. -/
abbrev MissingVertex (I : Finset ι) :=
  {j : ι // j ∉ I}

/--
An ordered pair of distinct vertices outside `I`, presented in the order
in which they are adjoined.
-/
abbrev SecondMissingPair (I : Finset ι) :=
  Σ j : MissingVertex I,
    MissingVertex (Insert.insert j.1 I)

omit [Fintype ι] in
lemma SecondMissingPair.second_not_mem
    {I : Finset ι} (p : SecondMissingPair I) :
    p.2.1 ∉ I := by
  intro hp
  exact p.2.2 (Finset.mem_insert_of_mem hp)

omit [Fintype ι] in
lemma SecondMissingPair.ne
    {I : Finset ι} (p : SecondMissingPair I) :
    p.1.1 ≠ p.2.1 := by
  intro h
  apply p.2.2
  simp [h]

/-- Swap the order in which two missing vertices are adjoined. -/
def SecondMissingPair.swap {I : Finset ι}
    (p : SecondMissingPair I) :
    SecondMissingPair I :=
  ⟨⟨p.2.1, p.second_not_mem⟩,
    ⟨p.1.1, by
      simp only [Finset.mem_insert, not_or]
      exact ⟨p.ne, p.1.2⟩⟩⟩

omit [Fintype ι] in
@[simp]
lemma SecondMissingPair.swap_first {I : Finset ι}
    (p : SecondMissingPair I) :
    p.swap.1.1 = p.2.1 :=
  rfl

omit [Fintype ι] in
@[simp]
lemma SecondMissingPair.swap_second {I : Finset ι}
    (p : SecondMissingPair I) :
    p.swap.2.1 = p.1.1 :=
  rfl

omit [Fintype ι] in
@[simp]
lemma SecondMissingPair.swap_swap {I : Finset ι}
    (p : SecondMissingPair I) :
    p.swap.swap = p := by
  rcases p with ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
  rfl

omit [Fintype ι] in
lemma SecondMissingPair.swap_ne {I : Finset ι}
    (p : SecondMissingPair I) :
    p.swap ≠ p := by
  intro h
  have hp :
      p.2.1 = p.1.1 :=
    congrArg (fun x : SecondMissingPair I => x.1.1) h
  exact p.ne hp.symm

/-- Adjoin one missing vertex to a cochain basis index. -/
def BasisIndex.insert {d : ℤ} {q : ℕ}
    (p : BasisIndex (ι := ι) d q)
    (j : MissingVertex p.1.1) :
    BasisIndex (ι := ι) d (q + 1) :=
  ⟨p.1.insert j.1 j.2,
    exponentInclusion (p.1.subset_insert j.1 j.2) p.2⟩

@[simp]
lemma BasisIndex.insert_simplex {d : ℤ} {q : ℕ}
    (p : BasisIndex (ι := ι) d q)
    (j : MissingVertex p.1.1) :
    (p.insert j).1.1 = Insert.insert j.1 p.1.1 :=
  rfl

@[simp]
lemma BasisIndex.insert_exponent {d : ℤ} {q : ℕ}
    (p : BasisIndex (ι := ι) d q)
    (j : MissingVertex p.1.1) :
    (p.insert j).2.1 = p.2.1 :=
  rfl

/-- Adjoin an ordered pair of missing vertices. -/
def BasisIndex.insertPair {d : ℤ} {q : ℕ}
    (b : BasisIndex (ι := ι) d q)
    (p : SecondMissingPair b.1.1) :
    BasisIndex (ι := ι) d (q + 1 + 1) :=
  (b.insert p.1).insert p.2

lemma BasisIndex.insertPair_swap {d : ℤ} {q : ℕ}
    (b : BasisIndex (ι := ι) d q)
    (p : SecondMissingPair b.1.1) :
    b.insertPair p = b.insertPair p.swap := by
  have hsimplex :
      (b.insertPair p).1 =
        (b.insertPair p.swap).1 := by
    apply Subtype.ext
    simp only [insertPair, insert_simplex,
      SecondMissingPair.swap_first,
      SecondMissingPair.swap_second]
    exact Finset.insert_comm _ _ _
  apply Sigma.ext hsimplex
  rw [Subtype.heq_iff_coe_eq (by
    intro x
    rw [hsimplex])]
  change b.2.1 = b.2.1
  rfl

omit [Fintype ι] in
lemma insertionSign_pair_swap [CommRing R]
    {I : Finset ι} (p : SecondMissingPair I) :
    insertionSign (R := R) I p.1.1 *
        insertionSign (R := R)
          (Insert.insert p.1.1 I) p.2.1 =
      -(insertionSign (R := R) I p.swap.1.1 *
        insertionSign (R := R)
          (Insert.insert p.swap.1.1 I) p.swap.2.1) := by
  exact insertionSign_mul_swap
    p.1.2 p.second_not_mem p.ne

/-- Coboundary of a single Laurent monomial basis vector. -/
noncomputable def basisCoboundary [CommRing R] {d : ℤ} {q : ℕ}
    (p : BasisIndex (ι := ι) d q) :
    Cochain (ι := ι) R d (q + 1) :=
  ∑ j : MissingVertex p.1.1,
    Finsupp.single (p.insert j)
      (insertionSign (R := R) p.1.1 j.1)

/-- One ordered-pair contribution to the second coboundary of a basis vector. -/
noncomputable def secondCoboundaryTerm [CommRing R]
    {d : ℤ} {q : ℕ}
    (b : BasisIndex (ι := ι) d q)
    (p : SecondMissingPair b.1.1) :
    Cochain (ι := ι) R d (q + 1 + 1) :=
  Finsupp.single (b.insertPair p)
    (insertionSign (R := R) b.1.1 p.1.1 *
      insertionSign (R := R)
        (Insert.insert p.1.1 b.1.1) p.2.1)

lemma secondCoboundaryTerm_add_swap [CommRing R]
    {d : ℤ} {q : ℕ}
    (b : BasisIndex (ι := ι) d q)
    (p : SecondMissingPair b.1.1) :
    secondCoboundaryTerm (R := R) b p +
      secondCoboundaryTerm (R := R) b p.swap = 0 := by
  rw [secondCoboundaryTerm, secondCoboundaryTerm,
    ← b.insertPair_swap p, ← Finsupp.single_add,
    insertionSign_pair_swap p, neg_add_cancel,
    Finsupp.single_zero]

/-- The alternating Laurent Čech cochain differential. -/
noncomputable def differential [CommRing R] (d : ℤ) (q : ℕ) :
    Cochain (ι := ι) R d q →ₗ[R]
      Cochain (ι := ι) R d (q + 1) :=
  Finsupp.linearCombination R
    (basisCoboundary (ι := ι) (R := R))

@[simp]
lemma differential_single [CommRing R]
    {d : ℤ} {q : ℕ}
    (p : BasisIndex (ι := ι) d q) (r : R) :
    differential (ι := ι) (R := R) d q
        (Finsupp.single p r) =
      r • basisCoboundary (ι := ι) (R := R) p := by
  simp [differential]

/-- The second coboundary of a basis vector is the sum over ordered pairs. -/
lemma differential_basisCoboundary [CommRing R]
    {d : ℤ} {q : ℕ}
    (b : BasisIndex (ι := ι) d q) :
    differential (ι := ι) (R := R) d (q + 1)
        (basisCoboundary (R := R) b) =
      ∑ p : SecondMissingPair b.1.1,
        secondCoboundaryTerm (R := R) b p := by
  rw [basisCoboundary, map_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [differential_single, basisCoboundary,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finsupp.smul_single']
  rfl

/-- The ordered-pair contributions cancel under vertex swap. -/
lemma sum_secondCoboundaryTerm_eq_zero [CommRing R]
    {d : ℤ} {q : ℕ}
    (b : BasisIndex (ι := ι) d q) :
    ∑ p : SecondMissingPair b.1.1,
      secondCoboundaryTerm (R := R) b p = 0 := by
  apply Finset.sum_involution
    (fun p _ => SecondMissingPair.swap p)
  · intro p _
    exact secondCoboundaryTerm_add_swap b p
  · intro p _ _
    exact p.swap_ne
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact p.swap_swap

/-- The Čech differential sends every basis coboundary to zero. -/
lemma differential_basisCoboundary_eq_zero [CommRing R]
    {d : ℤ} {q : ℕ}
    (b : BasisIndex (ι := ι) d q) :
    differential (ι := ι) (R := R) d (q + 1)
        (basisCoboundary (R := R) b) = 0 := by
  rw [differential_basisCoboundary,
    sum_secondCoboundaryTerm_eq_zero]

/-- The alternating Laurent Čech differential squares to zero. -/
theorem differential_comp [CommRing R] (d : ℤ) (q : ℕ) :
    (differential (ι := ι) (R := R) d (q + 1)).comp
        (differential (ι := ι) (R := R) d q) = 0 := by
  apply Finsupp.lhom_ext
  intro b r
  simp [LinearMap.comp_apply, differential_single,
    differential_basisCoboundary_eq_zero]

/-- Pointwise form of `d² = 0`. -/
theorem differential_differential [CommRing R]
    (d : ℤ) (q : ℕ) (c : Cochain (ι := ι) R d q) :
    differential (ι := ι) (R := R) d (q + 1)
        (differential (ι := ι) (R := R) d q c) = 0 := by
  exact LinearMap.congr_fun
    (differential_comp (ι := ι) (R := R) d q) c

end ProjectiveLaurentCech

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
