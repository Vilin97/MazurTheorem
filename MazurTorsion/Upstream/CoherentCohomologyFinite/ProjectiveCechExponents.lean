/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib

/-!
# Signed exponents in the standard projective Čech complex

For a finite family of homogeneous coordinates, a Laurent monomial is
indexed by an integer-valued exponent vector.  On the intersection indexed
by a finite set `I`, precisely the coordinates in `I` have been inverted.
Thus an exponent vector occurs on that intersection when every negative
coordinate belongs to `I`.

This file isolates that finite combinatorics.  It defines total degree,
negative support, and admissibility on a simplex.  It also proves the two
finiteness statements needed at the ends of the projective Čech complex:
there are finitely many fixed-degree exponent vectors which are everywhere
nonnegative, and finitely many which are everywhere strictly negative.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- A signed exponent vector in a finite family of variables. -/
abbrev ProjectiveExponent (ι : Type*) := ι → ℤ

namespace ProjectiveExponent

variable {ι : Type*} [Fintype ι]

/-- The homogeneous total degree of a signed exponent vector. -/
def totalDegree (a : ProjectiveExponent ι) : ℤ :=
  ∑ i, a i

@[simp]
lemma totalDegree_zero :
    totalDegree (0 : ProjectiveExponent ι) = 0 := by
  simp [totalDegree]

@[simp]
lemma totalDegree_add (a b : ProjectiveExponent ι) :
    totalDegree (a + b) = totalDegree a + totalDegree b := by
  simp [totalDegree, Finset.sum_add_distrib]

@[simp]
lemma totalDegree_neg (a : ProjectiveExponent ι) :
    totalDegree (-a) = -totalDegree a := by
  simp [totalDegree]

@[simp]
lemma totalDegree_sub (a b : ProjectiveExponent ι) :
    totalDegree (a - b) = totalDegree a - totalDegree b := by
  simp [sub_eq_add_neg]

/-- The set of variables which occur with negative exponent. -/
def negativeSupport (a : ProjectiveExponent ι) : Finset ι :=
  Finset.univ.filter fun i => a i < 0

@[simp]
lemma mem_negativeSupport (a : ProjectiveExponent ι) (i : ι) :
    i ∈ negativeSupport a ↔ a i < 0 := by
  simp [negativeSupport]

@[simp]
lemma negativeSupport_zero :
    negativeSupport (0 : ProjectiveExponent ι) = ∅ := by
  ext i
  simp

/-- Every coordinate of the exponent vector is nonnegative. -/
def IsNonnegative (a : ProjectiveExponent ι) : Prop :=
  ∀ i, 0 ≤ a i

/-- Every coordinate of the exponent vector is nonpositive. -/
def IsNonpositive (a : ProjectiveExponent ι) : Prop :=
  ∀ i, a i ≤ 0

/-- Every coordinate of the exponent vector is strictly negative. -/
def IsStrictlyNegative (a : ProjectiveExponent ι) : Prop :=
  ∀ i, a i < 0

/--
Reflect every exponent across `-1/2`.  It exchanges strictly negative
vectors with nonnegative vectors and is an involution.
-/
def signComplement (a : ProjectiveExponent ι) :
    ProjectiveExponent ι :=
  fun i => -a i - 1

omit [Fintype ι] in
@[simp]
lemma signComplement_apply (a : ProjectiveExponent ι) (i : ι) :
    signComplement a i = -a i - 1 :=
  rfl

omit [Fintype ι] in
@[simp]
lemma signComplement_signComplement (a : ProjectiveExponent ι) :
    signComplement (signComplement a) = a := by
  funext i
  simp [signComplement]

lemma totalDegree_signComplement (a : ProjectiveExponent ι) :
    totalDegree (signComplement a) =
      -totalDegree a - Fintype.card ι := by
  simp [signComplement, totalDegree, Finset.sum_sub_distrib]

omit [Fintype ι] in
lemma isNonnegative_signComplement_iff
    (a : ProjectiveExponent ι) :
    IsNonnegative (signComplement a) ↔ IsStrictlyNegative a := by
  constructor <;> intro h i
  · have hi := h i
    simp only [signComplement_apply] at hi
    omega
  · have hi := h i
    simp only [signComplement_apply]
    omega

omit [Fintype ι] in
lemma isStrictlyNegative_signComplement_iff
    (a : ProjectiveExponent ι) :
    IsStrictlyNegative (signComplement a) ↔ IsNonnegative a := by
  constructor <;> intro h i
  · have hi := h i
    simp only [signComplement_apply] at hi
    omega
  · have hi := h i
    simp only [signComplement_apply]
    omega

lemma isNonnegative_iff_negativeSupport_eq_empty
    (a : ProjectiveExponent ι) :
    IsNonnegative a ↔ negativeSupport a = ∅ := by
  constructor
  · intro ha
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact (not_lt_of_ge (ha i)) ((mem_negativeSupport a i).mp hi)
  · intro ha i
    have hi : i ∉ negativeSupport a := by
      rw [ha]
      simp
    simpa using hi

lemma isStrictlyNegative_iff_negativeSupport_eq_univ
    (a : ProjectiveExponent ι) :
    IsStrictlyNegative a ↔ negativeSupport a = Finset.univ := by
  constructor
  · intro ha
    ext i
    simp [ha i]
  · intro ha i
    have hi : i ∈ negativeSupport a := by
      rw [ha]
      simp
    simpa using hi

/--
An exponent vector is admissible on `I` when only variables indexed by `I`
may occur with negative exponent.  These are exactly the Laurent monomials
present on the standard affine intersection indexed by `I`.
-/
def AdmissibleOn (a : ProjectiveExponent ι) (I : Finset ι) : Prop :=
  negativeSupport a ⊆ I

lemma admissibleOn_iff_negative_imp_mem
    (a : ProjectiveExponent ι) (I : Finset ι) :
    AdmissibleOn a I ↔ ∀ i, a i < 0 → i ∈ I := by
  simp [AdmissibleOn, Finset.subset_iff]

lemma admissibleOn_iff_nonnegative_outside
    (a : ProjectiveExponent ι) (I : Finset ι) :
    AdmissibleOn a I ↔ ∀ i, i ∉ I → 0 ≤ a i := by
  rw [admissibleOn_iff_negative_imp_mem]
  constructor
  · intro h i hi
    exact not_lt.mp fun hai => hi (h i hai)
  · intro h i hai
    by_contra hi
    exact (not_lt_of_ge (h i hi)) hai

@[simp]
lemma admissibleOn_univ (a : ProjectiveExponent ι) :
    AdmissibleOn a Finset.univ := by
  exact Finset.subset_univ _

@[simp]
lemma admissibleOn_empty_iff (a : ProjectiveExponent ι) :
    AdmissibleOn a ∅ ↔ IsNonnegative a := by
  rw [AdmissibleOn, Finset.subset_empty,
    ← isNonnegative_iff_negativeSupport_eq_empty]

lemma AdmissibleOn.mono {a : ProjectiveExponent ι} {I J : Finset ι}
    (ha : AdmissibleOn a I) (hIJ : I ⊆ J) :
    AdmissibleOn a J :=
  ha.trans hIJ

lemma admissibleOn_inter [DecidableEq ι]
    {a : ProjectiveExponent ι} {I J : Finset ι} :
    AdmissibleOn a (I ∩ J) ↔ AdmissibleOn a I ∧ AdmissibleOn a J := by
  constructor
  · intro h
    exact
      ⟨h.mono Finset.inter_subset_left,
        h.mono Finset.inter_subset_right⟩
  · rintro ⟨hI, hJ⟩ i hi
    exact Finset.mem_inter.mpr ⟨hI hi, hJ hi⟩

lemma AdmissibleOn.insert [DecidableEq ι] {a : ProjectiveExponent ι}
    {I : Finset ι} (ha : AdmissibleOn a I) (i : ι) :
    AdmissibleOn a (insert i I) :=
  ha.mono (Finset.subset_insert i I)

/--
Removing a variable whose exponent is nonnegative preserves admissibility.
This is the support fact used by the usual simplex-contraction argument.
-/
lemma AdmissibleOn.erase_of_nonnegative [DecidableEq ι]
    {a : ProjectiveExponent ι}
    {I : Finset ι} (ha : AdmissibleOn a I) {i : ι}
    (hi : 0 ≤ a i) :
    AdmissibleOn a (I.erase i) := by
  intro j hj
  refine Finset.mem_erase.mpr ⟨?_, ha hj⟩
  intro hji
  subst j
  exact (not_lt_of_ge hi) (mem_negativeSupport a i |>.mp hj)

/--
The negative support of a product exponent (pointwise sum) is contained in
the union of the two negative supports.
-/
lemma negativeSupport_add_subset [DecidableEq ι]
    (a b : ProjectiveExponent ι) :
    negativeSupport (a + b) ⊆
      negativeSupport a ∪ negativeSupport b := by
  intro i hi
  simp only [mem_negativeSupport, Pi.add_apply, Finset.mem_union] at hi ⊢
  by_cases hai : a i < 0
  · exact Or.inl hai
  by_cases hbi : b i < 0
  · exact Or.inr hbi
  omega

lemma AdmissibleOn.add [DecidableEq ι] {a b : ProjectiveExponent ι}
    {I J : Finset ι} (ha : AdmissibleOn a I)
    (hb : AdmissibleOn b J) :
    AdmissibleOn (a + b) (I ∪ J) :=
  (negativeSupport_add_subset a b).trans
    (Finset.union_subset_union ha hb)

/-- A nonnegative coordinate is bounded above by the total degree. -/
lemma coordinate_le_totalDegree_of_nonnegative
    {a : ProjectiveExponent ι} (ha : IsNonnegative a) (i : ι) :
    a i ≤ totalDegree a := by
  exact Finset.single_le_sum
    (fun j _ => ha j) (Finset.mem_univ i)

/-- For a nonpositive vector, its total degree bounds every coordinate below. -/
lemma totalDegree_le_coordinate_of_nonpositive
    {a : ProjectiveExponent ι} (ha : IsNonpositive a) (i : ι) :
    totalDegree a ≤ a i := by
  have hneg : -a i ≤ ∑ j, -a j :=
    Finset.single_le_sum
      (fun j _ => neg_nonneg.mpr (ha j)) (Finset.mem_univ i)
  have h := neg_le_neg hneg
  simpa [totalDegree] using h

/-- Exponent vectors of fixed total degree which are everywhere nonnegative. -/
def nonnegativeOfDegree (d : ℤ) : Set (ProjectiveExponent ι) :=
  {a | IsNonnegative a ∧ totalDegree a = d}

/-- Exponent vectors of fixed total degree which are everywhere nonpositive. -/
def nonpositiveOfDegree (d : ℤ) : Set (ProjectiveExponent ι) :=
  {a | IsNonpositive a ∧ totalDegree a = d}

/-- Exponent vectors of fixed total degree which are everywhere strictly negative. -/
def strictlyNegativeOfDegree (d : ℤ) : Set (ProjectiveExponent ι) :=
  {a | IsStrictlyNegative a ∧ totalDegree a = d}

/--
There are finitely many nonnegative exponent vectors of a fixed total
degree.  Each coordinate lies in the finite interval `[0,d]`.
-/
theorem nonnegativeOfDegree_finite (d : ℤ) :
    (nonnegativeOfDegree (ι := ι) d).Finite := by
  classical
  refine
    (Set.Finite.pi'
      (fun _ : ι => Set.finite_Icc (0 : ℤ) d)).subset ?_
  rintro a ⟨ha, hdegree⟩ i
  exact ⟨ha i, (coordinate_le_totalDegree_of_nonnegative ha i).trans_eq hdegree⟩

/--
There are finitely many nonpositive exponent vectors of a fixed total
degree.  Each coordinate lies in the finite interval `[d,0]`.
-/
theorem nonpositiveOfDegree_finite (d : ℤ) :
    (nonpositiveOfDegree (ι := ι) d).Finite := by
  classical
  refine
    (Set.Finite.pi'
      (fun _ : ι => Set.finite_Icc d (0 : ℤ))).subset ?_
  rintro a ⟨ha, hdegree⟩ i
  exact
    ⟨hdegree ▸ totalDegree_le_coordinate_of_nonpositive ha i, ha i⟩

/--
There are finitely many strictly negative exponent vectors of a fixed
total degree.
-/
theorem strictlyNegativeOfDegree_finite (d : ℤ) :
    (strictlyNegativeOfDegree (ι := ι) d).Finite := by
  refine (nonpositiveOfDegree_finite (ι := ι) d).subset ?_
  rintro a ⟨ha, hdegree⟩
  exact ⟨fun i => (ha i).le, hdegree⟩

/--
Strictly negative degree-`d` vectors correspond to nonnegative vectors of
degree `-d-card ι`.
-/
def strictlyNegativeOfDegreeEquivNonnegative (d : ℤ) :
    strictlyNegativeOfDegree (ι := ι) d ≃
      nonnegativeOfDegree (ι := ι) (-d - Fintype.card ι) where
  toFun a :=
    ⟨signComplement a.1,
      (isNonnegative_signComplement_iff a.1).mpr a.property.1,
      (totalDegree_signComplement a.1).trans
        (congrArg (fun z : ℤ => -z - Fintype.card ι)
          a.property.2)⟩
  invFun a :=
    ⟨signComplement a.1,
      (isStrictlyNegative_signComplement_iff a.1).mpr a.property.1,
      by
        rw [totalDegree_signComplement, a.property.2]
        omega⟩
  left_inv a := by
    apply Subtype.ext
    exact signComplement_signComplement a.1
  right_inv a := by
    apply Subtype.ext
    exact signComplement_signComplement a.1

/--
The degree-`q` standard Čech simplices on which the exponent vector `a`
occurs.  A degree-`q` simplex has `q+1` vertices.
-/
noncomputable def admissibleSimplices (a : ProjectiveExponent ι) (q : ℕ) :
    Finset (Finset ι) :=
  by
    classical
    exact Finset.univ.filter fun I =>
      I.card = q + 1 ∧ AdmissibleOn a I

@[simp]
lemma mem_admissibleSimplices
    (a : ProjectiveExponent ι) (q : ℕ) (I : Finset ι) :
    I ∈ admissibleSimplices a q ↔
      I.card = q + 1 ∧ AdmissibleOn a I := by
  classical
  simp [admissibleSimplices]

lemma card_negativeSupport_le_of_mem_admissibleSimplices
    {a : ProjectiveExponent ι} {q : ℕ} {I : Finset ι}
    (hI : I ∈ admissibleSimplices a q) :
    (negativeSupport a).card ≤ q + 1 := by
  rw [← (mem_admissibleSimplices a q I).mp hI |>.1]
  exact Finset.card_le_card
    ((mem_admissibleSimplices a q I).mp hI |>.2)

lemma admissibleSimplices_eq_empty_of_card_lt_negativeSupport
    (a : ProjectiveExponent ι) (q : ℕ)
    (hcard : q + 1 < (negativeSupport a).card) :
    admissibleSimplices a q = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  exact (not_le_of_gt hcard)
    (card_negativeSupport_le_of_mem_admissibleSimplices hI)

lemma admissibleSimplices_eq_empty_of_card_variables_lt
    (a : ProjectiveExponent ι) (q : ℕ)
    (hcard : Fintype.card ι < q + 1) :
    admissibleSimplices a q = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  have hIcard :
      I.card = q + 1 :=
    (mem_admissibleSimplices a q I).mp hI |>.1
  have hle : I.card ≤ Fintype.card ι := by
    simpa using Finset.card_le_card (Finset.subset_univ I)
  omega

/--
If all exponents are strictly negative, every admissible simplex is the
full simplex.  This singles out the exceptional support in the top Čech
degree.
-/
lemma eq_univ_of_isStrictlyNegative_of_admissibleOn
    {a : ProjectiveExponent ι} (ha : IsStrictlyNegative a)
    {I : Finset ι} (hI : AdmissibleOn a I) :
    I = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  exact hI ((mem_negativeSupport a i).mpr (ha i))

lemma eq_univ_of_isStrictlyNegative_of_mem_admissibleSimplices
    {a : ProjectiveExponent ι} (ha : IsStrictlyNegative a)
    {q : ℕ} {I : Finset ι}
    (hI : I ∈ admissibleSimplices a q) :
    I = Finset.univ :=
  eq_univ_of_isStrictlyNegative_of_admissibleOn ha
    ((mem_admissibleSimplices a q I).mp hI |>.2)

/--
For an everywhere strictly negative exponent, the full simplex is the
unique admissible simplex in its cardinality.
-/
lemma admissibleSimplices_eq_singleton_univ_of_isStrictlyNegative
    {a : ProjectiveExponent ι} (ha : IsStrictlyNegative a)
    {q : ℕ} (hcard : Fintype.card ι = q + 1) :
    admissibleSimplices a q = {Finset.univ} := by
  classical
  ext I
  constructor
  · intro hI
    exact Finset.mem_singleton.mpr
      (eq_univ_of_isStrictlyNegative_of_mem_admissibleSimplices ha hI)
  · intro hI
    have hIeq : I = Finset.univ := Finset.mem_singleton.mp hI
    subst I
    exact (mem_admissibleSimplices a q Finset.univ).mpr
      ⟨by simpa using hcard, admissibleOn_univ a⟩

lemma admissibleSimplices_eq_empty_of_isStrictlyNegative_of_card_ne
    {a : ProjectiveExponent ι} (ha : IsStrictlyNegative a)
    {q : ℕ} (hcard : Fintype.card ι ≠ q + 1) :
    admissibleSimplices a q = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  have hIeq :
      I = Finset.univ :=
    eq_univ_of_isStrictlyNegative_of_mem_admissibleSimplices ha hI
  have hIcard :
      I.card = q + 1 :=
    (mem_admissibleSimplices a q I).mp hI |>.1
  apply hcard
  simpa [hIeq] using hIcard

end ProjectiveExponent

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
