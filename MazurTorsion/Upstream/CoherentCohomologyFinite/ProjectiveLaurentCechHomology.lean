/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCech

/-!
# Exponentwise homology of the projective Laurent Čech complex

The Laurent Čech differential preserves every signed exponent vector.
For a fixed homogeneous exponent `a`, its summand is the free module on
the simplices containing `a.negativeSupport`.

When the negative support is not the full vertex set, adjoining/removing a
chosen vertex outside that support gives the standard simplex contracting
homotopy.  The two exceptional supports are the empty support in degree
zero and the full support in top degree.
-/


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open scoped BigOperators

namespace ProjectiveLaurentCech

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

/-- The degree-`q` cochains belonging to one homogeneous exponent. -/
abbrev ExponentCochain (R : Type*) [Semiring R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d) (q : ℕ) :=
  SimplexForExponent (ι := ι) a q →₀ R

/-- Add a missing vertex to a simplex in a fixed-exponent summand. -/
def SimplexForExponent.insert {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d} {q : ℕ}
    (I : SimplexForExponent (ι := ι) a q)
    (j : MissingVertex I.1.1) :
    SimplexForExponent (ι := ι) a (q + 1) :=
  ⟨I.1.insert j.1 j.2,
    ProjectiveExponent.AdmissibleOn.insert I.2 j.1⟩

@[simp]
lemma SimplexForExponent.insert_simplex {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d} {q : ℕ}
    (I : SimplexForExponent (ι := ι) a q)
    (j : MissingVertex I.1.1) :
    (I.insert j).1.1 = Insert.insert j.1 I.1.1 :=
  rfl

@[simp]
lemma SimplexForExponent.mem_insert {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d} {q : ℕ}
    (I : SimplexForExponent (ι := ι) a q)
    (j : MissingVertex I.1.1) (r : ι) :
    r ∈ (I.insert j).1.1 ↔ r = j.1 ∨ r ∈ I.1.1 := by
  change r ∈ Insert.insert j.1 I.1.1 ↔ _
  exact Finset.mem_insert

/-- Coboundary of a fixed-exponent simplex basis vector. -/
noncomputable def exponentBasisCoboundary [CommRing R]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (I : SimplexForExponent (ι := ι) a q) :
    ExponentCochain (ι := ι) R a (q + 1) :=
  ∑ j : MissingVertex I.1.1,
    Finsupp.single (I.insert j)
      (insertionSign (R := R) I.1.1 j.1)

/-- Differential on the summand belonging to a fixed exponent. -/
noncomputable def exponentDifferential [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    ExponentCochain (ι := ι) R a q →ₗ[R]
      ExponentCochain (ι := ι) R a (q + 1) :=
  Finsupp.linearCombination R
    (exponentBasisCoboundary (ι := ι) (R := R))

@[simp]
lemma exponentDifferential_single [CommRing R]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (I : SimplexForExponent (ι := ι) a q)
    (r : R) :
    exponentDifferential (ι := ι) (R := R) a q
        (Finsupp.single I r) =
      r • exponentBasisCoboundary (R := R) I := by
  simp [exponentDifferential]

/-- Embed one fixed-exponent basis into the full Laurent Čech basis. -/
def exponentBasisEmbedding {d : ℤ}
    (a : HomogeneousExponent (ι := ι) d) (q : ℕ) :
    SimplexForExponent (ι := ι) a q →
      BasisIndex (ι := ι) d q :=
  fun I =>
    ⟨I.1, ⟨a.1, a.2, I.2⟩⟩

omit [LinearOrder ι] in
lemma exponentBasisEmbedding_injective {d : ℤ}
    (a : HomogeneousExponent (ι := ι) d) (q : ℕ) :
    Function.Injective
      (exponentBasisEmbedding (ι := ι) a q) := by
  intro I J h
  apply Subtype.ext
  exact congrArg Sigma.fst h

/-- Embed a fixed-exponent summand in the full cochain module. -/
noncomputable def exponentCochainInclusion [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    ExponentCochain (ι := ι) R a q →ₗ[R]
      Cochain (ι := ι) R d q :=
  Finsupp.lmapDomain R R
    (exponentBasisEmbedding (ι := ι) a q)

omit [LinearOrder ι] in
lemma exponentCochainInclusion_injective [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    Function.Injective
      (exponentCochainInclusion (R := R) a q) := by
  exact Finsupp.mapDomain_injective
    (exponentBasisEmbedding_injective a q)

omit [LinearOrder ι] in
@[simp]
lemma exponentCochainInclusion_single [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    {q : ℕ} (I : SimplexForExponent (ι := ι) a q)
    (r : R) :
    exponentCochainInclusion (R := R) a q
        (Finsupp.single I r) =
      Finsupp.single (exponentBasisEmbedding a q I) r := by
  simp [exponentCochainInclusion, Finsupp.lmapDomain_apply]

/--
The fixed-exponent differential is the restriction of the full Laurent
Čech differential.
-/
lemma exponentCochainInclusion_differential [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    (exponentCochainInclusion (R := R) a (q + 1)).comp
        (exponentDifferential (R := R) a q) =
      (differential (R := R) d q).comp
        (exponentCochainInclusion (R := R) a q) := by
  apply Finsupp.lhom_ext
  intro I r
  simp only [LinearMap.comp_apply,
    exponentDifferential_single,
    exponentCochainInclusion_single,
    differential_single, map_smul]
  congr 1
  rw [exponentBasisCoboundary, basisCoboundary,
    map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [exponentCochainInclusion_single]
  congr 2

/-- The fixed-exponent differential squares to zero. -/
theorem exponentDifferential_comp [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) :
    (exponentDifferential (R := R) a (q + 1)).comp
        (exponentDifferential (R := R) a q) = 0 := by
  apply LinearMap.ext
  intro c
  apply exponentCochainInclusion_injective
    (R := R) a (q + 2)
  change
    exponentCochainInclusion (R := R) a (q + 2)
        (exponentDifferential (R := R) a (q + 1)
          (exponentDifferential (R := R) a q c)) =
      exponentCochainInclusion (R := R) a (q + 2) 0
  rw [map_zero]
  calc
    _ = differential (R := R) d (q + 1)
          (exponentCochainInclusion (R := R) a (q + 1)
            (exponentDifferential (R := R) a q c)) := by
      exact LinearMap.congr_fun
        (exponentCochainInclusion_differential
          (R := R) a (q + 1))
        (exponentDifferential (R := R) a q c)
    _ = differential (R := R) d (q + 1)
          (differential (R := R) d q
            (exponentCochainInclusion (R := R) a q c)) := by
      congr 1
      exact LinearMap.congr_fun
        (exponentCochainInclusion_differential
          (R := R) a q) c
    _ = 0 :=
      differential_differential (R := R) d q
        (exponentCochainInclusion (R := R) a q c)

omit [LinearOrder ι] in
/-- A vertex outside the negative support has nonnegative exponent. -/
lemma nonnegative_at_of_not_mem_negativeSupport
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    {r : ι}
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1) :
    0 ≤ a.1 r := by
  rw [← not_lt]
  intro har
  exact hr
    ((ProjectiveExponent.mem_negativeSupport a.1 r).mpr har)

/--
Remove a chosen nonnegative vertex from an admissible simplex.
-/
def SimplexForExponent.erase {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1))
    (hrI : r ∈ I.1.1) :
    SimplexForExponent (ι := ι) a q :=
  ⟨I.1.erase r hrI,
    ProjectiveExponent.AdmissibleOn.erase_of_nonnegative
      I.2 (nonnegative_at_of_not_mem_negativeSupport a hr)⟩

@[simp]
lemma SimplexForExponent.erase_simplex {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1))
    (hrI : r ∈ I.1.1) :
    (I.erase r hr hrI).1.1 = I.1.1.erase r :=
  rfl

/-- Contract one fixed-exponent simplex basis vector at `r`. -/
noncomputable def exponentBasisHomotopy [CommRing R]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1)) :
    ExponentCochain (ι := ι) R a q :=
  if hrI : r ∈ I.1.1 then
    Finsupp.single (I.erase r hr hrI)
      (insertionSign (R := R) (I.1.1.erase r) r)
  else
    0

/-- The fixed-exponent simplex contracting homotopy. -/
noncomputable def exponentHomotopy [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1) :
    ExponentCochain (ι := ι) R a (q + 1) →ₗ[R]
      ExponentCochain (ι := ι) R a q :=
  Finsupp.linearCombination R
    (exponentBasisHomotopy (ι := ι) (R := R) r hr)

@[simp]
lemma exponentHomotopy_single [CommRing R]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1))
    (c : R) :
    exponentHomotopy (R := R) a r hr
        (Finsupp.single I c) =
      c • exponentBasisHomotopy (R := R) r hr I := by
  simp [exponentHomotopy]

omit [Fintype ι] in
lemma insertionSign_mul_self [CommRing R]
    (I : Finset ι) (r : ι) :
    insertionSign (R := R) I r *
      insertionSign (R := R) I r = 1 := by
  simp [insertionSign, ← mul_pow]

omit [Fintype ι] in
/--
The two non-distinguished terms in the simplex contraction have opposite
signs.
-/
lemma insertionSign_homotopy_cancel [CommRing R]
    {I : Finset ι} {r j : ι}
    (hrI : r ∉ I) (hjI : j ∉ I) (hrj : r ≠ j) :
    insertionSign (R := R) I r *
          insertionSign (R := R) I j +
        insertionSign (R := R) (Insert.insert r I) j *
          insertionSign (R := R) (Insert.insert j I) r =
      0 := by
  rcases lt_or_gt_of_ne hrj with hrj' | hjr'
  · rw [insertionSign, insertionSign, insertionSign, insertionSign,
      insertionPosition_insert_of_lt hrI hrj',
      insertionPosition_insert_of_not_lt (not_lt_of_ge hrj'.le),
      pow_succ]
    ring
  · rw [insertionSign, insertionSign, insertionSign, insertionSign,
      insertionPosition_insert_of_not_lt (not_lt_of_ge hjr'.le),
      insertionPosition_insert_of_lt hjI hjr',
      pow_succ]
    ring

/--
After erasing a vertex `r ∈ I`, a missing vertex is either `r` itself or
a vertex which was already missing from `I`.
-/
noncomputable def missingVertexEraseEquiv
    (I : Finset ι) (r : ι) (hrI : r ∈ I) :
    Option (MissingVertex I) ≃ MissingVertex (I.erase r) := by
  classical
  let f : Option (MissingVertex I) → MissingVertex (I.erase r)
    | none => ⟨r, by simp⟩
    | some j =>
        ⟨j.1, by
          intro hj
          exact j.2 (Finset.mem_of_mem_erase hj)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j =>
            exfalso
            exact j.2 ((congrArg Subtype.val hxy).symm ▸ hrI)
    | some j =>
        cases y with
        | none =>
            exfalso
            exact j.2 (congrArg Subtype.val hxy ▸ hrI)
        | some k =>
            congr 1
            apply Subtype.ext
            exact congrArg
              (fun z : MissingVertex (I.erase r) => z.1) hxy
  · intro j
    by_cases hjr : j.1 = r
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      exact hjr.symm
    · have hjI : j.1 ∉ I := by
        intro hjI
        exact j.2 ((Finset.mem_erase).2 ⟨hjr, hjI⟩)
      refine ⟨some ⟨j.1, hjI⟩, ?_⟩
      apply Subtype.ext
      rfl

omit [Fintype ι] in
@[simp]
lemma missingVertexEraseEquiv_none
    (I : Finset ι) (r : ι) (hrI : r ∈ I) :
    (missingVertexEraseEquiv I r hrI none).1 = r := by
  rfl

omit [Fintype ι] in
@[simp]
lemma missingVertexEraseEquiv_some
    (I : Finset ι) (r : ι) (hrI : r ∈ I)
    (j : MissingVertex I) :
    (missingVertexEraseEquiv I r hrI (some j)).1 = j.1 := by
  rfl

lemma SimplexForExponent.erase_insert {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a q)
    (hrI : r ∉ I.1.1) :
    (I.insert ⟨r, hrI⟩).erase r hr
        (by simp) = I := by
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.erase_insert hrI

lemma SimplexForExponent.insert_erase {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1))
    (hrI : r ∈ I.1.1) :
    (I.erase r hr hrI).insert
        (missingVertexEraseEquiv I.1.1 r hrI none) = I := by
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.insert_erase hrI

lemma SimplexForExponent.insert_erase_some {d : ℤ}
    {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1))
    (hrI : r ∈ I.1.1) (j : MissingVertex I.1.1) :
    (I.erase r hr hrI).insert
          (missingVertexEraseEquiv I.1.1 r hrI (some j)) =
        (I.insert j).erase r hr
          ((SimplexForExponent.mem_insert I j r).2
            (Or.inr hrI)) := by
  have hjr : j.1 ≠ r := by
    intro hjr
    exact j.2 (hjr ▸ hrI)
  apply Subtype.ext
  apply Subtype.ext
  exact (Finset.erase_insert_of_ne hjr).symm

/-- The two terms indexed by a vertex already missing from `I` cancel. -/
lemma exponentHomotopy_cancel_term [CommRing R]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1))
    (hrI : r ∈ I.1.1) (j : MissingVertex I.1.1) :
    Finsupp.single
          ((I.erase r hr hrI).insert
            (missingVertexEraseEquiv I.1.1 r hrI (some j)))
          (insertionSign (R := R) (I.1.1.erase r) r *
            insertionSign (R := R) (I.1.1.erase r) j.1) +
        Finsupp.single
          ((I.insert j).erase r hr
            ((SimplexForExponent.mem_insert I j r).2
              (Or.inr hrI)))
          (insertionSign (R := R) I.1.1 j.1 *
            insertionSign (R := R)
              ((Insert.insert j.1 I.1.1).erase r) r) =
      0 := by
  have hjr : j.1 ≠ r := by
    intro hjr
    exact j.2 (hjr ▸ hrI)
  have hrK : r ∉ I.1.1.erase r := by simp
  have hjK : j.1 ∉ I.1.1.erase r := by
    intro hjK
    exact j.2 (Finset.mem_of_mem_erase hjK)
  have hI : Insert.insert r (I.1.1.erase r) = I.1.1 :=
    Finset.insert_erase hrI
  have hJ :
      (Insert.insert j.1 I.1.1).erase r =
        Insert.insert j.1 (I.1.1.erase r) :=
    Finset.erase_insert_of_ne hjr
  have hsignI :
      insertionSign (R := R) I.1.1 j.1 =
        insertionSign (R := R)
          (Insert.insert r (I.1.1.erase r)) j.1 :=
    congrArg (fun K => insertionSign (R := R) K j.1) hI.symm
  rw [I.insert_erase_some r hr hrI j]
  rw [← Finsupp.single_add]
  rw [Finsupp.single_eq_zero, hsignI, hJ]
  exact insertionSign_homotopy_cancel hrK hjK hjr.symm

/--
If the contracting vertex is absent from a basis simplex, applying the
homotopy after the coboundary returns that basis vector.
-/
lemma exponentHomotopy_basisCoboundary_of_not_mem [CommRing R]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a q)
    (hrI : r ∉ I.1.1) :
    exponentHomotopy (R := R) (q := q) a r hr
        (exponentBasisCoboundary (R := R) I) =
      Finsupp.single I 1 := by
  rw [exponentBasisCoboundary, map_sum]
  simp_rw [exponentHomotopy_single]
  simp only [exponentBasisHomotopy,
    SimplexForExponent.mem_insert, hrI, or_false]
  let rI : MissingVertex I.1.1 := ⟨r, hrI⟩
  rw [Fintype.sum_eq_single rI]
  · dsimp only [rI]
    simp only [eq_self, dite_true,
      Finsupp.smul_single']
    have herase :
        (I.insert ⟨r, hrI⟩).1.1.erase r = I.1.1 :=
      Finset.erase_insert hrI
    rw [I.erase_insert r hr hrI]
    rw [herase]
    rw [insertionSign_mul_self]
  · intro x hx
    have h : r ≠ x.1 := by
      intro h'
      apply hx
      apply Subtype.ext
      exact h'.symm
    simp [h]

lemma exponentHomotopy_basis_identity [CommRing R]
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {q : ℕ} (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a (q + 1)) :
    exponentDifferential (R := R) a q
          (exponentBasisHomotopy (R := R) r hr I) +
        exponentHomotopy (R := R) a r hr
          (exponentBasisCoboundary (R := R) I) =
      Finsupp.single I 1 := by
  by_cases hrI : r ∈ I.1.1
  · simp [exponentBasisHomotopy, hrI,
      exponentBasisCoboundary, map_sum]
    rw [Finset.smul_sum]
    simp_rw [Finsupp.smul_single']
    simp_rw [← Finsupp.single_mul]
    change
      (∑ x : MissingVertex (I.1.1.erase r),
          Finsupp.single
            ((I.erase r hr hrI).insert x)
            (insertionSign (R := R) (I.1.1.erase r) r *
              insertionSign (R := R) (I.1.1.erase r) x.1)) +
        _ = _
    rw [← Equiv.sum_comp
      (missingVertexEraseEquiv I.1.1 r hrI)
      (fun x =>
        Finsupp.single
          ((I.erase r hr hrI).insert x)
          (insertionSign (R := R) (I.1.1.erase r) r *
            insertionSign (R := R) (I.1.1.erase r) x.1))]
    rw [Fintype.sum_option]
    rw [I.insert_erase r hr hrI]
    simp only [missingVertexEraseEquiv_none]
    rw [insertionSign_mul_self]
    rw [add_assoc, ← Finset.sum_add_distrib]
    apply add_eq_left.mpr
    apply Finset.sum_eq_zero
    intro j hj
    exact exponentHomotopy_cancel_term
      (R := R) r hr I hrI j
  · rw [exponentBasisHomotopy, dif_neg hrI,
      map_zero, zero_add]
    exact exponentHomotopy_basisCoboundary_of_not_mem
      (R := R) r hr I hrI

/--
Adjoining/removing a vertex outside the negative support contracts the
fixed-exponent complex in every positive cochain degree.
-/
theorem exponentHomotopy_identity [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1) :
    (exponentDifferential (R := R) a q).comp
          (exponentHomotopy (R := R) (q := q) a r hr) +
        (exponentHomotopy (R := R) (q := q + 1) a r hr).comp
          (exponentDifferential (R := R) a (q + 1)) =
      LinearMap.id := by
  apply Finsupp.lhom_ext
  intro I c
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    exponentHomotopy_single, exponentDifferential_single,
    map_smul, LinearMap.id_apply]
  rw [← smul_add]
  rw [exponentHomotopy_basis_identity]
  simp

/--
Every positive-degree spot of a fixed-exponent summand is exact as soon
as one vertex lies outside the negative support.
-/
theorem exponentDifferential_exact_of_not_mem [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ) (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1) :
    Function.Exact
      (exponentDifferential (R := R) a q)
      (exponentDifferential (R := R) a (q + 1)) := by
  intro c
  constructor
  · intro hc
    refine ⟨exponentHomotopy (R := R) (q := q) a r hr c, ?_⟩
    have hidentity :=
      LinearMap.congr_fun
        (exponentHomotopy_identity
          (R := R) a q r hr) c
    simpa [LinearMap.add_apply, LinearMap.comp_apply, hc]
      using hidentity
  · rintro ⟨b, rfl⟩
    have hd :=
      LinearMap.congr_fun
        (exponentDifferential_comp
          (R := R) a q) b
    simpa [LinearMap.comp_apply] using hd

/--
If the negative support is not the whole vertex set, all positive
fixed-exponent cohomology groups vanish.
-/
theorem exponentDifferential_exact_of_negativeSupport_ne_univ
    [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (q : ℕ)
    (ha :
      ProjectiveExponent.negativeSupport a.1 ≠
        (Finset.univ : Finset ι)) :
    Function.Exact
      (exponentDifferential (R := R) a q)
      (exponentDifferential (R := R) a (q + 1)) := by
  have hexists :
      ∃ r : ι,
        r ∉ ProjectiveExponent.negativeSupport a.1 := by
    by_contra h
    have hall :
        ∀ r : ι,
          r ∈ ProjectiveExponent.negativeSupport a.1 := by
      intro r
      by_contra hr
      exact h ⟨r, hr⟩
    exact ha (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨r, hr⟩ := hexists
  exact exponentDifferential_exact_of_not_mem
    (R := R) a q r hr

omit [LinearOrder ι] in
lemma not_mem_degreeZero_simplex_of_mem_negativeSupport
    {d : ℤ} {a : HomogeneousExponent (ι := ι) d}
    {s r : ι}
    (hs : s ∈ ProjectiveExponent.negativeSupport a.1)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1)
    (I : SimplexForExponent (ι := ι) a 0) :
    r ∉ I.1.1 := by
  intro hrI
  have hsI : s ∈ I.1.1 := I.2 hs
  have hcard : I.1.1.card = 1 := I.1.2
  obtain ⟨i, hI⟩ := Finset.card_eq_one.mp hcard
  rw [hI] at hsI hrI
  simp only [Finset.mem_singleton] at hsI hrI
  subst s
  subst r
  exact hr hs

/--
For a nonempty negative support, any chosen vertex outside the support
gives a left inverse to the degree-zero differential.
-/
theorem exponentHomotopy_comp_differential_degreeZero
    [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (ha :
      (ProjectiveExponent.negativeSupport a.1).Nonempty)
    (r : ι)
    (hr : r ∉ ProjectiveExponent.negativeSupport a.1) :
    (exponentHomotopy (R := R) (q := 0) a r hr).comp
        (exponentDifferential (R := R) a 0) =
      LinearMap.id := by
  obtain ⟨s, hs⟩ := ha
  apply Finsupp.lhom_ext
  intro I c
  simp only [LinearMap.comp_apply,
    exponentDifferential_single, map_smul,
    LinearMap.id_apply]
  rw [exponentHomotopy_basisCoboundary_of_not_mem
    (R := R) r hr I
      (not_mem_degreeZero_simplex_of_mem_negativeSupport
        hs hr I)]
  simp

/--
The degree-zero differential is injective unless the negative support is
empty or the whole vertex set.
-/
theorem exponentDifferential_degreeZero_injective_of_support_nonempty_ne_univ
    [CommRing R]
    {d : ℤ} (a : HomogeneousExponent (ι := ι) d)
    (hnonempty :
      (ProjectiveExponent.negativeSupport a.1).Nonempty)
    (hne :
      ProjectiveExponent.negativeSupport a.1 ≠
        (Finset.univ : Finset ι)) :
    Function.Injective
      (exponentDifferential (R := R) a 0) := by
  have hexists :
      ∃ r : ι,
        r ∉ ProjectiveExponent.negativeSupport a.1 := by
    by_contra h
    have hall :
        ∀ r : ι,
          r ∈ ProjectiveExponent.negativeSupport a.1 := by
      intro r
      by_contra hr
      exact h ⟨r, hr⟩
    exact hne (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨r, hr⟩ := hexists
  intro x y hxy
  have hleft :=
    exponentHomotopy_comp_differential_degreeZero
      (R := R) a hnonempty r hr
  calc
    x = ((exponentHomotopy (R := R) (q := 0) a r hr).comp
          (exponentDifferential (R := R) a 0)) x := by
        rw [hleft]
        rfl
    _ = ((exponentHomotopy (R := R) (q := 0) a r hr).comp
          (exponentDifferential (R := R) a 0)) y := by
        exact congrArg
          (exponentHomotopy (R := R) (q := 0) a r hr) hxy
    _ = y := by
        rw [hleft]
        rfl

end ProjectiveLaurentCech

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
