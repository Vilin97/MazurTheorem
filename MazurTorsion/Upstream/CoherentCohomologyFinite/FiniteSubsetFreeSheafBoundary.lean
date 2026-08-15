/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafComplex

/-!
# The normalized finite-subset free-sheaf boundary squares to zero

This file isolates the sign calculation for the source-side normalized
Čech complex.  An ordered pair of deleted vertices is paired with the
opposite deletion order.  The two target simplices and the two induced
maps agree, while their alternating signs are opposite.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- An ordered pair of distinct vertices of a simplex, presented in the
order in which the vertices are deleted.  The second vertex is indexed
by the actual erased simplex, so its type agrees definitionally with the
second face map. -/
abbrev RemovedPair {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1)) :=
  Σ j : ↥J.1, ↥(J.erase j.1 j.2).1

/-- Reverse the order of an ordered pair of deleted vertices. -/
def RemovedPair.swap {q : ℕ}
    {J : Simplex (ι := ι) (q + 1 + 1)}
    (p : RemovedPair J) :
    RemovedPair J := by
  have hk : p.2.1 ∈ J.1 := Finset.mem_of_mem_erase p.2.2
  have hkj : p.2.1 ≠ p.1.1 := (Finset.mem_erase.mp p.2.2).1
  exact
    ⟨⟨p.2.1, hk⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨hkj.symm, p.1.2⟩⟩⟩

@[simp]
lemma RemovedPair.swap_first {q : ℕ}
    {J : Simplex (ι := ι) (q + 1 + 1)}
    (p : RemovedPair J) :
    p.swap.1.1 = p.2.1 :=
  rfl

@[simp]
lemma RemovedPair.swap_second {q : ℕ}
    {J : Simplex (ι := ι) (q + 1 + 1)}
    (p : RemovedPair J) :
    p.swap.2.1 = p.1.1 :=
  rfl

@[simp]
lemma RemovedPair.swap_swap {q : ℕ}
    {J : Simplex (ι := ι) (q + 1 + 1)}
    (p : RemovedPair J) :
    p.swap.swap = p := by
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl

lemma RemovedPair.swap_ne {q : ℕ}
    {J : Simplex (ι := ι) (q + 1 + 1)}
    (p : RemovedPair J) :
    p.swap ≠ p := by
  intro h
  have hp : p.2.1 = p.1.1 :=
    congrArg (fun q : RemovedPair J => q.1.1) h
  exact (Finset.mem_erase.mp p.2.2).1 hp

/-- Delete an ordered pair of vertices from a simplex. -/
abbrev Simplex.erasePair {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    Simplex (ι := ι) q :=
  (J.erase p.1.1 p.1.2).erase p.2.1 p.2.2

@[simp]
lemma Simplex.erasePair_val {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    (Simplex.erasePair J p).1 =
      (J.1.erase p.1.1).erase p.2.1 :=
  rfl

lemma Simplex.erasePair_swap {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    Simplex.erasePair J p = Simplex.erasePair J p.swap := by
  apply Subtype.ext
  simp only [Simplex.erasePair_val, RemovedPair.swap_first,
    RemovedPair.swap_second]
  exact Finset.erase_right_comm

/-- Transporting the target of a free-sheaf map is the same as applying
the free-sheaf construction to the transported inclusion of opens. -/
lemma freeModuleSheafMap_comp_eqToHom_of_index
    {α : Type u} (g : α → Opens T) {a b : α} (h : a = b)
    {V : Opens T} (i : V ⟶ g a) :
    freeModuleSheafMap (R := R) i ≫
        eqToHom
          (congrArg
            (fun x => freeModuleSheaf (R := R) (g x)) h) =
      freeModuleSheafMap (R := R)
        (i ≫ eqToHom (congrArg g h)) := by
  cases h
  simp

/-- The map induced by deleting an ordered pair, expressed directly as
the unique inclusion of the final intersection.  This canonical form
keeps the comparison of the two deletion orders independent of the
intermediate simplex. -/
noncomputable def doubleFaceMap
    (U : ι → Opens T) {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    simplexSheaf (R := R) U J ⟶
      simplexSheaf (R := R) U (Simplex.erasePair J p) :=
  freeModuleSheafMap (R := R)
    (homOfLE
      (intersection_anti U
        ((Finset.erase_subset p.2.1 (J.1.erase p.1.1)).trans
          (Finset.erase_subset p.1.1 J.1))))

/-- Composing the two ordinary face maps gives the canonical
double-face map. -/
lemma faceMap_comp_faceMap
    (U : ι → Opens T) {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    faceMap (R := R) U J p.1 ≫
        faceMap (R := R) U
          (J.erase p.1.1 p.1.2) p.2 =
      doubleFaceMap (R := R) U J p := by
  unfold faceMap doubleFaceMap
  rw [freeModuleSheafMap_comp]
  congr 1

/-- The canonical double-face maps agree after transporting along the
commutativity of deleting distinct vertices. -/
lemma doubleFaceMap_comp_eqToHom_swap
    (U : ι → Opens T) {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    doubleFaceMap (R := R) U J p ≫
        eqToHom
          (congrArg
            (fun I : Simplex (ι := ι) q =>
              simplexSheaf (R := R) U I)
            (Simplex.erasePair_swap J p)) =
      doubleFaceMap (R := R) U J p.swap := by
  unfold doubleFaceMap
  rw [freeModuleSheafMap_comp_eqToHom_of_index]
  apply congrArg
  apply Subsingleton.elim
  exact congrArg Subtype.val (Simplex.erasePair_swap J p)

/-- The product of the two alternating signs attached to an ordered
pair of deleted vertices. -/
def removedPairSign {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) : ℤ :=
  insertionSign (R := ℤ) (J.1.erase p.1.1) p.1.1 *
    insertionSign (R := ℤ)
      ((J.1.erase p.1.1).erase p.2.1) p.2.1

lemma removedPairSign_swap {q : ℕ}
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    removedPairSign J p = -removedPairSign J p.swap := by
  let I := (J.1.erase p.1.1).erase p.2.1
  have hjJ : p.1.1 ∈ J.1 := p.1.2
  have hkJ : p.2.1 ∈ J.1 := Finset.mem_of_mem_erase p.2.2
  have hkj : p.2.1 ≠ p.1.1 := (Finset.mem_erase.mp p.2.2).1
  have hjI : p.1.1 ∉ I := by
    simp [I]
  have hkI : p.2.1 ∉ I := by
    simp [I]
  have hInsertK :
      Insert.insert p.2.1 I = J.1.erase p.1.1 := by
    dsimp only [I]
    rw [Finset.insert_erase (show p.2.1 ∈ J.1.erase p.1.1 from p.2.2)]
  have hInsertJ :
      Insert.insert p.1.1 I = J.1.erase p.2.1 := by
    dsimp only [I]
    rw [Finset.erase_right_comm]
    rw [Finset.insert_erase
      (show p.1.1 ∈ J.1.erase p.2.1 from
        Finset.mem_erase.mpr ⟨hkj.symm, hjJ⟩)]
  have hEraseSwap :
      (J.1.erase p.2.1).erase p.1.1 = I := by
    dsimp only [I]
    exact Finset.erase_right_comm
  have hsignFirst :
      insertionSign (R := ℤ) (J.1.erase p.1.1) p.1.1 =
        insertionSign (R := ℤ) (Insert.insert p.2.1 I) p.1.1 :=
    congrArg
      (fun K => insertionSign (R := ℤ) K p.1.1)
      hInsertK.symm
  have hsignSwapFirst :
      insertionSign (R := ℤ) (J.1.erase p.2.1) p.2.1 =
        insertionSign (R := ℤ) (Insert.insert p.1.1 I) p.2.1 :=
    congrArg
      (fun K => insertionSign (R := ℤ) K p.2.1)
      hInsertJ.symm
  unfold removedPairSign
  simp only [RemovedPair.swap_first, RemovedPair.swap_second]
  calc
    insertionSign (R := ℤ) (J.1.erase p.1.1) p.1.1 *
          insertionSign (R := ℤ)
            ((J.1.erase p.1.1).erase p.2.1) p.2.1 =
        insertionSign (R := ℤ) (Insert.insert p.2.1 I) p.1.1 *
          insertionSign (R := ℤ) I p.2.1 := by
            rw [hsignFirst]
    _ = insertionSign (R := ℤ) I p.2.1 *
          insertionSign (R := ℤ) (Insert.insert p.2.1 I) p.1.1 := by
            rw [mul_comm]
    _ = -(insertionSign (R := ℤ) I p.1.1 *
          insertionSign (R := ℤ)
            (Insert.insert p.1.1 I) p.2.1) :=
      insertionSign_mul_swap (R := ℤ) hkI hjI hkj
    _ = -(insertionSign (R := ℤ)
            (Insert.insert p.1.1 I) p.2.1 *
          insertionSign (R := ℤ) I p.1.1) := by
            rw [mul_comm]
    _ = -(insertionSign (R := ℤ)
            (J.1.erase p.2.1) p.2.1 *
          insertionSign (R := ℤ)
            ((J.1.erase p.2.1).erase p.1.1) p.1.1) := by
            rw [hsignSwapFirst, hEraseSwap]

/-- The contribution of one ordered pair of deleted vertices to the
composite boundary. -/
def removedPairTerm
    (U : ι → Opens T) (q : ℕ)
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    simplexSheaf (R := R) U J ⟶ term (R := R) U q :=
  removedPairSign J p •
    (faceMap (R := R) U J p.1 ≫
      faceMap (R := R) U (J.erase p.1.1 p.1.2) p.2 ≫
      Limits.Sigma.ι
        (fun I : Simplex (ι := ι) q =>
          simplexSheaf (R := R) U I)
        (Simplex.erasePair J p))

lemma removedPairTerm_add_swap
    (U : ι → Opens T) (q : ℕ)
    (J : Simplex (ι := ι) (q + 1 + 1))
    (p : RemovedPair J) :
    removedPairTerm (R := R) U q J p +
      removedPairTerm (R := R) U q J p.swap = 0 := by
  rw [removedPairTerm, removedPairTerm, removedPairSign_swap]
  rw [neg_smul, neg_add_eq_zero]
  congr 1
  simp only [← Category.assoc]
  rw [faceMap_comp_faceMap (R := R) U J p,
    faceMap_comp_faceMap (R := R) U J p.swap]
  -- Both composites are the map induced by the same inclusion of
  -- intersections, followed by the same coproduct injection.
  let h :
      Simplex.erasePair J p =
        Simplex.erasePair J p.swap :=
    Simplex.erasePair_swap J p
  let f :=
    fun I : Simplex (ι := ι) q =>
      simplexSheaf (R := R) U I
  calc
    doubleFaceMap (R := R) U J p ≫
          Limits.Sigma.ι f (Simplex.erasePair J p) =
        doubleFaceMap (R := R) U J p ≫
          (eqToHom (congrArg f h) ≫
            Limits.Sigma.ι f
              (Simplex.erasePair J p.swap)) := by
          rw [Limits.Sigma.eqToHom_comp_ι f h]
    _ = (doubleFaceMap (R := R) U J p ≫
            eqToHom (congrArg f h)) ≫
          Limits.Sigma.ι f
            (Simplex.erasePair J p.swap) := by
          simp only [Category.assoc]
    _ = doubleFaceMap (R := R) U J p.swap ≫
          Limits.Sigma.ι f
            (Simplex.erasePair J p.swap) := by
          rw [doubleFaceMap_comp_eqToHom_swap]

lemma simplexBoundary_comp_boundary
    (U : ι → Opens T) (q : ℕ)
    (J : Simplex (ι := ι) (q + 1 + 1)) :
    simplexBoundary (R := R) U (q + 1) J ≫
        boundary (R := R) U q =
      ∑ p : RemovedPair J,
        removedPairTerm (R := R) U q J p := by
  rw [simplexBoundary, Preadditive.sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Preadditive.zsmul_comp]
  simp only [Category.assoc, boundary, Limits.Sigma.ι_desc]
  rw [simplexBoundary, Preadditive.comp_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Preadditive.comp_zsmul, smul_smul]
  rfl

/-- The normalized finite-subset free-sheaf boundary squares to zero. -/
theorem boundary_comp
    (U : ι → Opens T) (q : ℕ) :
    boundary (R := R) U (q + 1) ≫
        boundary (R := R) U q = 0 := by
  apply Limits.Sigma.hom_ext
  intro J
  rw [comp_zero]
  rw [boundary, Limits.Sigma.ι_desc_assoc,
    simplexBoundary_comp_boundary]
  apply Finset.sum_involution
    (fun p _ => RemovedPair.swap p)
  · intro p _
    exact removedPairTerm_add_swap (R := R) U q J p
  · intro p _ _
    exact p.swap_ne
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact p.swap_swap

/-- The normalized finite-subset free-sheaf chain complex. -/
noncomputable def complex
    (U : ι → Opens T) :
    ChainComplex (ModuleSheaf (R := R) (T := T)) ℕ :=
  ChainComplex.of
    (fun q => term (R := R) U q)
    (fun q => boundary (R := R) U q)
    (boundary_comp (R := R) U)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
