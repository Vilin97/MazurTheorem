/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafHomComparison

open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

universe uι uR uA

variable {ι : Type uι} {R : Type uR} [Fintype ι] [LinearOrder ι]
variable [CommRing R]
variable (A : Finset ι → Type uA)
variable [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
variable (res : ∀ {I J : Finset ι}, I ⊆ J → A I →ₗ[R] A J)

/-- A simplex together with a vertex outside it. -/
abbrev SimplexMissingPair (q : ℕ) :=
  {p : Simplex (ι := ι) q × ι // p.2 ∉ p.1.1}

/-- A simplex together with one of its vertices. -/
abbrev SimplexPresentPair (q : ℕ) :=
  {p : Simplex (ι := ι) (q + 1) × ι // p.2 ∈ p.1.1}

/-- Inserting a missing vertex and removing a present vertex are inverse
parameterizations of codimension-one faces. -/
def simplexInsertErasePairEquiv (q : ℕ) :
    SimplexMissingPair (ι := ι) q ≃
      SimplexPresentPair (ι := ι) q where
  toFun p :=
    ⟨(p.1.1.insert p.1.2 p.2, p.1.2),
      Finset.mem_insert_self _ _⟩
  invFun p :=
    ⟨(p.1.1.erase p.1.2 p.2, p.1.2),
      Finset.notMem_erase _ _⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Finset.erase_insert p.2
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Finset.insert_erase p.2
    · rfl

def sigmaMissingPairEquiv (q : ℕ) :
    (Σ I : Simplex (ι := ι) q, MissingVertex I.1) ≃
      SimplexMissingPair (ι := ι) q where
  toFun p := ⟨(p.1, p.2.1), p.2.2⟩
  invFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  left_inv p := by rcases p with ⟨I, ⟨j, hj⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨I, j⟩, hj⟩; rfl

def sigmaPresentPairEquiv (q : ℕ) :
    (Σ J : Simplex (ι := ι) (q + 1), ↥J.1) ≃
      SimplexPresentPair (ι := ι) q where
  toFun p := ⟨(p.1, p.2.1), p.2.2⟩
  invFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  left_inv p := by rcases p with ⟨J, ⟨j, hj⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨J, j⟩, hj⟩; rfl

def simplexInsertEraseSigmaEquiv (q : ℕ) :
    (Σ I : Simplex (ι := ι) q, MissingVertex I.1) ≃
      (Σ J : Simplex (ι := ι) (q + 1), ↥J.1) :=
  (sigmaMissingPairEquiv (ι := ι) q).trans <|
    (simplexInsertErasePairEquiv (ι := ι) q).trans <|
      (sigmaPresentPairEquiv (ι := ι) q).symm

lemma dfinsupp_eq_sum_single_fintype
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {β : κ → Type*} [∀ i, AddCommMonoid (β i)]
    (y : Π₀ i, β i) :
    y = ∑ i, DFinsupp.single i (y i) := by
  classical
  ext i
  simp

noncomputable def insertedFaceContribution (q : ℕ)
    (x : (I : Simplex (ι := ι) q) → A I.1)
    (p : Σ I : Simplex (ι := ι) q, MissingVertex I.1) :
    FiniteSubsetCochain A (q + 1) :=
  DFinsupp.single (p.1.insert p.2.1 p.2.2)
    (insertionSign (R := R) p.1.1 p.2.1 •
      res (p.1.subset_insert p.2.1 p.2.2) (x p.1))

noncomputable def removedFaceContribution (q : ℕ)
    (x : (I : Simplex (ι := ι) q) → A I.1)
    (p : Σ J : Simplex (ι := ι) (q + 1), ↥J.1) :
    FiniteSubsetCochain A (q + 1) :=
  DFinsupp.single p.1
    (insertionSign (R := R) (p.1.1.erase p.2.1) p.2.1 •
      res (Finset.erase_subset p.2.1 p.1.1)
        (x (p.1.erase p.2.1 p.2.2)))

lemma restriction_apply_eq_of_heq
    {I I' J : Finset ι} (hI : I = I')
    (hIJ : I ⊆ J) (hI'J : I' ⊆ J)
    {a : A I} {a' : A I'} (ha : a ≍ a') :
    res hIJ a = res hI'J a' := by
  subst I'
  rw [heq_iff_eq] at ha
  subst a'
  rfl

lemma insertedFaceContribution_eq_removedFaceContribution
    (q : ℕ)
    (x : (I : Simplex (ι := ι) q) → A I.1)
    (p : Σ I : Simplex (ι := ι) q, MissingVertex I.1) :
    insertedFaceContribution A res q x p =
      removedFaceContribution A res q x
        (simplexInsertEraseSigmaEquiv (ι := ι) q p) := by
  rcases p with ⟨I, ⟨j, hj⟩⟩
  let hj' : j ∈ (I.insert j hj).1 :=
    Finset.mem_insert_self j I.1
  have hface : (I.insert j hj).erase j hj' = I := by
    apply Subtype.ext
    exact Finset.erase_insert hj
  dsimp [insertedFaceContribution, removedFaceContribution,
    simplexInsertEraseSigmaEquiv, sigmaMissingPairEquiv,
    simplexInsertErasePairEquiv, sigmaPresentPairEquiv]
  congr 1
  have hval :
      (Insert.insert j I.1).erase j = I.1 :=
    congrArg Subtype.val hface
  have hsign :
      insertionSign (R := R)
          ((Insert.insert j I.1).erase j) j =
        insertionSign (R := R) I.1 j :=
    congrArg (fun K => insertionSign (R := R) K j) hval
  have hx :
      x ((I.insert j hj).erase j
          (Finset.mem_insert_self j I.1)) ≍
        x I :=
    congr_arg_heq x hface
  have hres :
      res (Finset.erase_subset j (Insert.insert j I.1))
          (x ((I.insert j hj).erase j
            (Finset.mem_insert_self j I.1))) =
        res (I.subset_insert j hj) (x I) :=
    restriction_apply_eq_of_heq A res hval
      (Finset.erase_subset j (Insert.insert j I.1))
      (I.subset_insert j hj) hx
  rw [hsign]
  apply congrArg
    (fun z : A (Insert.insert j I.1) =>
      insertionSign (R := R) I.1 j • z)
  exact hres.symm

noncomputable def finiteSubsetPiDifferential (q : ℕ) :
    ((I : Simplex (ι := ι) q) → A I.1) →ₗ[R]
      ((J : Simplex (ι := ι) (q + 1)) → A J.1) :=
  LinearMap.pi fun J =>
    ∑ j : ↥J.1,
      insertionSign (R := R) (J.1.erase j.1) j.1 •
        ((res (Finset.erase_subset j.1 J.1)).comp
          (LinearMap.proj (R := R) (J.erase j.1 j.2)))

@[simp]
lemma finiteSubsetPiDifferential_apply (q : ℕ)
    (x : (I : Simplex (ι := ι) q) → A I.1)
    (J : Simplex (ι := ι) (q + 1)) :
    finiteSubsetPiDifferential A res q x J =
      ∑ j : ↥J.1,
        insertionSign (R := R) (J.1.erase j.1) j.1 •
          res (Finset.erase_subset j.1 J.1)
            (x (J.erase j.1 j.2)) := by
  simp [finiteSubsetPiDifferential]
  apply Finset.sum_congr rfl
  intro j _
  rfl

lemma finiteSubsetDifferential_eq_sum_insertedFaces
    (q : ℕ)
    (x : (I : Simplex (ι := ι) q) → A I.1) :
    finiteSubsetDifferential A res q
        ((DFinsupp.linearEquivFunOnFintype (R := R)).symm x) =
      ∑ p : Σ I : Simplex (ι := ι) q, MissingVertex I.1,
        insertedFaceContribution A res q x p := by
  classical
  let y :
      FiniteSubsetCochain A q :=
    (DFinsupp.linearEquivFunOnFintype (R := R)).symm x
  have hy (I : Simplex (ι := ι) q) : y I = x I := by
    change
      (DFinsupp.linearEquivFunOnFintype (R := R) y) I = x I
    dsimp only [y]
    rw [LinearEquiv.apply_symm_apply]
  calc
    finiteSubsetDifferential A res q y =
        finiteSubsetDifferential A res q
          (∑ I, DFinsupp.single I (y I)) := by
      rw [← dfinsupp_eq_sum_single_fintype y]
    _ = ∑ I, finiteSubsetDifferential A res q
          (DFinsupp.single I (y I)) := by
      exact map_sum _ _ _
    _ = ∑ I, finiteSubsetComponentDifferential A res q I (y I) := by
      apply Finset.sum_congr rfl
      intro I _
      exact finiteSubsetDifferential_component A res q I (y I)
    _ = ∑ I, finiteSubsetComponentDifferential A res q I (x I) := by
      apply Finset.sum_congr rfl
      intro I _
      rw [hy I]
    _ = ∑ I, ∑ j : MissingVertex I.1,
          insertedFaceContribution A res q x ⟨I, j⟩ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [finiteSubsetComponentDifferential,
        LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [LinearMap.smul_apply, LinearMap.comp_apply,
        DFinsupp.lsingle_apply, insertedFaceContribution,
        DFinsupp.single_smul]
    _ = ∑ p : Σ I : Simplex (ι := ι) q, MissingVertex I.1,
          insertedFaceContribution A res q x p :=
      (Fintype.sum_sigma
        (fun p : Σ I : Simplex (ι := ι) q, MissingVertex I.1 =>
          insertedFaceContribution A res q x p)).symm

lemma piDifferential_symm_eq_sum_removedFaces
    (q : ℕ)
    (x : (I : Simplex (ι := ι) q) → A I.1) :
    (DFinsupp.linearEquivFunOnFintype (R := R)).symm
        (finiteSubsetPiDifferential A res q x) =
      ∑ p : Σ J : Simplex (ι := ι) (q + 1), ↥J.1,
        removedFaceContribution A res q x p := by
  classical
  let z : FiniteSubsetCochain A (q + 1) :=
    (DFinsupp.linearEquivFunOnFintype (R := R)).symm
      (finiteSubsetPiDifferential A res q x)
  have hz (J : Simplex (ι := ι) (q + 1)) :
      z J = finiteSubsetPiDifferential A res q x J := by
    change
      (DFinsupp.linearEquivFunOnFintype (R := R) z) J =
        finiteSubsetPiDifferential A res q x J
    dsimp only [z]
    rw [LinearEquiv.apply_symm_apply]
  calc
    z = ∑ J : Simplex (ι := ι) (q + 1),
          DFinsupp.single J (z J) :=
      dfinsupp_eq_sum_single_fintype z
    _ = ∑ J : Simplex (ι := ι) (q + 1), DFinsupp.single J
          (finiteSubsetPiDifferential A res q x J) := by
      apply Finset.sum_congr rfl
      intro J _
      rw [hz J]
    _ = ∑ J : Simplex (ι := ι) (q + 1), DFinsupp.single J
          (∑ j : ↥J.1,
            insertionSign (R := R) (J.1.erase j.1) j.1 •
              res (Finset.erase_subset j.1 J.1)
                (x (J.erase j.1 j.2))) := by
      apply Finset.sum_congr rfl
      intro J _
      rw [finiteSubsetPiDifferential_apply]
    _ = ∑ J : Simplex (ι := ι) (q + 1), ∑ j : ↥J.1,
          removedFaceContribution A res q x ⟨J, j⟩ := by
      apply Finset.sum_congr rfl
      intro J _
      ext K
      by_cases hK : K = J
      · subst K
        simp [removedFaceContribution]
      · have hK' : J ≠ K := fun h => hK h.symm
        simp [removedFaceContribution, hK']
    _ = ∑ p : Σ J : Simplex (ι := ι) (q + 1), ↥J.1,
          removedFaceContribution A res q x p :=
      (Fintype.sum_sigma
        (fun p : Σ J : Simplex (ι := ι) (q + 1), ↥J.1 =>
          removedFaceContribution A res q x p)).symm

lemma finiteSubsetPiDifferential_conjugate
    (q : ℕ)
    (x : (I : Simplex (ι := ι) q) → A I.1) :
    (DFinsupp.linearEquivFunOnFintype (R := R)).symm
        (finiteSubsetPiDifferential A res q x) =
      finiteSubsetDifferential A res q
        ((DFinsupp.linearEquivFunOnFintype (R := R)).symm x) := by
  classical
  calc
    _ = ∑ p : Σ J : Simplex (ι := ι) (q + 1), ↥J.1,
          removedFaceContribution A res q x p :=
      piDifferential_symm_eq_sum_removedFaces A res q x
    _ = ∑ p : Σ I : Simplex (ι := ι) q, MissingVertex I.1,
          removedFaceContribution A res q x
            (simplexInsertEraseSigmaEquiv (ι := ι) q p) :=
      (Equiv.sum_comp
        (simplexInsertEraseSigmaEquiv (ι := ι) q)
        (removedFaceContribution A res q x)).symm
    _ = ∑ p : Σ I : Simplex (ι := ι) q, MissingVertex I.1,
          insertedFaceContribution A res q x p := by
      apply Finset.sum_congr rfl
      intro p _
      exact
        (insertedFaceContribution_eq_removedFaceContribution
          A res q x p).symm
    _ = _ :=
      (finiteSubsetDifferential_eq_sum_insertedFaces
        A res q x).symm

/-- The target-oriented finite-product presentation of the normalized
finite-subset Čech complex. -/
noncomputable def finiteSubsetPiCechComplex
    (hres : ∀ {I J K : Finset ι}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      res hJK (res hIJ x) = res (hIJ.trans hJK) x) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R
      ((I : Simplex (ι := ι) q) → A I.1))
    (fun q => ModuleCat.ofHom
      (finiteSubsetPiDifferential A res q))
    (fun q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change finiteSubsetPiDifferential A res (q + 1)
          (finiteSubsetPiDifferential A res q x) = 0
      apply
        (DFinsupp.linearEquivFunOnFintype
          (R := R)
          (ι := Simplex (ι := ι) (q + 2))
          (M := fun J => A J.1)).symm.injective
      rw [finiteSubsetPiDifferential_conjugate]
      rw [finiteSubsetPiDifferential_conjugate]
      have hd :
          finiteSubsetDifferential A res (q + 1)
              (finiteSubsetDifferential A res q
                ((DFinsupp.linearEquivFunOnFintype
                  (R := R)).symm x)) = 0 := by
        exact LinearMap.congr_fun
          (finiteSubsetDifferential_comp A res hres q)
          ((DFinsupp.linearEquivFunOnFintype
            (R := R)).symm x)
      rw [hd, map_zero])

/-- The finite-support and finite-product presentations of a normalized
finite-subset Čech complex are canonically isomorphic. -/
noncomputable def finiteSubsetCechComplexIsoPi
    (hres : ∀ {I J K : Finset ι}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      res hJK (res hIJ x) = res (hIJ.trans hJK) x) :
    finiteSubsetCechComplex A res hres ≅
      finiteSubsetPiCechComplex A res hres :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q =>
      (DFinsupp.linearEquivFunOnFintype
        (R := R)
        (ι := Simplex (ι := ι) q)
        (M := fun I => A I.1)).toModuleIso)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      simp only [finiteSubsetCechComplex,
        finiteSubsetPiCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change finiteSubsetPiDifferential A res i
          (DFinsupp.linearEquivFunOnFintype (R := R) y) =
        DFinsupp.linearEquivFunOnFintype (R := R)
          (finiteSubsetDifferential A res i y)
      apply
        (DFinsupp.linearEquivFunOnFintype
          (R := R)
          (ι := Simplex (ι := ι) (i + 1))
          (M := fun J => A J.1)).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      rw [finiteSubsetPiDifferential_conjugate]
      rw [LinearEquiv.symm_apply_apply])

/-- A pointwise linear equivalence of finite contravariant section systems
induces an isomorphism of their target-oriented Čech complexes. -/
noncomputable def finiteSubsetPiCechComplexIsoOfLinearEquiv
    (B : Finset ι → Type uA)
    [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
    (resB : ∀ {I J : Finset ι}, I ⊆ J → B I →ₗ[R] B J)
    (hresA : ∀ {I J K : Finset ι}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : A I),
      res hJK (res hIJ x) = res (hIJ.trans hJK) x)
    (hresB : ∀ {I J K : Finset ι}
      (hIJ : I ⊆ J) (hJK : J ⊆ K) (x : B I),
      resB hJK (resB hIJ x) = resB (hIJ.trans hJK) x)
    (e : ∀ {q : ℕ} (I : Simplex (ι := ι) q),
      A I.1 ≃ₗ[R] B I.1)
    (he : ∀ {q : ℕ}
      (J : Simplex (ι := ι) (q + 1)) (j : ↥J.1)
      (x : A (J.1.erase j.1)),
      e J (res (Finset.erase_subset j.1 J.1) x) =
        resB (Finset.erase_subset j.1 J.1)
          (e (J.erase j.1 j.2) x)) :
    finiteSubsetPiCechComplex A res hresA ≅
      finiteSubsetPiCechComplex B resB hresB :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q =>
      (LinearEquiv.piCongrRight
        (fun I : Simplex (ι := ι) q => e I)).toModuleIso)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      simp only [finiteSubsetPiCechComplex,
        CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext J
      change
        finiteSubsetPiDifferential B resB i
            (fun I => e I (x I)) J =
          e J (finiteSubsetPiDifferential A res i x J)
      rw [finiteSubsetPiDifferential_apply,
        finiteSubsetPiDifferential_apply, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      exact congrArg
        (fun z => insertionSign (R := R)
          (J.1.erase j.1) j.1 • z)
        (he J j (x (J.erase j.1 j.2))).symm)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech
