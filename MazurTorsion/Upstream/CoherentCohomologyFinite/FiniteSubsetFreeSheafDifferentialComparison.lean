/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafResolutionComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafResolution

/-!
# Differential compatibility for the ordered-cover resolution

The degreewise finite-subset comparison identifies the normalized
ordered-cover differential with the usual alternating finite-subset
boundary.  Consequently, after sheafification it gives an isomorphism
from the exact ordered-cover complex to the existing finite-subset free
sheaf complex.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

attribute [local instance] availableCoverIndexLinearOrder
  availableCoverIndexCategory

omit [Fintype ι] in
lemma insertionPosition_image_strictMono_erase
    {n : ℕ} (e : Fin (n + 1) → ι) (he : StrictMono e)
    (i : Fin (n + 1)) :
    insertionPosition
        ((Finset.univ.image e).erase (e i)) (e i) =
      i.1 := by
  rw [insertionPosition]
  have hfinset :
      ((Finset.univ.image e).erase (e i)).filter
          (fun a => a < e i) =
        (Finset.univ.filter (fun j => j < i)).image e := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hai, ⟨j, rfl⟩⟩, hji⟩
      exact ⟨j, ⟨he.lt_iff_lt.mp hji, rfl⟩⟩
    · rintro ⟨j, ⟨hji, rfl⟩⟩
      exact ⟨⟨ne_of_lt (he hji), ⟨j, rfl⟩⟩, he hji⟩
  rw [hfinset, Finset.card_image_of_injective _ he.injective]
  rw [show Finset.univ.filter (fun j => j < i) = Finset.Iio i by
    ext j
    simp]
  exact Fin.card_Iio i

lemma orderedNerve_face_nondegenerate
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate (q + 1))
    (i : Fin (q + 2)) :
    (CategoryTheory.nerve (CoverIndex U V)).δ i x.1 ∈
      (CategoryTheory.nerve
        (CoverIndex U V)).nonDegenerate q := by
  rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  intro a b hab
  have h :=
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
      x.1).mp x.2)
      (Fin.succAboveOrderEmb i |>.strictMono hab)
  change x.1.obj (i.succAbove a) <
    x.1.obj (i.succAbove b) at h
  exact h

lemma nondegenerateToAvailableSimplex_face_val
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate (q + 1))
    (i : Fin (q + 2)) :
    (nondegenerateToAvailableSimplex U V q
      ⟨(CategoryTheory.nerve (CoverIndex U V)).δ i x.1,
        orderedNerve_face_nondegenerate U V q x i⟩).1.1 =
      (nondegenerateToAvailableSimplex U V (q + 1) x).1.1.erase
        (x.1.obj i).1 := by
  dsimp [nondegenerateToAvailableSimplex]
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_erase, CategoryTheory.nerve.δ_obj]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨?_, ⟨i.succAbove j, rfl⟩⟩
    intro h
    have hxinj :
        Function.Injective
          (fun k : Fin (q + 2) => (x.1.obj k).1) :=
      fun a b h => by
        apply ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
          x.1).mp x.2).injective
        exact Subtype.ext h
    exact Fin.succAbove_ne i j (hxinj h)
  · rintro ⟨hai, ⟨j, rfl⟩⟩
    have hji : j ≠ i := by
      intro h
      apply hai
      subst j
      rfl
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact ⟨k, rfl⟩

lemma nondegenerateToAvailableSimplex_face
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate (q + 1))
    (i : Fin (q + 2)) :
    (nondegenerateToAvailableSimplex U V q
      ⟨(CategoryTheory.nerve (CoverIndex U V)).δ i x.1,
        orderedNerve_face_nondegenerate U V q x i⟩).1 =
      (nondegenerateToAvailableSimplex U V (q + 1) x).1.erase
        (x.1.obj i).1
        (by
          exact Finset.mem_image.mpr
            ⟨i, Finset.mem_univ i, rfl⟩) := by
  apply Subtype.ext
  exact nondegenerateToAvailableSimplex_face_val U V q x i

lemma orderedNerve_face_sign
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate (q + 1))
    (i : Fin (q + 2)) :
    insertionSign (R := ℤ)
        ((nondegenerateToAvailableSimplex U V (q + 1) x).1.1.erase
          (x.1.obj i).1)
        (x.1.obj i).1 =
      (-1 : ℤ) ^ i.1 := by
  dsimp [nondegenerateToAvailableSimplex]
  rw [insertionSign,
    insertionPosition_image_strictMono_erase]
  intro a b hab
  have h :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
      x.1).mp x.2 hab
  change (x.1.obj a).1 < (x.1.obj b).1 at h
  exact h

/-- The vertices of a nondegenerate ordered-nerve simplex are
equivalent to the elements of its underlying finite subset. -/
noncomputable def orderedNerveVertexEquiv
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate q) :
    Fin (q + 1) ≃
      ↥(nondegenerateToAvailableSimplex U V q x).1.1 := by
  let f :
      Fin (q + 1) →
        ↥(nondegenerateToAvailableSimplex U V q x).1.1 :=
    fun i =>
      ⟨(x.1.obj i).1,
        Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, rfl⟩⟩
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro a b hab
    apply ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
      x.1).mp x.2).injective
    apply Subtype.ext
    exact congrArg
      (fun z :
        ↥(nondegenerateToAvailableSimplex U V q x).1.1 =>
          z.1) hab
  · rw [Fintype.card_fin, Fintype.card_coe,
      (nondegenerateToAvailableSimplex U V q x).1.2]

/-- The represented-presheaf face map obtained by deleting one
vertex. -/
noncomputable def finiteSubsetSigmaPresheafFaceMap
    (U : ι → Opens T) {q : ℕ}
    (J : Simplex (ι := ι) (q + 1)) (j : ↥J.1) :
    yoneda.obj (intersection U J.1) ⋙
        sigmaConst.obj (ModuleCat.of R R) ⟶
      yoneda.obj (intersection U (J.erase j.1 j.2).1) ⋙
        sigmaConst.obj (ModuleCat.of R R) :=
  Functor.whiskerRight
    (yoneda.map
      (homOfLE
        (intersection_anti U
          (Finset.erase_subset j.1 J.1))))
    (sigmaConst.obj (ModuleCat.of R R))

/-- The alternating boundary out of one represented finite-subset
summand. -/
noncomputable def finiteSubsetSigmaPresheafSimplexBoundary
    (U : ι → Opens T) (q : ℕ)
    (J : Simplex (ι := ι) (q + 1)) :
    (yoneda.obj (intersection U J.1) ⋙
        sigmaConst.obj (ModuleCat.of R R)) ⟶
      finiteSubsetSigmaPresheafTerm (R := R) U q :=
  ∑ j : ↥J.1,
    insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
      (finiteSubsetSigmaPresheafFaceMap (R := R) U J j ≫
        Limits.Sigma.ι
          (fun I : Simplex (ι := ι) q =>
            yoneda.obj (intersection U I.1) ⋙
              sigmaConst.obj (ModuleCat.of R R))
          (J.erase j.1 j.2))

/-- The alternating differential on the represented finite-subset
presheaf terms. -/
noncomputable def finiteSubsetSigmaPresheafBoundary
    (U : ι → Opens T) (q : ℕ) :
    finiteSubsetSigmaPresheafTerm (R := R) U (q + 1) ⟶
      finiteSubsetSigmaPresheafTerm (R := R) U q :=
  Limits.Sigma.desc
    (finiteSubsetSigmaPresheafSimplexBoundary (R := R) U q)

/-- The generator of the represented finite-subset term attached to
an available simplex. -/
noncomputable def availableFiniteSubsetGenerator
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (A : AvailableSimplex U V q) :
    ModuleCat.of R R ⟶
      (finiteSubsetSigmaPresheafTerm
        (R := R) U q).obj (op V) :=
  Limits.Sigma.ι
      (fun _ : (V ⟶ intersection U A.1.1) =>
        ModuleCat.of R R)
      (homOfLE A.2) ≫
    (Limits.Sigma.ι
      (fun I : Simplex (ι := ι) q =>
        yoneda.obj (intersection U I.1) ⋙
          sigmaConst.obj (ModuleCat.of R R))
      A.1).app (op V)

lemma availableFiniteSubsetGenerator_congr
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    {A B : AvailableSimplex U V q} (h : A = B) :
    availableFiniteSubsetGenerator (R := R) U V q A =
      availableFiniteSubsetGenerator (R := R) U V q B := by
  subst B
  rfl

@[reassoc]
lemma finiteSubsetSigmaPresheaf_generator_boundary
    (U : ι → Opens T) (V : (Opens T)ᵒᵖ) (q : ℕ)
    (J : Simplex (ι := ι) (q + 1))
    (h : V.unop ⟶ intersection U J.1) :
    Limits.Sigma.ι
          (fun _ : (V.unop ⟶ intersection U J.1) =>
            ModuleCat.of R R) h ≫
        (Limits.Sigma.ι
          (fun I : Simplex (ι := ι) (q + 1) =>
            yoneda.obj (intersection U I.1) ⋙
              sigmaConst.obj (ModuleCat.of R R))
          J).app V ≫
        (finiteSubsetSigmaPresheafBoundary
          (R := R) U q).app V =
      ∑ j : ↥J.1,
        insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
          (Limits.Sigma.ι
              (fun _ :
                (V.unop ⟶
                  intersection U (J.erase j.1 j.2).1) =>
                ModuleCat.of R R)
              (h ≫ homOfLE
                (intersection_anti U
                  (Finset.erase_subset j.1 J.1))) ≫
            (Limits.Sigma.ι
              (fun I : Simplex (ι := ι) q =>
                yoneda.obj (intersection U I.1) ⋙
                  sigmaConst.obj (ModuleCat.of R R))
              (J.erase j.1 j.2)).app V) := by
  have houter :
      (Limits.Sigma.ι
          (fun I : Simplex (ι := ι) (q + 1) =>
            yoneda.obj (intersection U I.1) ⋙
              sigmaConst.obj (ModuleCat.of R R))
          J).app V ≫
        (finiteSubsetSigmaPresheafBoundary
          (R := R) U q).app V =
      (finiteSubsetSigmaPresheafSimplexBoundary
        (R := R) U q J).app V := by
    have hnat :=
      congrArg
        (fun f :
          (yoneda.obj (intersection U J.1) ⋙
              sigmaConst.obj (ModuleCat.of R R)) ⟶
            finiteSubsetSigmaPresheafTerm (R := R) U q =>
          f.app V)
        (Limits.Sigma.ι_desc
          (finiteSubsetSigmaPresheafSimplexBoundary
            (R := R) U q) J)
    simpa [finiteSubsetSigmaPresheafBoundary] using hnat
  let gen :
      ModuleCat.of R R ⟶
        (yoneda.obj (intersection U J.1) ⋙
          sigmaConst.obj (ModuleCat.of R R)).obj V :=
    Limits.Sigma.ι
      (fun _ : (V.unop ⟶ intersection U J.1) =>
        ModuleCat.of R R) h
  change gen ≫
      (Limits.Sigma.ι
        (fun I : Simplex (ι := ι) (q + 1) =>
          yoneda.obj (intersection U I.1) ⋙
            sigmaConst.obj (ModuleCat.of R R)) J).app V ≫
      (finiteSubsetSigmaPresheafBoundary (R := R) U q).app V = _
  rw [houter]
  let f := fun j : ↥J.1 =>
    insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
      (finiteSubsetSigmaPresheafFaceMap (R := R) U J j ≫
        Limits.Sigma.ι
          (fun I : Simplex (ι := ι) q =>
            yoneda.obj (intersection U I.1) ⋙
              sigmaConst.obj (ModuleCat.of R R))
          (J.erase j.1 j.2))
  change
    gen ≫ (∑ j, f j).app V = _
  have hsum :
      (∑ j, f j).app V = ∑ j, (f j).app V := by
    change
      ((evaluation (Opens T)ᵒᵖ
        (ModuleCat.{u} R)).obj V).map (∑ j, f j) =
        ∑ j,
          ((evaluation (Opens T)ᵒᵖ
            (ModuleCat.{u} R)).obj V).map (f j)
    rw [Functor.map_sum]
  rw [hsum]
  rw [Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [f]
  rw [show
      (insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
        (finiteSubsetSigmaPresheafFaceMap (R := R) U J j ≫
          Limits.Sigma.ι
            (fun I : Simplex (ι := ι) q =>
              yoneda.obj (intersection U I.1) ⋙
                sigmaConst.obj (ModuleCat.of R R))
            (J.erase j.1 j.2))).app V =
        insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
          (finiteSubsetSigmaPresheafFaceMap (R := R) U J j ≫
            Limits.Sigma.ι
              (fun I : Simplex (ι := ι) q =>
                yoneda.obj (intersection U I.1) ⋙
                  sigmaConst.obj (ModuleCat.of R R))
              (J.erase j.1 j.2)).app V by
      change
        ((evaluation (Opens T)ᵒᵖ
          (ModuleCat.{u} R)).obj V).map
            (insertionSign (R := ℤ)
              (J.1.erase j.1) j.1 •
                (finiteSubsetSigmaPresheafFaceMap
                  (R := R) U J j ≫
                  Limits.Sigma.ι
                    (fun I : Simplex (ι := ι) q =>
                      yoneda.obj (intersection U I.1) ⋙
                        sigmaConst.obj (ModuleCat.of R R))
                    (J.erase j.1 j.2))) = _
      rw [Functor.map_zsmul]
      rfl]
  rw [Preadditive.comp_zsmul]
  congr 1
  have hinner :
      gen ≫
        (finiteSubsetSigmaPresheafFaceMap
          (R := R) U J j).app V =
      Limits.Sigma.ι
          (fun _ :
            (V.unop ⟶
              intersection U (J.erase j.1 j.2).1) =>
            ModuleCat.of R R)
          (h ≫ homOfLE
            (intersection_anti U
              (Finset.erase_subset j.1 J.1))) := by
    dsimp only [gen]
    change
      Limits.Sigma.ι
          (fun _ : (V.unop ⟶ intersection U J.1) =>
            ModuleCat.of R R) h ≫
        (sigmaConst.obj (ModuleCat.of R R)).map
          ((yoneda.map
            (homOfLE
              (intersection_anti U
                (Finset.erase_subset j.1 J.1)))).app V) =
      _
    dsimp only [sigmaConst]
    rw [Limits.Sigma.ι_comp_map']
    simp only [Category.id_comp]
    rfl
  simp only [NatTrans.comp_app]
  erw [← Category.assoc, hinner]
  rfl

@[reassoc]
lemma ι_orderedCoverNormalizedTermIsoFiniteSubset_hom_app
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate q) :
    (CategoryTheory.nerve
        (CoverIndex U V)).ιNormalizedChainComplex x.1 ≫
      (orderedCoverNormalizedTermIsoFiniteSubset
        (R := R) U q).hom.app (op V) =
    Limits.Sigma.ι
        (fun _ : (V ⟶ intersection U
            (nondegenerateToAvailableSimplex U V q x).1.1) =>
          ModuleCat.of R R)
        (homOfLE
          (nondegenerateToAvailableSimplex U V q x).2) ≫
      (Limits.Sigma.ι
        (fun I : Simplex (ι := ι) q =>
          yoneda.obj (intersection U I.1) ⋙
            sigmaConst.obj (ModuleCat.of R R))
        (nondegenerateToAvailableSimplex U V q x).1).app (op V) := by
  change _ ≫
      ((orderedCoverNormalizedTermIsoAvailable
        (R := R) U q).hom.app (op V) ≫
        (availableFiniteSubsetSigmaIso
          (R := R) U q).hom.app (op V)) = _
  erw [← Category.assoc,
    ι_evaluatedNormalizedTermIsoAvailable_hom
      (R := R) U V q x.1 x.2]
  dsimp only [availableFiniteSubsetSigmaIso,
    availableToFiniteSubsetSigma]
  exact availableSimplexGenerator_comp_desc
    (R := R) U q (op V)
    ((finiteSubsetSigmaPresheafTerm (R := R) U q).obj (op V))
    (fun A =>
      representedIntersectionGenerator (R := R) U A.1 (op V)
          (homOfLE A.2) ≫
        (finiteSubsetSummandι (R := R) U q A.1).app (op V))
    (nondegenerateToAvailableSimplex U V q x)

/-- The degreewise finite-subset isomorphisms intertwine the normalized
ordered-nerve differential and the represented finite-subset
differential. -/
lemma orderedCoverNormalizedTermIsoFiniteSubset_comm_boundary
    (U : ι → Opens T) (q : ℕ) :
    (orderedCoverNormalizedTermIsoFiniteSubset
        (R := R) U (q + 1)).hom ≫
      finiteSubsetSigmaPresheafBoundary (R := R) U q =
    (orderedCoverNormalizedPresheafComplex
        (R := R) U).d (q + 1) q ≫
      (orderedCoverNormalizedTermIsoFiniteSubset
        (R := R) U q).hom := by
  apply NatTrans.ext
  funext V
  obtain ⟨V⟩ := V
  change
    (orderedCoverNormalizedTermIsoFiniteSubset
        (R := R) U (q + 1)).hom.app (op V) ≫
      (finiteSubsetSigmaPresheafBoundary
        (R := R) U q).app (op V) =
    ((CategoryTheory.nerve
      (CoverIndex U V)).normalizedChainComplex
        (ModuleCat.of R R)).d (q + 1) q ≫
      (orderedCoverNormalizedTermIsoFiniteSubset
        (R := R) U q).hom.app (op V)
  apply (CategoryTheory.nerve
    (CoverIndex U V)).normalizedChainComplex_hom_ext
  intro x hx
  let termIsoNext :
      ((CategoryTheory.nerve
        (CoverIndex U V)).normalizedChainComplex
          (ModuleCat.of R R)).X (q + 1) ⟶
        (finiteSubsetSigmaPresheafTerm
          (R := R) U (q + 1)).obj (op V) :=
    (orderedCoverNormalizedTermIsoFiniteSubset
      (R := R) U (q + 1)).hom.app (op V)
  let isoNext :
      ((CategoryTheory.nerve
        (CoverIndex U V)).normalizedChainComplex
          (ModuleCat.of R R)).X (q + 1) ⟶
        (finiteSubsetSigmaPresheafTerm
          (R := R) U q).obj (op V) :=
    termIsoNext ≫
      (finiteSubsetSigmaPresheafBoundary
        (R := R) U q).app (op V)
  let isoCurrent :
      ((CategoryTheory.nerve
        (CoverIndex U V)).normalizedChainComplex
          (ModuleCat.of R R)).X q ⟶
        (finiteSubsetSigmaPresheafTerm
          (R := R) U q).obj (op V) :=
    (orderedCoverNormalizedTermIsoFiniteSubset
      (R := R) U q).hom.app (op V)
  change
    (CategoryTheory.nerve
        (CoverIndex U V)).ιNormalizedChainComplex x ≫ isoNext =
      (CategoryTheory.nerve
          (CoverIndex U V)).ιNormalizedChainComplex x ≫
        ((CategoryTheory.nerve
          (CoverIndex U V)).normalizedChainComplex
            (ModuleCat.of R R)).d (q + 1) q ≫ isoCurrent
  let xn :
      (CategoryTheory.nerve
        (CoverIndex U V)).nonDegenerate (q + 1) :=
    ⟨x, hx⟩
  let gen :
      ModuleCat.of R R ⟶
        (yoneda.obj (intersection U
            (nondegenerateToAvailableSimplex
              U V (q + 1) xn).1.1) ⋙
          sigmaConst.obj (ModuleCat.of R R)).obj (op V) :=
    Limits.Sigma.ι
      (fun _ : (V ⟶ intersection U
          (nondegenerateToAvailableSimplex
            U V (q + 1) xn).1.1) =>
        ModuleCat.of R R)
      (homOfLE
        (nondegenerateToAvailableSimplex
          U V (q + 1) xn).2)
  have hgen :=
    ι_orderedCoverNormalizedTermIsoFiniteSubset_hom_app
      (R := R) U V (q + 1) xn
  change
    (CategoryTheory.nerve
        (CoverIndex U V)).ιNormalizedChainComplex x ≫
      termIsoNext =
      gen ≫
        (Limits.Sigma.ι
          (fun I : Simplex (ι := ι) (q + 1) =>
            yoneda.obj (intersection U I.1) ⋙
              sigmaConst.obj (ModuleCat.of R R))
          (nondegenerateToAvailableSimplex
            U V (q + 1) xn).1).app (op V) at hgen
  have hgenComp :=
    congrArg
      (fun k =>
        k ≫ (finiteSubsetSigmaPresheafBoundary
          (R := R) U q).app (op V))
      hgen
  let boundaryResult :
      ModuleCat.of R R ⟶
        (finiteSubsetSigmaPresheafTerm
          (R := R) U q).obj (op V) :=
    ∑ j : ↥(nondegenerateToAvailableSimplex
        U V (q + 1) xn).1.1,
      insertionSign (R := ℤ)
          ((nondegenerateToAvailableSimplex
            U V (q + 1) xn).1.1.erase j.1) j.1 •
        (Limits.Sigma.ι
            (fun _ :
              (V ⟶ intersection U
                ((nondegenerateToAvailableSimplex
                  U V (q + 1) xn).1.erase j.1 j.2).1) =>
                ModuleCat.of R R)
            (homOfLE
                (nondegenerateToAvailableSimplex
                  U V (q + 1) xn).2 ≫
              homOfLE
                (intersection_anti U
                  (Finset.erase_subset j.1
                    (nondegenerateToAvailableSimplex
                      U V (q + 1) xn).1.1))) ≫
          (Limits.Sigma.ι
            (fun I : Simplex (ι := ι) q =>
              yoneda.obj (intersection U I.1) ⋙
                sigmaConst.obj (ModuleCat.of R R))
            ((nondegenerateToAvailableSimplex
              U V (q + 1) xn).1.erase j.1 j.2)).app (op V))
  have hboundary :=
    finiteSubsetSigmaPresheaf_generator_boundary
      (R := R) U (op V) q
      (nondegenerateToAvailableSimplex
        U V (q + 1) xn).1
      (homOfLE
        (nondegenerateToAvailableSimplex
          U V (q + 1) xn).2)
  change
    (gen ≫
      (Limits.Sigma.ι
        (fun I : Simplex (ι := ι) (q + 1) =>
          yoneda.obj (intersection U I.1) ⋙
            sigmaConst.obj (ModuleCat.of R R))
        (nondegenerateToAvailableSimplex
          U V (q + 1) xn).1).app (op V)) ≫
      (finiteSubsetSigmaPresheafBoundary
        (R := R) U q).app (op V) = boundaryResult at hboundary
  calc
    _ = ((CategoryTheory.nerve
          (CoverIndex U V)).ιNormalizedChainComplex x ≫
          termIsoNext) ≫
        (finiteSubsetSigmaPresheafBoundary
          (R := R) U q).app (op V) := by
            dsimp only [isoNext]
            rw [Category.assoc]
    _ =
        (gen ≫
          (Limits.Sigma.ι
            (fun I : Simplex (ι := ι) (q + 1) =>
              yoneda.obj (intersection U I.1) ⋙
                sigmaConst.obj (ModuleCat.of R R))
            (nondegenerateToAvailableSimplex
              U V (q + 1) xn).1).app (op V)) ≫
        (finiteSubsetSigmaPresheafBoundary
          (R := R) U q).app (op V) :=
      hgenComp
    _ = boundaryResult := hboundary
    _ = _ := by
      dsimp only [boundaryResult]
      symm
      erw [← Category.assoc]
      rw [SSet.ιNormalizedChainComplex_d]
      rw [Preadditive.sum_comp]
      apply Fintype.sum_equiv
        (orderedNerveVertexEquiv U V (q + 1) xn)
      intro i
      rw [Preadditive.zsmul_comp]
      let xi :
          (CategoryTheory.nerve
            (CoverIndex U V)).nonDegenerate q :=
        ⟨(CategoryTheory.nerve
            (CoverIndex U V)).δ i x,
          orderedNerve_face_nondegenerate U V q xn i⟩
      erw [
        ι_orderedCoverNormalizedTermIsoFiniteSubset_hom_app
          (R := R) U V q xi]
      rw [← orderedNerve_face_sign U V q xn i]
      have hface :
          (nondegenerateToAvailableSimplex U V q xi).1 =
            (nondegenerateToAvailableSimplex
              U V (q + 1) xn).1.erase
              (orderedNerveVertexEquiv
                U V (q + 1) xn i).1
              (orderedNerveVertexEquiv
                U V (q + 1) xn i).2 := by
        rw [nondegenerateToAvailableSimplex_face U V q xn i]
        rfl
      let A :=
        nondegenerateToAvailableSimplex
          U V (q + 1) xn
      let j : ↥A.1.1 :=
        orderedNerveVertexEquiv U V (q + 1) xn i
      let E : Simplex (ι := ι) q :=
        A.1.erase j.1 j.2
      let AE : AvailableSimplex U V q :=
        ⟨E, A.2.trans
          (intersection_anti U
            (Finset.erase_subset j.1 A.1.1))⟩
      have hAvail :
          nondegenerateToAvailableSimplex U V q xi = AE := by
        apply Subtype.ext
        exact hface
      have hsign :
          insertionSign (R := ℤ)
              ((nondegenerateToAvailableSimplex
                U V (q + 1) xn).1.1.erase
                (x.obj i).1)
              (x.obj i).1 =
            insertionSign (R := ℤ)
              (A.1.1.erase j.1) j.1 := by
        rfl
      have hrightGenerator :
          availableFiniteSubsetGenerator
              (R := R) U V q AE =
            Limits.Sigma.ι
                (fun _ : (V ⟶ intersection U E.1) =>
                  ModuleCat.of R R)
                (homOfLE A.2 ≫
                  homOfLE
                    (intersection_anti U
                      (Finset.erase_subset j.1 A.1.1))) ≫
              (Limits.Sigma.ι
                (fun I : Simplex (ι := ι) q =>
                  yoneda.obj (intersection U I.1) ⋙
                    sigmaConst.obj (ModuleCat.of R R))
                E).app (op V) := by
        dsimp only [availableFiniteSubsetGenerator]
        congr 1
      change
        insertionSign (R := ℤ)
              ((nondegenerateToAvailableSimplex
                U V (q + 1) xn).1.1.erase
                (x.obj i).1)
              (x.obj i).1 •
            availableFiniteSubsetGenerator
              (R := R) U V q
                (nondegenerateToAvailableSimplex U V q xi) =
          insertionSign (R := ℤ)
              (A.1.1.erase j.1) j.1 •
            (Limits.Sigma.ι
                (fun _ : (V ⟶ intersection U E.1) =>
                  ModuleCat.of R R)
                (homOfLE A.2 ≫
                  homOfLE
                    (intersection_anti U
                      (Finset.erase_subset j.1 A.1.1))) ≫
              (Limits.Sigma.ι
                (fun I : Simplex (ι := ι) q =>
                  yoneda.obj (intersection U I.1) ⋙
                    sigmaConst.obj (ModuleCat.of R R))
                E).app (op V))
      calc
        _ = insertionSign (R := ℤ)
                ((nondegenerateToAvailableSimplex
                  U V (q + 1) xn).1.1.erase
                  (x.obj i).1)
                (x.obj i).1 •
              availableFiniteSubsetGenerator
                (R := R) U V q AE := by
          rw [availableFiniteSubsetGenerator_congr
            (R := R) U V q hAvail]
        _ = insertionSign (R := ℤ)
                (A.1.1.erase j.1) j.1 •
              availableFiniteSubsetGenerator
                (R := R) U V q AE := by
          rw [hsign]
        _ = _ := by
          rw [hrightGenerator]
          rfl

/-- The represented finite-subset presheaf boundary squares to zero. -/
theorem finiteSubsetSigmaPresheafBoundary_comp
    (U : ι → Opens T) (q : ℕ) :
    finiteSubsetSigmaPresheafBoundary (R := R) U (q + 1) ≫
        finiteSubsetSigmaPresheafBoundary (R := R) U q =
      0 := by
  let e :=
    orderedCoverNormalizedTermIsoFiniteSubset
      (R := R) U (q + 2)
  apply (cancel_epi e.hom).1
  rw [← Category.assoc,
    orderedCoverNormalizedTermIsoFiniteSubset_comm_boundary]
  rw [Category.assoc,
    orderedCoverNormalizedTermIsoFiniteSubset_comm_boundary]
  rw [← Category.assoc,
    (orderedCoverNormalizedPresheafComplex
      (R := R) U).d_comp_d, zero_comp, comp_zero]

/-- The represented finite-subset presheaf chain complex. -/
noncomputable def finiteSubsetSigmaPresheafComplex
    (U : ι → Opens T) :
    ChainComplex ((Opens T)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  ChainComplex.of
    (fun q => finiteSubsetSigmaPresheafTerm (R := R) U q)
    (fun q => finiteSubsetSigmaPresheafBoundary (R := R) U q)
    (finiteSubsetSigmaPresheafBoundary_comp (R := R) U)

/-- The normalized ordered-cover presheaf complex is isomorphic, with
differentials, to the represented finite-subset presheaf complex. -/
noncomputable def orderedCoverNormalizedPresheafComplexIsoFiniteSubset
    (U : ι → Opens T) :
    orderedCoverNormalizedPresheafComplex (R := R) U ≅
      finiteSubsetSigmaPresheafComplex (R := R) U :=
  HomologicalComplex.Hom.isoOfComponents
    (orderedCoverNormalizedTermIsoFiniteSubset (R := R) U)
    (by
      rintro i j (rfl : j + 1 = i)
      simpa [finiteSubsetSigmaPresheafComplex] using
        (orderedCoverNormalizedTermIsoFiniteSubset_comm_boundary
          (R := R) U j))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
