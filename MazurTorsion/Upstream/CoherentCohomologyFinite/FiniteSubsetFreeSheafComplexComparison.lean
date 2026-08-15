/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafDifferentialComparison

/-!
# Sheaf-level comparison with the finite-subset free complex

Sheafification of the represented finite-subset presheaf complex is
identified, including its alternating differential, with the existing
finite-subset free sheaf complex.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- Naturality of the canonical comparison from a coproduct of copies
of `R` to the free module functor. -/
lemma representedSigmaIsoFree_naturality
    {V W : Opens T} (i : V ⟶ W) :
    Functor.whiskerRight (yoneda.map i)
          (sigmaConst.obj (ModuleCat.of R R)) ≫
        (Functor.isoWhiskerLeft (yoneda.obj W)
          (sigmaConstIsoFreeModule (R := R))).hom =
      (Functor.isoWhiskerLeft (yoneda.obj V)
          (sigmaConstIsoFreeModule (R := R))).hom ≫
        Functor.whiskerRight (yoneda.map i)
          (ModuleCat.free R) := by
  apply NatTrans.ext
  funext X
  exact
    (sigmaConstIsoFreeModule (R := R)).hom.naturality
      ((yoneda.map i).app X)

/-- After sheafification, the represented-summand comparison commutes
with maps induced by inclusions of opens. -/
@[reassoc]
lemma sheafifiedRepresentedSigmaIsoFreeModuleSheaf_naturality
    {V W : Opens T} (i : V ⟶ W) :
    (moduleSheafification (R := R) (T := T)).map
          (Functor.whiskerRight (yoneda.map i)
            (sigmaConst.obj (ModuleCat.of R R))) ≫
        (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) W).hom =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) V).hom ≫
        freeModuleSheafMap (R := R) i := by
  change
    (moduleSheafification (R := R) (T := T)).map
          (Functor.whiskerRight (yoneda.map i)
            (sigmaConst.obj (ModuleCat.of R R))) ≫
        (moduleSheafification (R := R) (T := T)).map
          (Functor.isoWhiskerLeft (yoneda.obj W)
            (sigmaConstIsoFreeModule (R := R))).hom =
      (moduleSheafification (R := R) (T := T)).map
          (Functor.isoWhiskerLeft (yoneda.obj V)
            (sigmaConstIsoFreeModule (R := R))).hom ≫
        (moduleSheafification (R := R) (T := T)).map
          (Functor.whiskerRight (yoneda.map i)
            (ModuleCat.free R))
  rw [← Functor.map_comp, ← Functor.map_comp,
    representedSigmaIsoFree_naturality]

/-- A coproduct injection passes through the sheafified finite-subset
term comparison as the corresponding represented-summand comparison
followed by the existing free-sheaf coproduct injection. -/
@[reassoc]
lemma map_finiteSubsetSigma_ι_comp_sheafifiedTermIso
    (U : ι → Opens T) (q : ℕ)
    (I : Simplex (ι := ι) q) :
    (moduleSheafification (R := R) (T := T)).map
          (Limits.Sigma.ι
            (fun J : Simplex (ι := ι) q =>
              yoneda.obj (intersection U J.1) ⋙
                sigmaConst.obj (ModuleCat.of R R))
            I) ≫
        (sheafifiedFiniteSubsetSigmaTermIso
          (R := R) U q).hom =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U I.1)).hom ≫
        Limits.Sigma.ι
          (fun J : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U J.1))
          I := by
  change
    (moduleSheafification (R := R) (T := T)).map
          (colimit.ι
            (Discrete.functor
              (fun J : Simplex (ι := ι) q =>
                yoneda.obj (intersection U J.1) ⋙
                  sigmaConst.obj (ModuleCat.of R R)))
            (Discrete.mk I)) ≫
      ((preservesColimitIso
          (moduleSheafification (R := R) (T := T))
          (Discrete.functor
            (fun J : Simplex (ι := ι) q =>
              yoneda.obj (intersection U J.1) ⋙
                sigmaConst.obj (ModuleCat.of R R)))).hom ≫
        (sheafifiedFiniteSubsetDiagramIso
          (R := R) U q).hom ≫
        (Limits.Sigma.mapIso
          (fun J : Simplex (ι := ι) q =>
            sheafifiedRepresentedSigmaIsoFreeModuleSheaf
              (R := R) (T := T)
              (intersection U J.1))).hom) =
    _
  rw [← Category.assoc, ← Category.assoc,
    ι_preservesColimitIso_hom]
  erw [colimit.ι_map]
  simp only [sheafifiedFiniteSubsetDiagramIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp]
  rw [Limits.Sigma.ι_mapIso_hom]

@[reassoc]
lemma finiteSubsetTerm_ι_comp_sheafifiedTermIso_inv
    (U : ι → Opens T) (q : ℕ)
    (I : Simplex (ι := ι) q) :
    Limits.Sigma.ι
          (fun J : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U J.1))
          I ≫
        (sheafifiedFiniteSubsetSigmaTermIso
          (R := R) U q).inv =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U I.1)).inv ≫
        (moduleSheafification (R := R) (T := T)).map
          (Limits.Sigma.ι
            (fun J : Simplex (ι := ι) q =>
              yoneda.obj (intersection U J.1) ⋙
                sigmaConst.obj (ModuleCat.of R R))
            I) := by
  let inj :
      (moduleSheafification (R := R) (T := T)).obj
          (yoneda.obj (intersection U I.1) ⋙
            sigmaConst.obj (ModuleCat.of R R)) ⟶
        (moduleSheafification (R := R) (T := T)).obj
          (finiteSubsetSigmaPresheafTerm (R := R) U q) :=
    (moduleSheafification (R := R) (T := T)).map
      (Limits.Sigma.ι
        (fun J : Simplex (ι := ι) q =>
          yoneda.obj (intersection U J.1) ⋙
            sigmaConst.obj (ModuleCat.of R R)) I)
  change
    Limits.Sigma.ι
          (fun J : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U J.1)) I ≫
        (sheafifiedFiniteSubsetSigmaTermIso
          (R := R) U q).inv =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U I.1)).inv ≫ inj
  apply (cancel_mono
    (sheafifiedFiniteSubsetSigmaTermIso
      (R := R) U q).hom).1
  rw [Category.assoc,
    (sheafifiedFiniteSubsetSigmaTermIso
      (R := R) U q).inv_hom_id,
    Category.comp_id]
  erw [Category.assoc]
  have hmap :=
    map_finiteSubsetSigma_ι_comp_sheafifiedTermIso
      (R := R) U q I
  change
    inj ≫ (sheafifiedFiniteSubsetSigmaTermIso
      (R := R) U q).hom =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
        (R := R) (T := T) (intersection U I.1)).hom ≫
        Limits.Sigma.ι
          (fun J : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U J.1)) I at hmap
  rw [hmap, Iso.inv_hom_id_assoc]

/-- Sheafification of the represented finite-subset presheaf
complex. -/
noncomputable def sheafifiedFiniteSubsetSigmaPresheafComplex
    (U : ι → Opens T) :
    ChainComplex (ModuleSheaf (R := R) T) ℕ :=
  ((moduleSheafification (R := R) (T := T)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj
      (finiteSubsetSigmaPresheafComplex (R := R) U)

/-- The sheafified represented finite-subset differential is the
existing free-sheaf alternating boundary. -/
lemma sheafifiedFiniteSubsetSigmaTermIso_comm_boundary
    (U : ι → Opens T) (q : ℕ) :
    (sheafifiedFiniteSubsetSigmaTermIso
        (R := R) U (q + 1)).hom ≫
      boundary (R := R) U q =
    (moduleSheafification (R := R) (T := T)).map
        (finiteSubsetSigmaPresheafBoundary
          (R := R) U q) ≫
      (sheafifiedFiniteSubsetSigmaTermIso
        (R := R) U q).hom := by
  apply (cancel_epi
    (sheafifiedFiniteSubsetSigmaTermIso
      (R := R) U (q + 1)).inv).1
  rw [(sheafifiedFiniteSubsetSigmaTermIso
      (R := R) U (q + 1)).inv_hom_id_assoc]
  apply Limits.Sigma.hom_ext
  intro J
  rw [boundary, Limits.Sigma.ι_desc]
  rw [finiteSubsetTerm_ι_comp_sheafifiedTermIso_inv_assoc]
  have houter :
      Limits.Sigma.ι
          (fun I : Simplex (ι := ι) (q + 1) =>
            yoneda.obj (intersection U I.1) ⋙
              sigmaConst.obj (ModuleCat.of R R))
          J ≫
        finiteSubsetSigmaPresheafBoundary
          (R := R) U q =
      finiteSubsetSigmaPresheafSimplexBoundary
        (R := R) U q J :=
    Limits.Sigma.ι_desc _ _
  let presheafInj :
      (yoneda.obj (intersection U J.1) ⋙
          sigmaConst.obj (ModuleCat.of R R)) ⟶
        finiteSubsetSigmaPresheafTerm (R := R) U (q + 1) :=
    Limits.Sigma.ι
      (fun I : Simplex (ι := ι) (q + 1) =>
        yoneda.obj (intersection U I.1) ⋙
          sigmaConst.obj (ModuleCat.of R R)) J
  let presheafSimplexBoundary :
      (yoneda.obj (intersection U J.1) ⋙
          sigmaConst.obj (ModuleCat.of R R)) ⟶
        finiteSubsetSigmaPresheafTerm (R := R) U q :=
    ∑ j : ↥J.1,
      insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
        (finiteSubsetSigmaPresheafFaceMap (R := R) U J j ≫
          finiteSubsetSummandι
            (R := R) U q (J.erase j.1 j.2))
  change
    presheafInj ≫
        finiteSubsetSigmaPresheafBoundary (R := R) U q =
      presheafSimplexBoundary at houter
  let inj :
      (moduleSheafification (R := R) (T := T)).obj
          (yoneda.obj (intersection U J.1) ⋙
            sigmaConst.obj (ModuleCat.of R R)) ⟶
        (moduleSheafification (R := R) (T := T)).obj
          (finiteSubsetSigmaPresheafTerm (R := R) U (q + 1)) :=
    (moduleSheafification (R := R) (T := T)).map presheafInj
  let mappedBoundary :
      (moduleSheafification (R := R) (T := T)).obj
          (finiteSubsetSigmaPresheafTerm (R := R) U (q + 1)) ⟶
        (moduleSheafification (R := R) (T := T)).obj
          (finiteSubsetSigmaPresheafTerm (R := R) U q) :=
    (moduleSheafification (R := R) (T := T)).map
      (finiteSubsetSigmaPresheafBoundary (R := R) U q)
  change
    simplexBoundary (R := R) U q J =
      ((sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U J.1)).inv ≫ inj) ≫
        mappedBoundary ≫
          (sheafifiedFiniteSubsetSigmaTermIso
            (R := R) U q).hom
  have houterMap :
      inj ≫ mappedBoundary =
        (moduleSheafification (R := R) (T := T)).map
          presheafSimplexBoundary := by
    dsimp only [inj, mappedBoundary]
    rw [← Functor.map_comp, houter]
  have houterMapFull :
      ((sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U J.1)).inv ≫ inj) ≫
        mappedBoundary ≫
          (sheafifiedFiniteSubsetSigmaTermIso
            (R := R) U q).hom =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U J.1)).inv ≫
        (moduleSheafification (R := R) (T := T)).map
          presheafSimplexBoundary ≫
          (sheafifiedFiniteSubsetSigmaTermIso
            (R := R) U q).hom := by
    rw [Category.assoc, reassoc_of% houterMap]
  rw [houterMapFull]
  dsimp only [presheafSimplexBoundary, simplexBoundary]
  rw [Functor.map_sum,
    Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  let E : Simplex (ι := ι) q := J.erase j.1 j.2
  rw [Functor.map_zsmul, ← Category.assoc,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  rw [Functor.map_comp]
  simp only [Category.assoc]
  let summandInj :
      (moduleSheafification (R := R) (T := T)).obj
          (yoneda.obj (intersection U E.1) ⋙
            sigmaConst.obj (ModuleCat.of R R)) ⟶
        (moduleSheafification (R := R) (T := T)).obj
          (finiteSubsetSigmaPresheafTerm (R := R) U q) :=
    (moduleSheafification (R := R) (T := T)).map
      (finiteSubsetSummandι (R := R) U q E)
  change
    faceMap (R := R) U J j ≫
        Limits.Sigma.ι
          (fun I : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U I.1)) E =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U J.1)).inv ≫
        (moduleSheafification (R := R) (T := T)).map
          (finiteSubsetSigmaPresheafFaceMap (R := R) U J j) ≫
          summandInj ≫
            (sheafifiedFiniteSubsetSigmaTermIso
              (R := R) U q).hom
  have hsummand :=
    map_finiteSubsetSigma_ι_comp_sheafifiedTermIso
      (R := R) U q E
  change
    summandInj ≫
        (sheafifiedFiniteSubsetSigmaTermIso
          (R := R) U q).hom =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U E.1)).hom ≫
        Limits.Sigma.ι
          (fun I : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U I.1)) E at hsummand
  rw [hsummand]
  dsimp only [finiteSubsetSigmaPresheafFaceMap]
  let inc : intersection U J.1 ⟶ intersection U E.1 :=
    homOfLE
      (intersection_anti U
        (Finset.erase_subset j.1 J.1))
  change
    freeModuleSheafMap (R := R) inc ≫
        Limits.Sigma.ι
          (fun I : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U I.1))
          E =
      (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U J.1)).inv ≫
        (moduleSheafification (R := R) (T := T)).map
          (Functor.whiskerRight (yoneda.map inc)
            (sigmaConst.obj (ModuleCat.of R R))) ≫
        (sheafifiedRepresentedSigmaIsoFreeModuleSheaf
          (R := R) (T := T) (intersection U E.1)).hom ≫
        Limits.Sigma.ι
          (fun I : Simplex (ι := ι) q =>
            freeModuleSheaf (R := R) (intersection U I.1))
          E
  rw [sheafifiedRepresentedSigmaIsoFreeModuleSheaf_naturality_assoc]
  rw [Iso.inv_hom_id_assoc]

/-- The sheafification of the represented finite-subset presheaf
complex is the existing finite-subset free sheaf complex. -/
noncomputable def sheafifiedFiniteSubsetSigmaPresheafComplexIso
    (U : ι → Opens T) :
    sheafifiedFiniteSubsetSigmaPresheafComplex (R := R) U ≅
      complex (R := R) U :=
  HomologicalComplex.Hom.isoOfComponents
    (sheafifiedFiniteSubsetSigmaTermIso (R := R) U)
    (by
      rintro i j (rfl : j + 1 = i)
      dsimp [complex]
      simp only [ChainComplex.of_d]
      let mappedBoundary :
          (sheafifiedFiniteSubsetSigmaPresheafComplex
              (R := R) U).X (j + 1) ⟶
            (sheafifiedFiniteSubsetSigmaPresheafComplex
              (R := R) U).X j :=
        (moduleSheafification (R := R) (T := T)).map
          (finiteSubsetSigmaPresheafBoundary (R := R) U j)
      have hd :
          (sheafifiedFiniteSubsetSigmaPresheafComplex
              (R := R) U).d (j + 1) j = mappedBoundary := by
        dsimp [sheafifiedFiniteSubsetSigmaPresheafComplex,
          finiteSubsetSigmaPresheafComplex, mappedBoundary]
        simp only [ChainComplex.of_d,
          Functor.mapHomologicalComplex_obj_d]
        rfl
      rw [hd]
      change
        (sheafifiedFiniteSubsetSigmaTermIso
            (R := R) U (j + 1)).hom ≫
            boundary (R := R) U j =
          mappedBoundary ≫
            (sheafifiedFiniteSubsetSigmaTermIso
              (R := R) U j).hom
      have h :=
        sheafifiedFiniteSubsetSigmaTermIso_comm_boundary
          (R := R) U j
      change
        (sheafifiedFiniteSubsetSigmaTermIso
            (R := R) U (j + 1)).hom ≫
            boundary (R := R) U j =
          mappedBoundary ≫
            (sheafifiedFiniteSubsetSigmaTermIso
              (R := R) U j).hom at h
      exact h)

/-- The exact sheafified ordered-cover complex is isomorphic, as a
chain complex, to the existing finite-subset free sheaf complex. -/
noncomputable def sheafifiedOrderedCoverComplexIsoFiniteSubset
    (U : ι → Opens T) :
    sheafifiedOrderedCoverComplex (R := R) U ≅
      complex (R := R) U :=
  ((moduleSheafification
      (R := R) (T := T)).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapIso
      (orderedCoverNormalizedPresheafComplexIsoFiniteSubset
        (R := R) U) ≪≫
    sheafifiedFiniteSubsetSigmaPresheafComplexIso
      (R := R) U

/-- Positive-degree exactness of the existing finite-subset free
sheaf complex. -/
theorem finiteSubsetFreeSheafComplex_exactAt_succ
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (complex (R := R) U).ExactAt (n + 1) :=
  (sheafifiedOrderedCoverComplex_exactAt_succ
    (R := R) U hU n).of_iso
      (sheafifiedOrderedCoverComplexIsoFiniteSubset
        (R := R) U)

/-- The finite-subset complex augmentation transported from the exact
ordered-cover resolution. -/
noncomputable def finiteSubsetFreeSheafAugmentationToConstant
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    complex (R := R) U ⟶
      (ChainComplex.single₀
        (ModuleSheaf (R := R) T)).obj
          (constantRankOneSheaf (R := R) T) :=
  (sheafifiedOrderedCoverComplexIsoFiniteSubset
      (R := R) U).inv ≫
    sheafifiedOrderedCoverAugmentationToConstant
      (R := R) U hU

/-- The transported augmentation of the existing finite-subset
complex is a quasi-isomorphism. -/
theorem finiteSubsetFreeSheafAugmentationToConstant_quasiIso
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    QuasiIso
      (finiteSubsetFreeSheafAugmentationToConstant
        (R := R) U hU) := by
  let e :=
    sheafifiedOrderedCoverComplexIsoFiniteSubset
      (R := R) U
  letI h₁ : QuasiIso e.inv := inferInstance
  letI h₂ : QuasiIso
      (sheafifiedOrderedCoverAugmentationToConstant
        (R := R) U hU) :=
    sheafifiedOrderedCoverAugmentationToConstant_quasiIso
      (R := R) U hU
  exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
