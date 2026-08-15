/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafBoundary

/-!
# Hom out of the normalized finite-subset free-sheaf terms

Maps from the sheafified free module represented by an open are the
sections on that open.  This file upgrades that adjunction to an
`R`-linear equivalence and applies it to every finite coproduct term of
the normalized finite-subset Čech source.
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

/-- Maps from the free module sheaf represented by `V` are sections on
`V`. -/
noncomputable def freeModuleSheafHomEquiv (V : Opens T)
    (F : ModuleSheaf (R := R) T) :
    (freeModuleSheaf (R := R) V ⟶ F) ≃ F.obj.obj (op V) :=
  ((sheafificationAdjunction _ _).homEquiv
      (yoneda.obj V ⋙ ModuleCat.free R) F).trans <|
    ((ModuleCat.adj R).whiskerRight _).homEquiv
      (yoneda.obj V)
      ((sheafToPresheaf _ _).obj F) |>.trans yonedaEquiv

/-- The Hom--sections equivalence commutes with restriction along an
inclusion of opens. -/
lemma freeModuleSheafHomEquiv_naturality {V W : Opens T}
    (i : V ⟶ W) (F : ModuleSheaf (R := R) T)
    (f : freeModuleSheaf (R := R) W ⟶ F) :
    freeModuleSheafHomEquiv V F
        (freeModuleSheafMap (R := R) i ≫ f) =
      F.obj.map i.op (freeModuleSheafHomEquiv W F f) := by
  let L := presheafToSheaf
    (_root_.Opens.grothendieckTopology T) (ModuleCat.{u} R)
  let U := sheafToPresheaf
    (_root_.Opens.grothendieckTopology T) (ModuleCat.{u} R)
  let PV := yoneda.obj V ⋙ ModuleCat.free R
  let PW := yoneda.obj W ⋙ ModuleCat.free R
  let u : PV ⟶ PW :=
    Functor.whiskerRight (yoneda.map i) (ModuleCat.free R)
  let adjS := sheafificationAdjunction
    (_root_.Opens.grothendieckTopology T) (ModuleCat.{u} R)
  let adjM := (ModuleCat.adj R).whiskerRight (Opens T)ᵒᵖ
  let g : PW ⟶ U.obj F :=
    adjS.homEquiv PW F f
  let h : yoneda.obj W ⟶
      ((U.obj F) ⋙ forget (ModuleCat R)) :=
    adjM.homEquiv (yoneda.obj W) (U.obj F) g
  have hS :
      adjS.homEquiv PV F (L.map u ≫ f) = u ≫ g :=
    adjS.homEquiv_naturality_left u f
  have hM :
      adjM.homEquiv (yoneda.obj V) (U.obj F) (u ≫ g) =
        yoneda.map i ≫ h := by
    simpa only [Functor.whiskeringRight_obj_map] using
      adjM.homEquiv_naturality_left (yoneda.map i) g
  have hY :
      yonedaEquiv (yoneda.map i ≫ h) =
        F.obj.map i.op (yonedaEquiv h) :=
    (yonedaEquiv_naturality h i).symm
  change
    yonedaEquiv
      (adjM.homEquiv (yoneda.obj V) (U.obj F)
        (adjS.homEquiv PV F (L.map u ≫ f))) =
      F.obj.map i.op
        (yonedaEquiv
          (adjM.homEquiv (yoneda.obj W) (U.obj F)
            (adjS.homEquiv PW F f)))
  rw [hS, hM]
  exact hY

/-- The Hom--sections equivalence is linear over the constant
coefficient ring. -/
noncomputable def freeModuleSheafHomLinearEquiv (V : Opens T)
    (F : ModuleSheaf (R := R) T) :
    (freeModuleSheaf (R := R) V ⟶ F) ≃ₗ[R]
      F.obj.obj (op V) where
  toEquiv := freeModuleSheafHomEquiv V F
  map_add' f g := by
    change freeModuleSheafHomEquiv V F (f + g) =
      freeModuleSheafHomEquiv V F f +
        freeModuleSheafHomEquiv V F g
    rfl
  map_smul' r f := by
    change freeModuleSheafHomEquiv V F (r • f) =
      r • freeModuleSheafHomEquiv V F f
    rfl

/-- A map out of a coproduct is linearly equivalent to a family of maps
out of its summands. -/
noncomputable def sigmaHomLinearEquiv
    {β : Type u} [Fintype β]
    (X : β → ModuleSheaf (R := R) T)
    (F : ModuleSheaf (R := R) T)
    [HasCoproduct X] :
    ((∐ X) ⟶ F) ≃ₗ[R] ((i : β) → (X i ⟶ F)) where
  toFun f i := Limits.Sigma.ι X i ≫ f
  invFun f := Limits.Sigma.desc f
  left_inv f := by
    apply Limits.Sigma.hom_ext
    intro i
    exact Limits.Sigma.ι_desc _ _
  right_inv f := by
    funext i
    exact Limits.Sigma.ι_desc _ _
  map_add' f g := by
    funext i
    simp
  map_smul' r f := by
    funext i
    simp

/-- The section module attached to one finite intersection. -/
abbrev sectionModule
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (I : Finset ι) : Type u :=
  F.obj.obj (op (intersection U I))

/-- Restriction of sections when the set of open indices is enlarged. -/
noncomputable def sectionRestriction
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    {I J : Finset ι} (h : I ⊆ J) :
    sectionModule U F I →ₗ[R] sectionModule U F J :=
  (F.obj.map
    (homOfLE (intersection_anti U h)).op).hom

lemma sectionRestriction_comp
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    {I J K : Finset ι}
    (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : sectionModule U F I) :
    sectionRestriction U F hJK
        (sectionRestriction U F hIJ x) =
      sectionRestriction U F (hIJ.trans hJK) x := by
  change
    (F.obj.map (homOfLE (intersection_anti U hIJ)).op ≫
      F.obj.map (homOfLE (intersection_anti U hJK)).op) x =
      F.obj.map
        (homOfLE (intersection_anti U (hIJ.trans hJK))).op x
  rw [← F.obj.map_comp]
  congr 1

/-- The normalized finite-subset section Čech complex. -/
noncomputable def sectionCechComplex
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) :
    CochainComplex (ModuleCat R) ℕ :=
  finiteSubsetCechComplex
    (sectionModule U F)
    (sectionRestriction U F)
    (sectionRestriction_comp U F)

/-- Degreewise, contravariant Hom out of a normalized free-sheaf term
is the finite-subset module of sections on the corresponding
intersections. -/
noncomputable def termHomLinearEquiv
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) (q : ℕ) :
    (term (R := R) U q ⟶ F) ≃ₗ[R]
      FiniteSubsetCochain (sectionModule U F) q :=
  (sigmaHomLinearEquiv
      (fun I : Simplex (ι := ι) q =>
        simplexSheaf (R := R) U I) F).trans <|
    (LinearEquiv.piCongrRight
      (fun I : Simplex (ι := ι) q =>
        freeModuleSheafHomLinearEquiv
          (intersection U I.1) F)).trans <|
      (DFinsupp.linearEquivFunOnFintype (R := R)).symm

@[simp]
lemma termHomLinearEquiv_apply
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) (f : term (R := R) U q ⟶ F)
    (I : Simplex (ι := ι) q) :
    termHomLinearEquiv U F q f I =
      freeModuleSheafHomLinearEquiv
        (intersection U I.1) F
        (Limits.Sigma.ι
          (fun J : Simplex (ι := ι) q =>
            simplexSheaf (R := R) U J) I ≫ f) :=
  rfl

/-- For a finite index type, the finite-support presentation of
normalized cochains is linearly equivalent to the corresponding finite
product. -/
noncomputable def termHomPiLinearEquiv
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) (q : ℕ) :
    (term (R := R) U q ⟶ F) ≃ₗ[R]
      ((I : Simplex (ι := ι) q) → sectionModule U F I.1) :=
  (termHomLinearEquiv U F q).trans
    (DFinsupp.linearEquivFunOnFintype (R := R))

@[simp]
lemma termHomPiLinearEquiv_apply
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) (f : term (R := R) U q ⟶ F)
    (I : Simplex (ι := ι) q) :
    termHomPiLinearEquiv U F q f I =
      freeModuleSheafHomLinearEquiv
        (intersection U I.1) F
        (Limits.Sigma.ι
          (fun J : Simplex (ι := ι) q =>
            simplexSheaf (R := R) U J) I ≫ f) :=
  rfl

/-- The target-oriented alternating differential on normalized
finite-subset section cochains. -/
noncomputable def sectionPiDifferential
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) :
    ((I : Simplex (ι := ι) q) → sectionModule U F I.1) →ₗ[R]
      ((J : Simplex (ι := ι) (q + 1)) →
        sectionModule U F J.1) :=
  LinearMap.pi fun J =>
    ∑ j : ↥J.1,
      insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
        ((sectionRestriction U F
          (Finset.erase_subset j.1 J.1)).comp
            (LinearMap.proj (R := R)
              (J.erase j.1 j.2)))

@[simp]
lemma sectionPiDifferential_apply
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ)
    (x : (I : Simplex (ι := ι) q) →
      sectionModule U F I.1)
    (J : Simplex (ι := ι) (q + 1)) :
    sectionPiDifferential U F q x J =
      ∑ j : ↥J.1,
        insertionSign (R := ℤ) (J.1.erase j.1) j.1 •
          sectionRestriction U F
            (Finset.erase_subset j.1 J.1)
            (x (J.erase j.1 j.2)) := by
  simp [sectionPiDifferential]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- Precomposing by the source boundary becomes the usual
target-oriented alternating restriction differential on sections. -/
lemma termHomPiLinearEquiv_boundary
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) (f : term (R := R) U q ⟶ F) :
    termHomPiLinearEquiv U F (q + 1)
        (boundary (R := R) U q ≫ f) =
      sectionPiDifferential U F q
        (termHomPiLinearEquiv U F q f) := by
  funext J
  rw [sectionPiDifferential_apply]
  rw [termHomPiLinearEquiv_apply]
  change freeModuleSheafHomLinearEquiv
      (intersection U J.1) F
      ((Limits.Sigma.ι
          (fun K : Simplex (ι := ι) (q + 1) =>
            simplexSheaf (R := R) U K) J ≫
        boundary (R := R) U q) ≫ f) = _
  rw [boundary, Limits.Sigma.ι_desc, simplexBoundary,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact freeModuleSheafHomEquiv_naturality
    (homOfLE
      (intersection_anti U
        (Finset.erase_subset j.1 J.1)))
    F
    (Limits.Sigma.ι
      (fun I : Simplex (ι := ι) q =>
        simplexSheaf (R := R) U I)
      (J.erase j.1 j.2) ≫ f)

/-- Precomposition by one normalized source boundary, as a linear map
between the corresponding Hom modules. -/
noncomputable def contravariantHomDifferential
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) :
    (term (R := R) U q ⟶ F) →ₗ[R]
      (term (R := R) U (q + 1) ⟶ F) where
  toFun f := boundary (R := R) U q ≫ f
  map_add' f g := by simp
  map_smul' r f := by simp

@[simp]
lemma contravariantHomDifferential_apply
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) (f : term (R := R) U q ⟶ F) :
    contravariantHomDifferential U F q f =
      boundary (R := R) U q ≫ f :=
  rfl

lemma contravariantHomDifferential_comp
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) :
    (contravariantHomDifferential U F (q + 1)).comp
        (contravariantHomDifferential U F q) = 0 := by
  apply LinearMap.ext
  intro f
  change
    boundary (R := R) U (q + 1) ≫
        boundary (R := R) U q ≫ f = 0
  rw [← Category.assoc, boundary_comp, zero_comp]

/-- The contravariant Hom cocomplex of the normalized free-sheaf
source complex against `F`. -/
noncomputable def contravariantHomCocomplex
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R (term (R := R) U q ⟶ F))
    (fun q => ModuleCat.ofHom
      (contravariantHomDifferential U F q))
    (fun q => by
      apply ModuleCat.hom_ext
      exact contravariantHomDifferential_comp U F q)

lemma sectionPiDifferential_comp
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T)
    (q : ℕ) :
    (sectionPiDifferential U F (q + 1)).comp
        (sectionPiDifferential U F q) = 0 := by
  apply LinearMap.ext
  intro x
  change sectionPiDifferential U F (q + 1)
      (sectionPiDifferential U F q x) = 0
  rw [← (termHomPiLinearEquiv U F q).apply_symm_apply x]
  rw [← termHomPiLinearEquiv_boundary]
  rw [← termHomPiLinearEquiv_boundary]
  change termHomPiLinearEquiv U F (q + 2)
    ((boundary (R := R) U (q + 1) ≫
      boundary (R := R) U q) ≫
        (termHomPiLinearEquiv U F q).symm x) = 0
  rw [boundary_comp, zero_comp, map_zero]

/-- The normalized finite-subset section Čech complex, in its
target-oriented finite-product presentation. -/
noncomputable def sectionPiCechComplex
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of R
      ((I : Simplex (ι := ι) q) →
        sectionModule U F I.1))
    (fun q => ModuleCat.ofHom
      (sectionPiDifferential U F q))
    (fun q => by
      apply ModuleCat.hom_ext
      exact sectionPiDifferential_comp U F q)

/-- Contravariant Hom out of the normalized finite-subset free-sheaf
complex is the normalized section Čech complex. -/
noncomputable def contravariantHomCocomplexIsoSectionPiCech
    (U : ι → Opens T) (F : ModuleSheaf (R := R) T) :
    contravariantHomCocomplex U F ≅ sectionPiCechComplex U F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (termHomPiLinearEquiv U F q).toModuleIso)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [sectionPiCechComplex,
        contravariantHomCocomplex, CochainComplex.of_d]
      change sectionPiDifferential U F i
          (termHomPiLinearEquiv U F i f) =
        termHomPiLinearEquiv U F (i + 1)
          (boundary (R := R) U i ≫ f)
      exact (termHomPiLinearEquiv_boundary U F i f).symm)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
