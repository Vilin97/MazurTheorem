/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafResolutionSheafified
import Mathlib.Data.Finset.Sort

/-!
# Finite-subset description of ordered-cover nondegenerate simplices

A nondegenerate simplex in the nerve of the ordered set of cover
members containing a test open is exactly a finite subset of cover
indices of the corresponding cardinality whose intersection contains
the test open.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {R : Type u} [CommRing R]
variable {T : TopCat.{u}}
variable {ι : Type u} [Fintype ι] [LinearOrder ι]

local instance availableCoverIndexLinearOrder
    (U : ι → Opens T) (V : Opens T) :
    LinearOrder (CoverIndex U V) :=
  LinearOrder.lift' (fun i => i.1)
    (fun _ _ h => Subtype.ext h)

local instance availableCoverIndexCategory
    (U : ι → Opens T) (V : Opens T) :
    SmallCategory (CoverIndex U V) :=
  Preorder.smallCategory _

/-- A finite subset of cover indices of dimension `q` which is
available at the test open `V`. -/
abbrev AvailableSimplex
    (U : ι → Opens T) (V : Opens T) (q : ℕ) :=
  {I : Simplex (ι := ι) q // V ≤ intersection U I.1}

/-- The finite subset underlying a nondegenerate ordered-nerve
simplex. -/
def nondegenerateToAvailableSimplex
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate q) :
    AvailableSimplex U V q := by
  let s : Finset ι :=
    Finset.univ.image (fun j : Fin (q + 1) => (x.1.obj j).1)
  have hinj :
      Function.Injective
        (fun j : Fin (q + 1) => (x.1.obj j).1) := by
    intro a b hab
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_injective
      x.1).mp x.2
    apply Subtype.ext
    exact hab
  have hcard : s.card = q + 1 := by
    rw [Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  refine ⟨⟨s, hcard⟩, ?_⟩
  refine le_iInf fun i => le_iInf fun hi => ?_
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact (x.1.obj j).2

/-- Enumerate an available finite subset increasingly to obtain a
nondegenerate ordered-nerve simplex. -/
def availableSimplexToNondegenerate
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (I : AvailableSimplex U V q) :
    (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate q := by
  let e : Fin (q + 1) ↪o ι :=
    I.1.1.orderEmbOfFin I.1.2
  let f : Fin (q + 1) →o CoverIndex U V :=
    { toFun := fun j =>
        ⟨e j, le_iInf_iff.mp I.2 (e j) |>
          fun h => le_iInf_iff.mp h
            (I.1.1.orderEmbOfFin_mem I.1.2 j)⟩
      monotone' := fun _ _ h => e.monotone h }
  let s : (CategoryTheory.nerve (CoverIndex U V)).obj
      (op (SimplexCategory.mk q)) := f.monotone.functor
  refine ⟨s, (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).2 ?_⟩
  intro a b hab
  exact e.strictMono hab

/-- Nondegenerate ordered-cover simplices are naturally indexed by
available finite subsets. -/
def nondegenerateAvailableSimplexEquiv
    (U : ι → Opens T) (V : Opens T) (q : ℕ) :
    (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate q ≃
      AvailableSimplex U V q where
  toFun := nondegenerateToAvailableSimplex U V q
  invFun := availableSimplexToNondegenerate U V q
  left_inv x := by
    apply Subtype.ext
    apply CategoryTheory.nerve.ext_of_isThin
    funext j
    apply Subtype.ext
    let s : Finset ι :=
      Finset.univ.image
        (fun k : Fin (q + 1) => (x.1.obj k).1)
    have hxstrict :
        StrictMono (fun k : Fin (q + 1) => (x.1.obj k).1) :=
      fun _ _ h =>
        (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono
          x.1).mp x.2 h
    let ex : Fin (q + 1) ↪o ι :=
      OrderEmbedding.ofStrictMono _ hxstrict
    have hcard : s.card = q + 1 := by
      rw [Finset.card_image_of_injective _
        hxstrict.injective, Finset.card_univ, Fintype.card_fin]
    have hex :
        ex = s.orderEmbOfFin hcard :=
      Finset.orderEmbOfFin_unique' hcard (fun k => by
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
    change (s.orderEmbOfFin hcard) j = (x.1.obj j).1
    exact congrArg (fun e : Fin (q + 1) ↪o ι => e j) hex.symm
  right_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [availableSimplexToNondegenerate,
      nondegenerateToAvailableSimplex]
    exact Finset.image_orderEmbOfFin_univ I.1.1 I.1.2

/-- An available finite subset is equivalently a finite subset together
with the unique inclusion of the test open into its intersection. -/
def availableSimplexSigmaHomEquiv
    (U : ι → Opens T) (V : Opens T) (q : ℕ) :
    AvailableSimplex U V q ≃
      Σ I : Simplex (ι := ι) q, (V ⟶ intersection U I.1) where
  toFun I := ⟨I.1, homOfLE I.2⟩
  invFun I := ⟨I.1, leOfHom I.2⟩
  left_inv I := by
    apply Subtype.ext
    rfl
  right_inv I := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subsingleton.elim

/-- Restrict an available finite subset along an inclusion of test
opens. -/
def AvailableSimplex.map
    (U : ι → Opens T) {V W : (Opens T)ᵒᵖ}
    (f : V ⟶ W) (q : ℕ) :
    AvailableSimplex U V.unop q →
      AvailableSimplex U W.unop q :=
  fun I => ⟨I.1, (leOfHom f.unop).trans I.2⟩

@[simp]
lemma AvailableSimplex.map_val
    (U : ι → Opens T) {V W : (Opens T)ᵒᵖ}
    (f : V ⟶ W) (q : ℕ)
    (I : AvailableSimplex U V.unop q) :
    (AvailableSimplex.map U f q I).1 = I.1 :=
  rfl

/-- The coproduct of coefficient objects indexed by available finite
subsets, functorial in the test open. -/
noncomputable def availableSimplexTermFunctor
    (U : ι → Opens T) (q : ℕ) :
    (Opens T)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj V :=
    ∐ fun _ : AvailableSimplex U V.unop q =>
      ModuleCat.of R R
  map {V W} f :=
    Limits.Sigma.map' (AvailableSimplex.map U f q)
      (fun _ => 𝟙 (ModuleCat.of R R))
  map_id V := by
    rw [← Limits.Sigma.map'_id_id]
    apply Limits.Sigma.map'_eq
    · intro I
      simp
    · funext I
      apply Subtype.ext
      rfl
  map_comp f g := by
    rw [Limits.Sigma.map'_comp_map']
    apply Limits.Sigma.map'_eq
    · intro I
      simp
    · funext I
      apply Subtype.ext
      rfl

/-- The coproduct injection associated to one available simplex. -/
noncomputable def availableSimplexGenerator
    (U : ι → Opens T) (q : ℕ) (V : (Opens T)ᵒᵖ)
    (A : AvailableSimplex U V.unop q) :
    ModuleCat.of R R ⟶
      (availableSimplexTermFunctor (R := R) U q).obj V :=
  Limits.Sigma.ι
    (fun _ : AvailableSimplex U V.unop q => ModuleCat.of R R) A

/-- Descend a family of maps from the available-simplex summands. -/
noncomputable def availableSimplexDesc
    (U : ι → Opens T) (q : ℕ) (V : (Opens T)ᵒᵖ)
    (X : ModuleCat.{u} R)
    (p : ∀ A : AvailableSimplex U V.unop q,
      ModuleCat.of R R ⟶ X) :
    (availableSimplexTermFunctor (R := R) U q).obj V ⟶ X :=
  Limits.Sigma.desc p

@[reassoc]
lemma availableSimplexGenerator_map
    (U : ι → Opens T) (q : ℕ) {V W : (Opens T)ᵒᵖ}
    (f : V ⟶ W) (A : AvailableSimplex U V.unop q) :
    availableSimplexGenerator (R := R) U q V A ≫
        (availableSimplexTermFunctor (R := R) U q).map f =
      availableSimplexGenerator (R := R) U q W
        (AvailableSimplex.map U f q A) := by
  dsimp only [availableSimplexGenerator,
    availableSimplexTermFunctor]
  rw [Limits.Sigma.ι_comp_map']
  simp

@[reassoc]
lemma availableSimplexGenerator_comp_desc
    (U : ι → Opens T) (q : ℕ) (V : (Opens T)ᵒᵖ)
    (X : ModuleCat.{u} R)
    (p : ∀ A : AvailableSimplex U V.unop q,
      ModuleCat.of R R ⟶ X)
    (A : AvailableSimplex U V.unop q) :
    availableSimplexGenerator (R := R) U q V A ≫
        availableSimplexDesc (R := R) U q V X p = p A := by
  exact Limits.Sigma.ι_desc p A

universe vC uC

/-- Reindex a coproduct of copies of one object along an equivalence of
indexing types. -/
noncomputable def coproductConstEquivIso
    {C : Type uC} [Category.{vC} C]
    [HasCoproducts.{u} C]
    {α β : Type u} (e : α ≃ β) (M : C) :
    (∐ fun _ : α => M) ≅ (∐ fun _ : β => M) where
  hom := Limits.Sigma.desc fun a =>
    Limits.Sigma.ι (fun _ : β => M) (e a)
  inv := Limits.Sigma.desc fun b =>
    Limits.Sigma.ι (fun _ : α => M) (e.symm b)
  hom_inv_id := by
    apply Limits.Sigma.hom_ext
    intro a
    rw [← Category.assoc, Limits.Sigma.ι_desc,
      Limits.Sigma.ι_desc, e.symm_apply_apply,
      Category.comp_id]
  inv_hom_id := by
    apply Limits.Sigma.hom_ext
    intro b
    rw [← Category.assoc, Limits.Sigma.ι_desc,
      Limits.Sigma.ι_desc, e.apply_symm_apply,
      Category.comp_id]

/-- In each degree, normalized chains are the coproduct of their
nondegenerate simplex summands. -/
noncomputable def normalizedTermIsoNondegenerate
    (X : SSet.{u}) (q : ℕ) :
    (X.normalizedChainComplex (ModuleCat.of R R)).X q ≅
      ∐ fun _ : X.nonDegenerate q => ModuleCat.of R R :=
  (X.isColimitCofanNormalizedChainComplex
    (ModuleCat.of R R) q).coconePointUniqueUpToIso
      (Limits.coproductIsCoproduct _)

/-- The evaluated normalized term is a coproduct indexed by the
available finite subsets. -/
noncomputable def evaluatedNormalizedTermIsoAvailable
    (U : ι → Opens T) (V : Opens T) (q : ℕ) :
    ((CategoryTheory.nerve
      (CoverIndex U V)).normalizedChainComplex
        (ModuleCat.of R R)).X q ≅
      ∐ fun _ : AvailableSimplex U V q =>
        ModuleCat.of R R :=
  normalizedTermIsoNondegenerate
      (R := R) (CategoryTheory.nerve (CoverIndex U V)) q ≪≫
    coproductConstEquivIso
      (nondegenerateAvailableSimplexEquiv U V q)
      (ModuleCat.of R R)

/-- Expanded form of the evaluated normalized term: first choose a
finite subset, then a represented inclusion of the test open into its
intersection. -/
noncomputable def evaluatedNormalizedTermIsoFiniteSubset
    (U : ι → Opens T) (V : Opens T) (q : ℕ) :
    ((CategoryTheory.nerve
      (CoverIndex U V)).normalizedChainComplex
        (ModuleCat.of R R)).X q ≅
      ∐ fun I : Simplex (ι := ι) q =>
        ∐ fun _ : (V ⟶ intersection U I.1) =>
          ModuleCat.of R R :=
  evaluatedNormalizedTermIsoAvailable
      (R := R) U V q ≪≫
    coproductConstEquivIso
      (availableSimplexSigmaHomEquiv U V q)
      (ModuleCat.of R R) ≪≫
    (Limits.sigmaSigmaIso
      (fun I : Simplex (ι := ι) q =>
        (V ⟶ intersection U I.1))
      (fun _ _ => ModuleCat.of R R)).symm

/-- The finite-subset presheaf term using coproducts of copies of the
coefficient object. -/
noncomputable def finiteSubsetSigmaPresheafTerm
    (U : ι → Opens T) (q : ℕ) :
    (Opens T)ᵒᵖ ⥤ ModuleCat.{u} R :=
  ∐ fun I : Simplex (ι := ι) q =>
    yoneda.obj (intersection U I.1) ⋙
      sigmaConst.obj (ModuleCat.of R R)

/-- The outer coproduct injection for one finite subset. -/
noncomputable def finiteSubsetSummandι
    (U : ι → Opens T) (q : ℕ)
    (I : Simplex (ι := ι) q) :
    yoneda.obj (intersection U I.1) ⋙
        sigmaConst.obj (ModuleCat.of R R) ⟶
      finiteSubsetSigmaPresheafTerm (R := R) U q :=
  Limits.Sigma.ι
    (fun J : Simplex (ι := ι) q =>
      yoneda.obj (intersection U J.1) ⋙
        sigmaConst.obj (ModuleCat.of R R)) I

/-- Descend a family of natural transformations from the finite-subset
summands. -/
noncomputable def finiteSubsetSigmaDesc
    (U : ι → Opens T) (q : ℕ)
    {G : CategoryTheory.Functor (Opens T)ᵒᵖ (ModuleCat.{u} R)}
    (p : ∀ I : Simplex (ι := ι) q,
      yoneda.obj (intersection U I.1) ⋙
        sigmaConst.obj (ModuleCat.of R R) ⟶ G) :
    finiteSubsetSigmaPresheafTerm (R := R) U q ⟶ G :=
  Limits.Sigma.desc p

@[reassoc]
lemma finiteSubsetSummandι_comp_desc
    (U : ι → Opens T) (q : ℕ)
    {G : CategoryTheory.Functor (Opens T)ᵒᵖ (ModuleCat.{u} R)}
    (p : ∀ I : Simplex (ι := ι) q,
      yoneda.obj (intersection U I.1) ⋙
        sigmaConst.obj (ModuleCat.of R R) ⟶ G)
    (I : Simplex (ι := ι) q) :
    finiteSubsetSummandι (R := R) U q I ≫
        finiteSubsetSigmaDesc (R := R) U q p = p I := by
  exact Limits.Sigma.ι_desc p I

/-- The generator of a represented-intersection summand. -/
noncomputable def representedIntersectionGenerator
    (U : ι → Opens T) (I : Simplex (ι := ι) q)
    (V : (Opens T)ᵒᵖ)
    (h : (yoneda.obj (intersection U I.1)).obj V) :
    ModuleCat.of R R ⟶
      (yoneda.obj (intersection U I.1) ⋙
        sigmaConst.obj (ModuleCat.of R R)).obj V :=
  Limits.Sigma.ι
    (fun _ : (yoneda.obj (intersection U I.1)).obj V =>
      ModuleCat.of R R) h

/-- Descend a family of maps from the generators of one represented
intersection. -/
noncomputable def representedIntersectionDesc
    (U : ι → Opens T) (I : Simplex (ι := ι) q)
    (V : (Opens T)ᵒᵖ) (X : ModuleCat.{u} R)
    (p : ∀ h : (yoneda.obj (intersection U I.1)).obj V,
      ModuleCat.of R R ⟶ X) :
    (yoneda.obj (intersection U I.1) ⋙
        sigmaConst.obj (ModuleCat.of R R)).obj V ⟶ X :=
  Limits.Sigma.desc p

@[reassoc]
lemma representedIntersectionGenerator_comp_desc
    (U : ι → Opens T) (I : Simplex (ι := ι) q)
    (V : (Opens T)ᵒᵖ) (X : ModuleCat.{u} R)
    (p : ∀ h : (yoneda.obj (intersection U I.1)).obj V,
      ModuleCat.of R R ⟶ X)
    (h : (yoneda.obj (intersection U I.1)).obj V) :
    representedIntersectionGenerator (R := R) U I V h ≫
        representedIntersectionDesc (R := R) U I V X p = p h := by
  exact Limits.Sigma.ι_desc p h

@[reassoc]
lemma representedIntersectionGenerator_map
    (U : ι → Opens T) (I : Simplex (ι := ι) q)
    {V W : (Opens T)ᵒᵖ} (f : V ⟶ W)
    (h : (yoneda.obj (intersection U I.1)).obj V) :
    representedIntersectionGenerator (R := R) U I V h ≫
        (yoneda.obj (intersection U I.1) ⋙
          sigmaConst.obj (ModuleCat.of R R)).map f =
      representedIntersectionGenerator (R := R) U I W
        ((yoneda.obj (intersection U I.1)).map f h) := by
  dsimp only [representedIntersectionGenerator,
    Functor.comp_map, sigmaConst]
  rw [Limits.Sigma.ι_comp_map']
  simp

/-- The map on nondegenerate simplices induced by restricting the test
open.  The ordered-cover restriction is injective on objects, hence it
cannot turn a nondegenerate simplex into a degenerate one. -/
def orderedCoverNondegenerateMap
    (U : ι → Opens T) {V W : (Opens T)ᵒᵖ}
    (f : V ⟶ W) (q : ℕ) :
    (CategoryTheory.nerve
      (CoverIndex U V.unop)).nonDegenerate q →
      (CategoryTheory.nerve
        (CoverIndex U W.unop)).nonDegenerate q := by
  intro x
  let y : (CategoryTheory.nerve
      (CoverIndex U W.unop)).obj
        (op (SimplexCategory.mk q)) :=
    (CategoryTheory.nerveMap
      (coverIndexRestriction U f)).app _ x.1
  refine ⟨y, (PartialOrder.mem_nerve_nonDegenerate_iff_injective y).2 ?_⟩
  intro a b hab
  apply (PartialOrder.mem_nerve_nonDegenerate_iff_injective
    x.1).mp x.2
  apply Subtype.ext
  change
    (coverIndexRestriction U f).obj (x.1.obj a) =
      (coverIndexRestriction U f).obj (x.1.obj b) at hab
  exact congrArg
    (fun z : CoverIndex U W.unop => z.1) hab

@[simp]
lemma orderedCoverNondegenerateMap_val
    (U : ι → Opens T) {V W : (Opens T)ᵒᵖ}
    (f : V ⟶ W) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V.unop)).nonDegenerate q) :
    (orderedCoverNondegenerateMap U f q x).1 =
      (CategoryTheory.nerveMap
        (coverIndexRestriction U f)).app _ x.1 :=
  rfl

@[simp]
lemma nondegenerateToAvailableSimplex_naturality
    (U : ι → Opens T) {V W : (Opens T)ᵒᵖ}
    (f : V ⟶ W) (q : ℕ)
    (x : (CategoryTheory.nerve
      (CoverIndex U V.unop)).nonDegenerate q) :
    nondegenerateToAvailableSimplex U W.unop q
        (orderedCoverNondegenerateMap U f q x) =
      AvailableSimplex.map U f q
        (nondegenerateToAvailableSimplex U V.unop q x) := by
  apply Subtype.ext
  apply Subtype.ext
  dsimp only [nondegenerateToAvailableSimplex,
    AvailableSimplex.map]
  apply Finset.image_congr
  intro j _
  rfl

@[reassoc]
lemma ι_evaluatedNormalizedTermIsoAvailable_hom
    (U : ι → Opens T) (V : Opens T) (q : ℕ)
    (x : (CategoryTheory.nerve (CoverIndex U V)).obj
      (op (SimplexCategory.mk q)))
    (hx : x ∈ (CategoryTheory.nerve
      (CoverIndex U V)).nonDegenerate q) :
    (CategoryTheory.nerve
        (CoverIndex U V)).ιNormalizedChainComplex x ≫
        (evaluatedNormalizedTermIsoAvailable
          (R := R) U V q).hom =
      Limits.Sigma.ι
        (fun _ : AvailableSimplex U V q =>
          ModuleCat.of R R)
        (nondegenerateToAvailableSimplex U V q ⟨x, hx⟩) := by
  change
    (CategoryTheory.nerve
        (CoverIndex U V)).ιNormalizedChainComplex x ≫
        ((normalizedTermIsoNondegenerate
          (R := R) (CategoryTheory.nerve
            (CoverIndex U V)) q).hom ≫
          (coproductConstEquivIso
            (nondegenerateAvailableSimplexEquiv U V q)
            (ModuleCat.of R R)).hom) = _
  rw [← Category.assoc]
  have hfirst :
      (CategoryTheory.nerve
          (CoverIndex U V)).ιNormalizedChainComplex x ≫
          (normalizedTermIsoNondegenerate
            (R := R) (CategoryTheory.nerve
              (CoverIndex U V)) q).hom =
        Limits.Sigma.ι
          (fun _ : (CategoryTheory.nerve
            (CoverIndex U V)).nonDegenerate q =>
              ModuleCat.of R R) ⟨x, hx⟩ := by
    exact
      ((CategoryTheory.nerve
        (CoverIndex U V)).isColimitCofanNormalizedChainComplex
          (ModuleCat.of R R) q).comp_coconePointUniqueUpToIso_hom
        (Limits.coproductIsCoproduct _) (Discrete.mk ⟨x, hx⟩)
  rw [hfirst]
  dsimp [coproductConstEquivIso]
  rw [Limits.Sigma.ι_desc]
  rfl

/-- The normalized ordered-cover term is naturally the coproduct of
copies of `R` indexed by available finite subsets. -/
noncomputable def orderedCoverNormalizedTermIsoAvailable
    (U : ι → Opens T) (q : ℕ) :
    (orderedCoverNormalizedPresheafComplex
      (R := R) U).X q ≅
      availableSimplexTermFunctor (R := R) U q :=
  NatIso.ofComponents
    (fun V =>
      evaluatedNormalizedTermIsoAvailable
        (R := R) U V.unop q)
    (fun {V W} f => by
      change
        (SSet.normalizedChainComplexMap
            ((orderedCoverNerveFunctor U).map f)
            (ModuleCat.of R R)).f q ≫
            (evaluatedNormalizedTermIsoAvailable
              (R := R) U W.unop q).hom =
          (evaluatedNormalizedTermIsoAvailable
              (R := R) U V.unop q).hom ≫
            Limits.Sigma.map'
              (AvailableSimplex.map U f q)
              (fun _ => 𝟙 (ModuleCat.of R R))
      apply (CategoryTheory.nerve
        (CoverIndex U V.unop)).normalizedChainComplex_hom_ext
      intro x hx
      dsimp only [orderedCoverNerveFunctor]
      rw [← Category.assoc,
        SSet.ι_normalizedChainComplexMap_f]
      have hy :
          ((CategoryTheory.nerveMap
            (coverIndexRestriction U f)).app _ x) ∈
              (CategoryTheory.nerve
                (CoverIndex U W.unop)).nonDegenerate q := by
        exact
          (orderedCoverNondegenerateMap U f q ⟨x, hx⟩).2
      rw [ι_evaluatedNormalizedTermIsoAvailable_hom
        (R := R) U W.unop q
        ((CategoryTheory.nerveMap
          (coverIndexRestriction U f)).app _ x) hy]
      rw [ι_evaluatedNormalizedTermIsoAvailable_hom_assoc
        (R := R) U V.unop q x hx]
      rw [Limits.Sigma.ι_comp_map']
      simp only [Category.id_comp]
      congr 1)

/-- One represented-intersection summand maps to the available-simplex
term by sending a represented inclusion to its corresponding available
finite subset. -/
noncomputable def finiteSubsetSummandToAvailable
    (U : ι → Opens T) (q : ℕ)
    (I : Simplex (ι := ι) q) :
    yoneda.obj (intersection U I.1) ⋙
        sigmaConst.obj (ModuleCat.of R R) ⟶
      availableSimplexTermFunctor (R := R) U q where
  app V :=
    representedIntersectionDesc (R := R) U I V
      ((availableSimplexTermFunctor (R := R) U q).obj V) fun h =>
      availableSimplexGenerator (R := R) U q V
        ⟨I, leOfHom h⟩
  naturality {V W} f := by
    apply Limits.Sigma.hom_ext
    intro h
    change
      representedIntersectionGenerator (R := R) U I V h ≫
          (yoneda.obj (intersection U I.1) ⋙
            sigmaConst.obj (ModuleCat.of R R)).map f ≫
          representedIntersectionDesc (R := R) U I W
            ((availableSimplexTermFunctor (R := R) U q).obj W)
            (fun k => availableSimplexGenerator (R := R) U q W
              ⟨I, leOfHom k⟩) =
        representedIntersectionGenerator (R := R) U I V h ≫
          representedIntersectionDesc (R := R) U I V
            ((availableSimplexTermFunctor (R := R) U q).obj V)
            (fun k => availableSimplexGenerator (R := R) U q V
              ⟨I, leOfHom k⟩) ≫
          (availableSimplexTermFunctor (R := R) U q).map f
    rw [← Category.assoc, representedIntersectionGenerator_map]
    rw [representedIntersectionGenerator_comp_desc]
    rw [← Category.assoc,
      representedIntersectionGenerator_comp_desc]
    rw [availableSimplexGenerator_map]
    congr 1

/-- The finite coproduct of the represented-intersection summands maps
to the available-simplex term. -/
noncomputable def finiteSubsetSigmaToAvailable
    (U : ι → Opens T) (q : ℕ) :
  finiteSubsetSigmaPresheafTerm (R := R) U q ⟶
      availableSimplexTermFunctor (R := R) U q :=
  finiteSubsetSigmaDesc (R := R) U q
    (finiteSubsetSummandToAvailable (R := R) U q)

/-- The inverse generator map: an available finite subset determines a
represented inclusion into the corresponding intersection summand. -/
noncomputable def availableToFiniteSubsetSigma
    (U : ι → Opens T) (q : ℕ) :
    availableSimplexTermFunctor (R := R) U q ⟶
      finiteSubsetSigmaPresheafTerm (R := R) U q where
  app V :=
    availableSimplexDesc (R := R) U q V
      ((finiteSubsetSigmaPresheafTerm (R := R) U q).obj V) fun A =>
      representedIntersectionGenerator (R := R) U A.1 V
          (homOfLE A.2) ≫
        (finiteSubsetSummandι (R := R) U q A.1).app V
  naturality {V W} f := by
    apply Limits.Sigma.hom_ext
    intro A
    change
      availableSimplexGenerator (R := R) U q V A ≫
          (availableSimplexTermFunctor (R := R) U q).map f ≫
          availableSimplexDesc (R := R) U q W
            ((finiteSubsetSigmaPresheafTerm (R := R) U q).obj W) (fun B =>
            representedIntersectionGenerator (R := R) U B.1 W
                (homOfLE B.2) ≫
              (finiteSubsetSummandι
                (R := R) U q B.1).app W) =
        availableSimplexGenerator (R := R) U q V A ≫
          availableSimplexDesc (R := R) U q V
            ((finiteSubsetSigmaPresheafTerm (R := R) U q).obj V) (fun B =>
            representedIntersectionGenerator (R := R) U B.1 V
                (homOfLE B.2) ≫
              (finiteSubsetSummandι
                (R := R) U q B.1).app V) ≫
          (finiteSubsetSigmaPresheafTerm (R := R) U q).map f
    rw [← Category.assoc, availableSimplexGenerator_map]
    rw [availableSimplexGenerator_comp_desc]
    rw [← Category.assoc, availableSimplexGenerator_comp_desc]
    have houter :
        (finiteSubsetSummandι
            (R := R) U q A.1).app V ≫
            (finiteSubsetSigmaPresheafTerm
              (R := R) U q).map f =
          ((yoneda.obj (intersection U A.1.1) ⋙
              sigmaConst.obj (ModuleCat.of R R)).map f) ≫
            (finiteSubsetSummandι
              (R := R) U q A.1).app W :=
      (finiteSubsetSummandι
        (R := R) U q A.1).naturality f |>.symm
    rw [Category.assoc]
    rw [houter]
    rw [← Category.assoc]
    rw [representedIntersectionGenerator_map]
    congr 1

@[reassoc]
lemma representedIntersectionGenerator_comp_toAvailable_app
    (U : ι → Opens T) (q : ℕ)
    (I : Simplex (ι := ι) q) (V : (Opens T)ᵒᵖ)
    (h : (yoneda.obj (intersection U I.1)).obj V) :
    representedIntersectionGenerator (R := R) U I V h ≫
        (finiteSubsetSummandToAvailable
          (R := R) U q I).app V =
      availableSimplexGenerator (R := R) U q V
        ⟨I, leOfHom h⟩ := by
  exact representedIntersectionGenerator_comp_desc
    (R := R) U I V
    ((availableSimplexTermFunctor (R := R) U q).obj V)
    (fun k => availableSimplexGenerator (R := R) U q V
      ⟨I, leOfHom k⟩) h

@[reassoc]
lemma availableSimplexGenerator_comp_toFiniteSubset_app
    (U : ι → Opens T) (q : ℕ) (V : (Opens T)ᵒᵖ)
    (A : AvailableSimplex U V.unop q) :
    availableSimplexGenerator (R := R) U q V A ≫
        (availableToFiniteSubsetSigma (R := R) U q).app V =
      representedIntersectionGenerator (R := R) U A.1 V
          (homOfLE A.2) ≫
        (finiteSubsetSummandι (R := R) U q A.1).app V := by
  exact availableSimplexGenerator_comp_desc
    (R := R) U q V
    ((finiteSubsetSigmaPresheafTerm (R := R) U q).obj V)
    (fun B => representedIntersectionGenerator (R := R) U B.1 V
        (homOfLE B.2) ≫
      (finiteSubsetSummandι (R := R) U q B.1).app V) A

@[reassoc]
lemma finiteSubsetSigma_ι_comp_toAvailable_app
    (U : ι → Opens T) (q : ℕ)
    (I : Simplex (ι := ι) q) (V : (Opens T)ᵒᵖ) :
    (finiteSubsetSummandι (R := R) U q I).app V ≫
      (finiteSubsetSigmaToAvailable
        (R := R) U q).app V =
      (finiteSubsetSummandToAvailable
      (R := R) U q I).app V := by
  have h := congrArg
    (fun k : (yoneda.obj (intersection U I.1) ⋙
        sigmaConst.obj (ModuleCat.of R R)) ⟶
        availableSimplexTermFunctor (R := R) U q =>
      k.app V)
    (finiteSubsetSummandι_comp_desc (R := R) U q
      (finiteSubsetSummandToAvailable (R := R) U q) I)
  simpa [finiteSubsetSigmaToAvailable] using h

lemma availableToFiniteSubsetSigma_comp_toAvailable
    (U : ι → Opens T) (q : ℕ) :
    availableToFiniteSubsetSigma (R := R) U q ≫
        finiteSubsetSigmaToAvailable (R := R) U q =
      𝟙 (availableSimplexTermFunctor (R := R) U q) := by
  apply NatTrans.ext
  funext V
  apply Limits.Sigma.hom_ext
  intro A
  simp only [NatTrans.comp_app, NatTrans.id_app,
    Category.comp_id]
  change
    availableSimplexGenerator (R := R) U q V A ≫
        (availableToFiniteSubsetSigma (R := R) U q).app V ≫
        (finiteSubsetSigmaToAvailable (R := R) U q).app V =
      availableSimplexGenerator (R := R) U q V A
  rw [availableSimplexGenerator_comp_toFiniteSubset_app_assoc]
  rw [finiteSubsetSigma_ι_comp_toAvailable_app]
  rw [representedIntersectionGenerator_comp_toAvailable_app]

lemma finiteSubsetSigmaToAvailable_comp_availableTo
    (U : ι → Opens T) (q : ℕ) :
    finiteSubsetSigmaToAvailable (R := R) U q ≫
        availableToFiniteSubsetSigma (R := R) U q =
      𝟙 (finiteSubsetSigmaPresheafTerm (R := R) U q) := by
  apply Limits.Sigma.hom_ext
  intro I
  apply NatTrans.ext
  funext V
  apply Limits.Sigma.hom_ext
  intro h
  change
    (representedIntersectionGenerator (R := R) U I V h ≫
        (finiteSubsetSummandι (R := R) U q I).app V) ≫
        ((finiteSubsetSigmaToAvailable (R := R) U q).app V ≫
          (availableToFiniteSubsetSigma (R := R) U q).app V) =
      representedIntersectionGenerator (R := R) U I V h ≫
        (finiteSubsetSummandι (R := R) U q I).app V
  rw [Category.assoc]
  rw [finiteSubsetSigma_ι_comp_toAvailable_app_assoc]
  rw [representedIntersectionGenerator_comp_toAvailable_app_assoc]
  rw [availableSimplexGenerator_comp_toFiniteSubset_app]
  congr 1

/-- Available finite subsets are naturally the same as the coproduct of
the represented-intersection coefficient presheaves. -/
noncomputable def availableFiniteSubsetSigmaIso
    (U : ι → Opens T) (q : ℕ) :
    availableSimplexTermFunctor (R := R) U q ≅
      finiteSubsetSigmaPresheafTerm (R := R) U q where
  hom := availableToFiniteSubsetSigma (R := R) U q
  inv := finiteSubsetSigmaToAvailable (R := R) U q
  hom_inv_id :=
    availableToFiniteSubsetSigma_comp_toAvailable
      (R := R) U q
  inv_hom_id :=
    finiteSubsetSigmaToAvailable_comp_availableTo
      (R := R) U q

/-- Degreewise, the normalized ordered-cover presheaf complex is the
finite coproduct of coefficient presheaves represented by the finite
intersections. -/
noncomputable def orderedCoverNormalizedTermIsoFiniteSubset
    (U : ι → Opens T) (q : ℕ) :
    (orderedCoverNormalizedPresheafComplex
      (R := R) U).X q ≅
      finiteSubsetSigmaPresheafTerm (R := R) U q :=
  orderedCoverNormalizedTermIsoAvailable
      (R := R) U q ≪≫
    availableFiniteSubsetSigmaIso (R := R) U q

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
