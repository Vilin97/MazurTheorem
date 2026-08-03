/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Properties

/-!
# Constant group schemes from finite families of rational sections

Over a field, the constant scheme on a finite group is the finite coproduct of copies of the
base point.  This file makes that decomposition explicit, proves that an injective finite family
of rational sections is a closed immersion, and checks componentwise that a group-valued family
extends to a morphism of commutative group schemes.

The final construction is the scheme-theoretic input used by the split `\Gamma_0(N)` source
datum: it replaces an assumed extension interface by a checked morphism and closed-immersion
proof.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

open scoped Function

/-- A finite coproduct of pairwise-disjoint closed immersions is a closed
immersion. -/
theorem isClosedImmersion_sigmaDesc
    {ι : Type u} [Finite ι] {Y : ι → Scheme.{u}} {X : Scheme.{u}}
    (α : ∀ i, Y i ⟶ X) [∀ i, IsClosedImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α ·))) :
    IsClosedImmersion (Sigma.desc α) := by
  letI : SurjectiveOnStalks (Sigma.desc α) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks)
      (fun _ ↦ inferInstance)
  refine ⟨?_⟩
  suffices Topology.IsClosedEmbedding (Sigma.desc α ∘ sigmaMk Y) by
    have heq : (Sigma.desc α : (∐ Y :) → X) =
        (Sigma.desc α ∘ sigmaMk Y) ∘ (sigmaMk Y).symm := by
      funext x
      simp
    rw [heq]
    exact this.comp (sigmaMk Y).symm.isClosedEmbedding
  refine .of_continuous_injective_isClosedMap ?_ ?_ ?_
  · fun_prop
  · rintro ⟨ix, x⟩ ⟨iy, y⟩ e
    have : α ix x = α iy y := by
      simpa [← Scheme.Hom.comp_apply] using e
    obtain rfl : ix = iy := by
      by_contra h
      exact Set.disjoint_iff_forall_ne.mp (hα h)
        ⟨x, rfl⟩ ⟨y, this.symm⟩ rfl
    exact congrArg (Sigma.mk ix) ((α ix).isClosedEmbedding.injective this)
  · intro s hs
    rw [show (Sigma.desc α ∘ sigmaMk Y) '' s =
        ⋃ i, α i '' ((fun y : Y i ↦ (⟨i, y⟩ : Σ i, Y i)) ⁻¹' s) by
      ext z
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage,
        Function.comp_apply]
      constructor
      · rintro ⟨⟨i, y⟩, hy, rfl⟩
        exact ⟨i, y, hy, by simp [← Scheme.Hom.comp_apply]⟩
      · rintro ⟨i, y, hy, rfl⟩
        exact ⟨⟨i, y⟩, hy, by simp [← Scheme.Hom.comp_apply]⟩]
    exact isClosed_iUnion_of_finite fun i ↦
      (α i).isClosedEmbedding.isClosedMap _
        ((isClosed_sigma_iff.mp hs) i)

/-- The residue-field map induced by the identity point of the spectrum of a
field is an isomorphism. -/
theorem specField_identityResidue_isIso {K : Type u} [Field K] :
    IsIso ((Spec (.of K)).descResidueField
      (Scheme.stalkClosedPointTo (𝟙 (Spec (.of K))))) := by
  let x := IsLocalRing.closedPoint K
  let q := (Spec (.of K)).descResidueField
    (Scheme.stalkClosedPointTo (𝟙 (Spec (.of K))))
  let j := (Spec (.of K)).fromSpecResidueField x
  letI : Field ((Spec (.of K)).residueField x) :=
    Scheme.instFieldCarrierResidueField _ _
  letI : Nonempty (Spec ((Spec (.of K)).residueField x)) := by
    exact ⟨(Scheme.instUniqueCarrierCarrierCommRingCatSpecResidueField _ _).default⟩
  have hjci : IsClosedImmersion j := by
    dsimp only [j]
    exact isClosed_singleton_iff_isClosedImmersion.mp isClosed_singleton
  have hj : Function.Surjective j := Function.surjective_to_subsingleton _
  have hjs : Surjective j := ⟨hj⟩
  have hred : IsReduced (Spec (.of K)) := inferInstance
  have hjiso : IsIso j :=
    @isIso_of_isClosedImmersion_of_surjective _ _ j hjci hjs hred
  letI : IsIso j := hjiso
  have hq : Spec.map q ≫ j = 𝟙 (Spec (.of K)) := by
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
      K (Spec (.of K)) (𝟙 (Spec (.of K)))
  letI : IsIso (Spec.map q) :=
    @IsIso.of_isIso_fac_right Scheme _ _ _ _ j (Spec.map q)
      (𝟙 (Spec (.of K))) hjiso (by infer_instance) hq
  letI : IsIso (Scheme.Spec.map q.op) := by
    change IsIso (Spec.map q)
    infer_instance
  letI : IsIso q.op := isIso_of_reflects_iso q.op Scheme.Spec
  haveI : IsIso q.op.unop := inferInstance
  have hqIso : IsIso q.op.unop := inferInstance
  change IsIso q at hqIso
  exact hqIso

/-- Two sections over the spectrum of a field agree if they agree on its
unique closed point. -/
theorem section_eq_of_apply_closedPoint_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (f g : Spec (.of K) ⟶ X)
    (hf : f ≫ π = 𝟙 _) (hg : g ≫ π = 𝟙 _)
    (h : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) :
    f = g := by
  apply (X.SpecToEquivOfField K).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨h, ?_⟩
  let q := (Spec (.of K)).descResidueField
    (Scheme.stalkClosedPointTo (𝟙 (Spec (.of K))))
  let rf := π.residueFieldMap (f (IsLocalRing.closedPoint K))
  let rg := π.residueFieldMap (g (IsLocalRing.closedPoint K))
  let φf := X.descResidueField (Scheme.stalkClosedPointTo f)
  let φg := X.descResidueField (Scheme.stalkClosedPointTo g)
  obtain ⟨efpt, efres⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    (congrArg (Scheme.SpecToEquivOfField K (Spec (.of K))) hf)
  obtain ⟨egpt, egres⟩ := Scheme.SpecToEquivOfField_eq_iff.mp
    (congrArg (Scheme.SpecToEquivOfField K (Spec (.of K))) hg)
  change π (f (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint K at efpt
  change π (g (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint K at egpt
  have efcomp := Scheme.descResidueField_stalkClosedPointTo_comp (f := π) f
  have egcomp := Scheme.descResidueField_stalkClosedPointTo_comp (f := π) g
  have hrfφ : rf ≫ φf =
      ((Spec (.of K)).residueFieldCongr efpt).hom ≫ q := by
    change π.residueFieldMap (f (IsLocalRing.closedPoint K)) ≫
        X.descResidueField (Scheme.stalkClosedPointTo f) = _
    rw [← efcomp]
    exact efres
  have hrgφ : rg ≫ φg =
      ((Spec (.of K)).residueFieldCongr egpt).hom ≫ q := by
    change π.residueFieldMap (g (IsLocalRing.closedPoint K)) ≫
        X.descResidueField (Scheme.stalkClosedPointTo g) = _
    rw [← egcomp]
    exact egres
  haveI : IsIso q := specField_identityResidue_isIso
  haveI : IsIso ((Spec (.of K)).residueFieldCongr efpt).hom := inferInstance
  have hφf : Function.Injective φf := (φf.hom.injective)
  have hqf : Function.Surjective
      (((Spec (.of K)).residueFieldCongr efpt).hom ≫ q) := by
    exact (ConcreteCategory.bijective_of_isIso q).2.comp
      (ConcreteCategory.bijective_of_isIso
        ((Spec (.of K)).residueFieldCongr efpt).hom).2
  have hrf : Function.Surjective rf := by
    intro y
    obtain ⟨x, hx⟩ := hqf (φf y)
    refine ⟨x, hφf ?_⟩
    calc
      φf (rf x) = (((Spec (.of K)).residueFieldCongr efpt).hom ≫ q) x := by
        exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hrfφ) x
      _ = φf y := hx
  letI : Epi rf := ConcreteCategory.epi_of_surjective rf hrf
  change φf = (X.residueFieldCongr h).hom ≫ φg
  apply (cancel_epi rf).1
  have hbase : ((Spec (.of K)).residueFieldCongr efpt).hom =
      ((Spec (.of K)).residueFieldCongr (congrArg π h)).hom ≫
        ((Spec (.of K)).residueFieldCongr egpt).hom := by
    symm
    calc
      ((Spec (.of K)).residueFieldCongr (congrArg π h)).hom ≫
          ((Spec (.of K)).residueFieldCongr egpt).hom =
        ((Spec (.of K)).residueFieldCongr
          ((congrArg π h).trans egpt)).hom :=
            Scheme.residueFieldCongr_trans_hom _ _ _
      _ = ((Spec (.of K)).residueFieldCongr efpt).hom := by
        rw [show (congrArg π h).trans egpt = efpt from Subsingleton.elim _ _]
  calc
    rf ≫ φf = ((Spec (.of K)).residueFieldCongr efpt).hom ≫ q := hrfφ
    _ = (((Spec (.of K)).residueFieldCongr (congrArg π h)).hom ≫
          ((Spec (.of K)).residueFieldCongr egpt).hom) ≫ q := by rw [hbase]
    _ = ((Spec (.of K)).residueFieldCongr (congrArg π h)).hom ≫
          (((Spec (.of K)).residueFieldCongr egpt).hom ≫ q) :=
      Category.assoc _ _ _
    _ = ((Spec (.of K)).residueFieldCongr (congrArg π h)).hom ≫
          (rg ≫ φg) := by rw [hrgφ]
    _ = (((Spec (.of K)).residueFieldCongr (congrArg π h)).hom ≫ rg) ≫ φg :=
      (Category.assoc _ _ _).symm
    _ = (rf ≫ (X.residueFieldCongr h).hom) ≫ φg := by
      rw [π.residueFieldMap_congr' h]
    _ = rf ≫ (X.residueFieldCongr h).hom ≫ φg := rfl

/-- Distinct sections over the spectrum of a field have disjoint ranges. -/
theorem pairwise_disjoint_section_ranges
    {K : Type u} [Field K] {X : Scheme.{u}}
    {ι : Type u} (π : X ⟶ Spec (.of K))
    (s : ι → (Spec (.of K) ⟶ X))
    (hs : ∀ i, s i ≫ π = 𝟙 _) (hinj : Function.Injective s) :
    Pairwise (Disjoint on fun i ↦ Set.range (s i)) := by
  intro i j hij
  change Disjoint (Set.range (s i)) (Set.range (s j))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hb : b = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  subst a
  subst b
  exact hij (hinj (section_eq_of_apply_closedPoint_eq
    π (s i) (s j) (hs i) (hs j) hab))

/-- An injective finite family of sections over a field descends from their
coproduct as a closed immersion. -/
theorem isClosedImmersion_sigmaDesc_sections
    {K : Type u} [Field K] {X : Scheme.{u}}
    {ι : Type u} [Finite ι] (π : X ⟶ Spec (.of K))
    (s : ι → (Spec (.of K) ⟶ X))
    (hs : ∀ i, s i ≫ π = 𝟙 _) (hinj : Function.Injective s) :
    IsClosedImmersion (Sigma.desc s) := by
  letI (i : ι) : IsClosedImmersion (s i) :=
    isClosedImmersion_of_comp_eq_id π (s i) (hs i)
  exact isClosedImmersion_sigmaDesc s
    (pairwise_disjoint_section_ranges π s hs hinj)

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

private abbrev baseTestObject (K : Type u) [Field K] :
    Over (Spec (.of K)) :=
  AffineCommGroupScheme.testObject (R := K) K

private def pointSchemeMap
    (K : Type u) [Field K] {X : Over (Spec (.of K))}
    (x : baseTestObject K ⟶ X) : Spec (.of K) ⟶ X.left :=
  x.left

private theorem pointSchemeMap_comp
    (K : Type u) [Field K] {X Y : Over (Spec (.of K))}
    (x : baseTestObject K ⟶ X) (f : X ⟶ Y) :
    pointSchemeMap K (x ≫ f) = pointSchemeMap K x ≫ f.left := by
  rfl

private abbrev constantProductScheme
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] : Scheme.{u} :=
  pullback
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (ConstantCoordinates K G))))
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (ConstantCoordinates K G))))

/-- The underlying map of schemes of a distinguished point of a constant group scheme. -/
abbrev constantGeometricPointMap
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g : G) :
    Spec (.of K) ⟶ (constantScheme K G).scheme :=
  pointSchemeMap K (constantGeometricPoint K G g)

/-- The constant scheme on a finite group is the coproduct of one copy of the
base field spectrum for each group element. -/
def constantSchemeSigmaIso
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] :
    (constantScheme K G).scheme ≅ ∐ fun _ : G ↦ Spec (.of K) :=
  (Scheme.Spec.mapIso
      (ULift.algEquiv.{u, u, 0} (R := K)
        (A := G → K)).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (asIso (sigmaSpec (fun _ : G ↦ CommRingCat.of K))).symm

/-- The underlying scheme map of a distinguished constant point is evaluation
at its index. -/
theorem constantGeometricPoint_left
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g : G) :
    constantGeometricPointMap K G g =
      Spec.map (CommRingCat.ofHom
        (ConstantCoordinates.evaluation (R := K) g).toRingHom) := by
  rw [← Spec.map_preimage (constantGeometricPointMap K G g)]
  rw [← pointToAlgHom_constantPoint K G g]
  rfl

/-- Under the coproduct decomposition, a distinguished constant point is the
corresponding coproduct inclusion. -/
theorem constantGeometricPoint_sigma
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g : G) :
    constantGeometricPointMap K G g ≫
        (constantSchemeSigmaIso K G).hom =
      Sigma.ι (fun _ : G ↦ Spec (.of K)) g := by
  let e :=
    (ULift.algEquiv.{u, u, 0} (R := K)
      (A := G → K)).toRingEquiv.toCommRingCatIso
  let σ := sigmaSpec (fun _ : G ↦ CommRingCat.of K)
  have hpi :
      constantGeometricPointMap K G g ≫
          (Scheme.Spec.mapIso e.op).symm.hom =
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : G ↦ K) g)) := by
    rw [constantGeometricPoint_left]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext x
    rfl
  have hi : Sigma.ι (fun _ : G ↦ Spec (.of K)) g ≫ σ =
      Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : G ↦ K) g)) :=
    ι_sigmaSpec (fun _ : G ↦ CommRingCat.of K) g
  calc
    constantGeometricPointMap K G g ≫
        (constantSchemeSigmaIso K G).hom =
      (constantGeometricPointMap K G g ≫
          (Scheme.Spec.mapIso e.op).symm.hom) ≫ (asIso σ).inv := by
        rfl
    _ = Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun _ : G ↦ K) g)) ≫ (asIso σ).inv :=
      congrArg (fun q ↦ q ≫ (asIso σ).inv) hpi
    _ = (Sigma.ι (fun _ : G ↦ Spec (.of K)) g ≫ σ) ≫
          (asIso σ).inv := by rw [hi]
    _ = Sigma.ι (fun _ : G ↦ Spec (.of K)) g := by
      rw [Category.assoc]
      simp [σ]

private def constantSchemeProductSigmaIso
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] :
    constantProductScheme K G ≅
      ∐ fun _ : G × G ↦ Spec (.of K) :=
  (pullbackSpecIso K (ConstantCoordinates K G)
      (ConstantCoordinates K G)) ≪≫
    (Scheme.Spec.mapIso
      (ConstantCoordinates.tensorEval (R := K)
        (G := G)).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (asIso (sigmaSpec (fun _ : G × G ↦ CommRingCat.of K))).symm

private def constantPairSchemeMap
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g h : G) :
    Spec (.of K) ⟶
      constantProductScheme K G :=
  Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lift
        (ConstantCoordinates.evaluation (R := K) g)
        (ConstantCoordinates.evaluation (R := K) h)
        (fun _ _ ↦ Commute.all _ _)).toRingHom) ≫
    (pullbackSpecIso K (ConstantCoordinates K G)
      (ConstantCoordinates K G)).inv

private theorem constantPairSchemeMap_fst
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g h : G) :
    constantPairSchemeMap K G g h ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap K (ConstantCoordinates K G))))
          (Spec.map (CommRingCat.ofHom
            (algebraMap K (ConstantCoordinates K G)))) =
      constantGeometricPointMap K G g := by
  rw [constantPairSchemeMap, constantGeometricPoint_left]
  change (Spec.map _ ≫
      (pullbackSpecIso K (ConstantCoordinates K G)
        (ConstantCoordinates K G)).inv) ≫
      pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (ConstantCoordinates K G))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (ConstantCoordinates K G)))) = Spec.map _
  rw [Category.assoc, pullbackSpecIso_inv_fst]
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext x
  simp [Algebra.TensorProduct.includeLeftRingHom]

private theorem constantPairSchemeMap_snd
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g h : G) :
    constantPairSchemeMap K G g h ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom
            (algebraMap K (ConstantCoordinates K G))))
          (Spec.map (CommRingCat.ofHom
            (algebraMap K (ConstantCoordinates K G)))) =
      constantGeometricPointMap K G h := by
  rw [constantPairSchemeMap, constantGeometricPoint_left]
  change (Spec.map _ ≫
      (pullbackSpecIso K (ConstantCoordinates K G)
        (ConstantCoordinates K G)).inv) ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (ConstantCoordinates K G))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (ConstantCoordinates K G)))) = Spec.map _
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext x
  simp [Algebra.TensorProduct.includeRight]

private theorem constantPairSchemeMap_sigma
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g h : G) :
    constantPairSchemeMap K G g h ≫
        (constantSchemeProductSigmaIso K G).hom =
      Sigma.ι (fun _ : G × G ↦ Spec (.of K)) (g, h) := by
  let e :=
    (ConstantCoordinates.tensorEval (R := K)
      (G := G)).toRingEquiv.toCommRingCatIso
  let σ := sigmaSpec (fun _ : G × G ↦ CommRingCat.of K)
  have hcancel :
      constantPairSchemeMap K G g h ≫
          (pullbackSpecIso K (ConstantCoordinates K G)
            (ConstantCoordinates K G)).hom =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lift
            (ConstantCoordinates.evaluation (R := K) g)
            (ConstantCoordinates.evaluation (R := K) h)
            (fun _ _ ↦ Commute.all _ _)).toRingHom) := by
    rw [constantPairSchemeMap, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have heval :
      Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.lift
              (ConstantCoordinates.evaluation (R := K) g)
              (ConstantCoordinates.evaluation (R := K) h)
              (fun _ _ ↦ Commute.all _ _)).toRingHom) ≫
          (Scheme.Spec.mapIso e.op).symm.hom =
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun _ : G × G ↦ K) (g, h))) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext x
    change Algebra.TensorProduct.lift
        (ConstantCoordinates.evaluation (R := K) g)
        (ConstantCoordinates.evaluation (R := K) h)
        (fun _ _ ↦ Commute.all _ _)
        ((ConstantCoordinates.tensorEval (R := K) (G := G)).symm x) =
      x (g, h)
    rw [ConstantCoordinates.lift_evaluation_evaluation]
    exact congrFun ((ConstantCoordinates.tensorEval (R := K)
      (G := G)).apply_symm_apply x) (g, h)
  have hpi :
      (constantPairSchemeMap K G g h ≫
          (pullbackSpecIso K (ConstantCoordinates K G)
            (ConstantCoordinates K G)).hom) ≫
          (Scheme.Spec.mapIso e.op).symm.hom =
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun _ : G × G ↦ K) (g, h))) := by
    exact (congrArg
      (fun q ↦ q ≫ (Scheme.Spec.mapIso e.op).symm.hom) hcancel).trans heval
  have hi : Sigma.ι (fun _ : G × G ↦ Spec (.of K)) (g, h) ≫ σ =
      Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : G × G ↦ K) (g, h))) :=
    ι_sigmaSpec (fun _ : G × G ↦ CommRingCat.of K) (g, h)
  calc
    constantPairSchemeMap K G g h ≫
        (constantSchemeProductSigmaIso K G).hom =
      (constantPairSchemeMap K G g h ≫
          (pullbackSpecIso K (ConstantCoordinates K G)
            (ConstantCoordinates K G)).hom ≫
          (Scheme.Spec.mapIso e.op).symm.hom) ≫ (asIso σ).inv := by
        rfl
    _ =
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun _ : G × G ↦ K) (g, h))) ≫
          (asIso σ).inv :=
      congrArg (fun q ↦ q ≫ (asIso σ).inv) hpi
    _ = (Sigma.ι (fun _ : G × G ↦ Spec (.of K)) (g, h) ≫ σ) ≫
          (asIso σ).inv := by rw [hi]
    _ = Sigma.ι (fun _ : G × G ↦ Spec (.of K)) (g, h) := by
      rw [Category.assoc]
      simp [σ]

/-- Morphisms out of a finite constant scheme agree if they agree on every
distinguished constant point. -/
theorem constantScheme_hom_ext
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G]
    {X : Scheme.{u}} (f g : (constantScheme K G).scheme ⟶ X)
    (h : ∀ a : G,
      constantGeometricPointMap K G a ≫ f =
        constantGeometricPointMap K G a ≫ g) :
    f = g := by
  apply (cancel_epi (constantSchemeSigmaIso K G).inv).1
  apply Sigma.hom_ext
  intro a
  have ha : Sigma.ι (fun _ : G ↦ Spec (.of K)) a ≫
      (constantSchemeSigmaIso K G).inv =
        constantGeometricPointMap K G a := by
    calc
      _ = (constantGeometricPointMap K G a ≫
          (constantSchemeSigmaIso K G).hom) ≫
            (constantSchemeSigmaIso K G).inv := by
        exact (congrArg
          (fun q ↦ q ≫ (constantSchemeSigmaIso K G).inv)
          (constantGeometricPoint_sigma K G a)).symm
      _ = constantGeometricPointMap K G a := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [← Category.assoc, ha] using h a

private theorem constantSchemeProduct_hom_ext
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G]
    {X : Scheme.{u}}
    (f g : constantProductScheme K G ⟶ X)
    (h : ∀ a b : G,
      constantPairSchemeMap K G a b ≫ f =
        constantPairSchemeMap K G a b ≫ g) :
    f = g := by
  apply (cancel_epi (constantSchemeProductSigmaIso K G).inv).1
  apply Sigma.hom_ext
  rintro ⟨a, b⟩
  have hab : Sigma.ι (fun _ : G × G ↦ Spec (.of K)) (a, b) ≫
      (constantSchemeProductSigmaIso K G).inv =
        constantPairSchemeMap K G a b := by
    calc
      _ = (constantPairSchemeMap K G a b ≫
          (constantSchemeProductSigmaIso K G).hom) ≫
            (constantSchemeProductSigmaIso K G).inv := by
        exact (congrArg
          (fun q ↦ q ≫ (constantSchemeProductSigmaIso K G).inv)
          (constantPairSchemeMap_sigma K G a b)).symm
      _ = constantPairSchemeMap K G a b := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [← Category.assoc, hab] using h a b

open scoped CategoryTheory.MonObj

private def extendConstantUnderlying
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
  (f : G →* (baseTestObject K ⟶ E.X)) :
    (constantScheme K G).scheme ⟶ E.X.left :=
  (constantSchemeSigmaIso K G).hom ≫
    Sigma.desc (fun g ↦ pointSchemeMap K (f g))

private theorem constantGeometricPoint_extendConstantUnderlying
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →* (baseTestObject K ⟶ E.X)) (g : G) :
    constantGeometricPointMap K G g ≫
        extendConstantUnderlying K E G f =
      pointSchemeMap K (f g) := by
  rw [extendConstantUnderlying, ← Category.assoc,
    constantGeometricPoint_sigma, Sigma.ι_desc]

private theorem extendConstantUnderlying_comp_structureMap
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →* (baseTestObject K ⟶ E.X)) :
    extendConstantUnderlying K E G f ≫ E.X.hom =
      (constantScheme K G).structureMap := by
  apply constantScheme_hom_ext K G
  intro g
  rw [← Category.assoc,
    constantGeometricPoint_extendConstantUnderlying]
  exact (f g).w.trans (constantGeometricPoint K G g).w.symm

private def extendConstantOver
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →* (baseTestObject K ⟶ E.X)) :
    (constantScheme K G).obj.X ⟶ E.X :=
  Over.homMk (extendConstantUnderlying K E G f)
    (extendConstantUnderlying_comp_structureMap K E G f)

private theorem constantGeometricPoint_extendConstantOver
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →* (baseTestObject K ⟶ E.X)) (g : G) :
    constantGeometricPoint K G g ≫
        extendConstantOver K E G f = f g := by
  apply Over.OverMorphism.ext
  exact constantGeometricPoint_extendConstantUnderlying K E G f g

private theorem baseTestObject_hom_eq_id
    (K : Type u) [Field K] :
    (baseTestObject K).hom = 𝟙 (Spec (.of K)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
  rw [Spec.map_eq_id]
  ext x
  rfl

private theorem constantGeometricPoint_one
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] :
    constantGeometricPoint K G 1 =
      (1 : baseTestObject K ⟶ (constantScheme K G).obj.X) := by
  let x := constantGeometricPoint K G 1
  have h := constantPoint_mul K G 1 1
  have hone : (1 : G) * 1 = 1 := one_mul 1
  rw [hone] at h
  change x = x * x at h
  apply mul_left_cancel (a := x)
  simpa using h.symm

private def constantPairPoint
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g h : G) :
    baseTestObject K ⟶
      ((constantScheme K G).obj.X ⊗ (constantScheme K G).obj.X) :=
  CartesianMonoidalCategory.lift
    (constantGeometricPoint K G g)
    (constantGeometricPoint K G h)

private theorem constantPairPoint_left
    (K : Type u) [Field K]
    (G : Type u) [CommGroup G] [Fintype G] (g h : G) :
    pointSchemeMap K (constantPairPoint K G g h) =
      constantPairSchemeMap K G g h := by
  apply pullback.hom_ext
  · have hl := congrArg (pointSchemeMap K)
      (CartesianMonoidalCategory.lift_fst
        (constantGeometricPoint K G g)
        (constantGeometricPoint K G h))
    rw [pointSchemeMap_comp] at hl
    exact hl.trans (constantPairSchemeMap_fst K G g h).symm
  · have hl := congrArg (pointSchemeMap K)
      (CartesianMonoidalCategory.lift_snd
        (constantGeometricPoint K G g)
        (constantGeometricPoint K G h))
    rw [pointSchemeMap_comp] at hl
    exact hl.trans (constantPairSchemeMap_snd K G g h).symm

/-- Extend a finite group-valued family of rational sections to a morphism
from the corresponding constant commutative group scheme. -/
def extendConstantHom
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →* (AffineCommGroupScheme.testObject (R := K) K ⟶ E.X)) :
    (constantScheme K G).obj ⟶ E := by
  let q := extendConstantOver K E G f
  apply InducedCategory.homMk
  refine Grp.homMk'' q (one_f := ?_) (mul_f := ?_)
  · let X := baseTestObject K
    have hX : X.hom = 𝟙 (Spec (.of K)) :=
      baseTestObject_hom_eq_id K
    letI : IsIso X.hom := by
      rw [hX]
      exact CategoryTheory.IsIso.id _
    letI : IsIso ((Over.forget (Spec (.of K))).map (toUnit X)) := by
      change IsIso X.hom
      infer_instance
    letI : IsIso (toUnit X) := by
      exact isIso_of_reflects_iso (toUnit X) (Over.forget _)
    apply (cancel_epi (toUnit X)).1
    have hpoint :
        (1 : X ⟶ (constantScheme K G).obj.X) ≫ q =
          (1 : X ⟶ E.X) := by
      calc
        _ = constantGeometricPoint K G 1 ≫ q :=
          congrArg (fun z ↦ z ≫ q)
            (constantGeometricPoint_one K G).symm
        _ = f 1 := constantGeometricPoint_extendConstantOver K E G f 1
        _ = 1 := f.map_one
    simpa only [Hom.one_def, Category.assoc] using hpoint
  · apply Over.OverMorphism.ext
    apply constantSchemeProduct_hom_ext K G
    intro a b
    rw [← constantPairPoint_left K G a b]
    let p := constantPairPoint K G a b
    have hpoint :
        p ≫ μ[(constantScheme K G).obj.X] ≫ q =
          p ≫ (q ⊗ₘ q) ≫ μ[E.X] := by
      calc
        _ = (constantGeometricPoint K G a *
              constantGeometricPoint K G b) ≫ q := by
          rfl
        _ = constantGeometricPoint K G (a * b) ≫ q := by
          exact congrArg (fun z ↦ z ≫ q)
            (constantPoint_mul K G a b).symm
        _ = f (a * b) :=
          constantGeometricPoint_extendConstantOver K E G f (a * b)
        _ = f a * f b := f.map_mul a b
        _ = (constantGeometricPoint K G a ≫ q) *
              (constantGeometricPoint K G b ≫ q) := by
          rw [constantGeometricPoint_extendConstantOver,
            constantGeometricPoint_extendConstantOver]
        _ = p ≫ (q ⊗ₘ q) ≫ μ[E.X] := by
          change (CartesianMonoidalCategory.lift
              (constantGeometricPoint K G a ≫ q)
              (constantGeometricPoint K G b ≫ q)) ≫ μ[E.X] =
            (CartesianMonoidalCategory.lift
              (constantGeometricPoint K G a)
              (constantGeometricPoint K G b) ≫ (q ⊗ₘ q)) ≫ μ[E.X]
          rw [lift_map]
    exact congrArg Over.Hom.left hpoint

/-- The constant-group extension agrees with the supplied rational section at
each distinguished constant point. -/
theorem extendConstantHom_map_point
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →*
      (AffineCommGroupScheme.testObject (R := K) K ⟶ E.X)) (g : G) :
    constantGeometricPoint K G g ≫
        (extendConstantHom K E G f).hom.hom.hom = f g := by
  exact constantGeometricPoint_extendConstantOver K E G f g

/-- If the rational sections are injectively indexed, their constant-group
extension is a closed immersion. -/
theorem extendConstantHom_isClosedImmersion
    (K : Type u) [Field K]
    (E : CommGroupScheme (Spec (.of K)))
    (G : Type u) [CommGroup G] [Fintype G]
    (f : G →*
      (AffineCommGroupScheme.testObject (R := K) K ⟶ E.X))
    (hinj : Function.Injective f) :
    IsClosedImmersion
      (extendConstantHom K E G f).hom.hom.hom.left := by
  let s : G → (Spec (.of K) ⟶ E.X.left) := fun g ↦
    pointSchemeMap K (f g)
  have hs : ∀ g, s g ≫ E.X.hom = 𝟙 (Spec (.of K)) := by
    intro g
    exact (f g).w.trans (baseTestObject_hom_eq_id K)
  have hinj_s : Function.Injective s := by
    intro a b hab
    apply hinj
    apply Over.OverMorphism.ext
    exact hab
  letI : IsClosedImmersion (Sigma.desc s) :=
    isClosedImmersion_sigmaDesc_sections E.X.hom s hs hinj_s
  change IsClosedImmersion
    ((constantSchemeSigmaIso K G).hom ≫ Sigma.desc s)
  exact IsClosedImmersion.comp
    (constantSchemeSigmaIso K G).hom (Sigma.desc s)

end AlgebraicGeometry.FiniteFlatCommGroupScheme
