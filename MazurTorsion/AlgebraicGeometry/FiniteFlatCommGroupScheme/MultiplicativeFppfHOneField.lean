/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeCocycleDescent

/-!
# Hilbert 90 for the represented multiplicative fppf sheaf over a field

This file proves the degree-one fppf Hilbert 90 statement used by the bad-fibre Kummer
calculation.  The proof is entirely Cech-theoretic: a cocycle on an arbitrary fppf cover of the
spectrum of a field is pulled back to one nonempty affine chart, its represented overlap value
is made into effective rank-one descent data, and freeness over the field supplies an actual
coboundary gauge.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent

open AffineCommGroupScheme
open CategoryTheory.PresheafOfGroups

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

private abbrev singletonUnderlyingMap {T : Over (Spec (.of A))}
    (a : T ⟶ testObject (R := A) B) : T.left ⟶ Spec (.of B) :=
  a.left

private theorem singletonPairCondition {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) :
    singletonUnderlyingMap a ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      singletonUnderlyingMap b ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  simpa [singletonUnderlyingMap, testObject] using a.w.trans b.w.symm

private noncomputable def singletonPairLiftUnderlying {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) : T.left ⟶ Spec (.of (B ⊗[A] B)) :=
  pullback.lift (singletonUnderlyingMap a) (singletonUnderlyingMap b)
      (singletonPairCondition a b) ≫
    (pullbackSpecIso A B B).hom

private theorem singletonPairLiftUnderlying_base {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) :
    singletonPairLiftUnderlying a b ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) = T.hom := by
  rw [singletonPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_base,
    ← Category.assoc, pullback.lift_fst]
  simpa [singletonUnderlyingMap, testObject] using a.w

private theorem singletonPairLiftUnderlying_fst {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) :
    singletonPairLiftUnderlying a b ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      singletonUnderlyingMap a := by
  rw [singletonPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_fst,
    pullback.lift_fst]

private theorem singletonPairLiftUnderlying_snd {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) :
    singletonPairLiftUnderlying a b ≫
        Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)) :
            B →+* B ⊗[A] B)) =
      singletonUnderlyingMap b := by
  rw [singletonPairLiftUnderlying, Category.assoc, pullbackSpecIso_hom_snd,
    pullback.lift_snd]

/-- The affine tensor-product overlap represents pairs of maps to the singleton affine family. -/
private noncomputable def singletonPairLift {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) :
    T ⟶ testObject (R := A) (B ⊗[A] B) :=
  Over.homMk (singletonPairLiftUnderlying a b)
    (singletonPairLiftUnderlying_base a b)

private theorem singletonPairLift_pairLeft {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) :
    singletonPairLift a b ≫ singletonPairLeft = a := by
  apply Over.OverMorphism.ext
  exact singletonPairLiftUnderlying_fst a b

private theorem singletonPairLift_pairRight {T : Over (Spec (.of A))}
    (a b : T ⟶ testObject (R := A) B) :
    singletonPairLift a b ≫ singletonPairRight = b := by
  apply Over.OverMorphism.ext
  exact singletonPairLiftUnderlying_snd a b

/-- Over a principal ideal domain, every represented multiplicative cocycle on a faithfully
flat singleton affine family is an actual coboundary. -/
theorem representedMultiplicativeOneCocycle_isCohomologous_one
    (c : RepresentedMultiplicativeOneCocycle (A := A) (B := B))
    (hf : (algebraMap A B).FaithfullyFlat) [Nontrivial B] [IsDomain A]
    [IsPrincipalIdealRing A] : c.IsCohomologous 1 := by
  obtain ⟨u, hu⟩ := c.toMultiplicativeUnitCocycle.exists_coboundaryUnit hf
  let g : (multiplicativeScheme A).Point (testObject (R := A) B) :=
    (multiplicativePointMulEquiv A B).symm u
  let x : (multiplicativeScheme A).Point (testObject (R := A) (B ⊗[A] B)) :=
    c.ev () () (singletonPairLeft (A := A) (B := B))
      (singletonPairRight (A := A) (B := B))
  have hg : multiplicativePointMulEquiv A B g = u :=
    (multiplicativePointMulEquiv A B).apply_symm_apply u
  have hoverlap :
      singletonPairLeft (A := A) (B := B) ≫ g *
          x =
        singletonPairRight (A := A) (B := B) ≫ g := by
    apply (multiplicativePointMulEquiv A (B ⊗[A] B)).injective
    rw [map_mul, singletonPairLeft, singletonPairRight,
      multiplicativePointMulEquiv_testObjectMap,
      multiplicativePointMulEquiv_testObjectMap, hg]
    change Units.map _ u * c.toMultiplicativeUnitCocycle.unit = Units.map _ u
    exact hu
  refine ⟨fun _ ↦ g, ?_⟩
  rintro ⟨⟩ ⟨⟩ T a b
  dsimp only [OneCocycle.one_toOneCochain, OneCochain.one_ev]
  rw [one_mul]
  let y : (multiplicativeScheme A).Point T := c.ev () () a b
  change (a ≫ g) * y = (b ≫ g)
  let q := singletonPairLift a b
  have hq := congrArg (fun z ↦ q ≫ z) hoverlap
  have hc := c.ev_precomp () () q
    (singletonPairLeft (A := A) (B := B))
    (singletonPairRight (A := A) (B := B))
  rw [singletonPairLift_pairLeft, singletonPairLift_pairRight] at hc
  change q ≫ x = y at hc
  rw [MonObj.comp_mul] at hq
  change ((q ≫ singletonPairLeft) ≫ g) * (q ≫ x) =
    (q ≫ singletonPairRight) ≫ g at hq
  rw [show q = singletonPairLift a b by rfl, singletonPairLift_pairLeft,
    singletonPairLift_pairRight, hc] at hq
  exact hq

/-- The singleton coboundary calculation is unchanged for any nonempty subsingleton index type. -/
theorem constantRepresentedMultiplicativeOneCocycle_isCohomologous_one
    {I : Type u} [Nonempty I] [Subsingleton I]
    (c : OneCocycle (pointPresheaf (multiplicativeScheme A))
      (fun _ : I ↦ testObject (R := A) B))
    (hf : (algebraMap A B).FaithfullyFlat) [Nontrivial B] [IsDomain A]
    [IsPrincipalIdealRing A] : c.IsCohomologous 1 := by
  letI : Inhabited I := Classical.inhabited_of_nonempty ‹Nonempty I›
  let r : FamilyRefinement (fun _ : Unit ↦ testObject (R := A) B)
      (fun _ : I ↦ testObject (R := A) B) :=
    { index := fun _ ↦ default
      map := fun _ ↦ 𝟙 _ }
  let c₀ := r.pullbackOneCocycle c
  change RepresentedMultiplicativeOneCocycle (A := A) (B := B) at c₀
  have hc₀ := representedMultiplicativeOneCocycle_isCohomologous_one c₀ hf
  let s : FamilyRefinement (fun _ : I ↦ testObject (R := A) B)
      (fun _ : Unit ↦ testObject (R := A) B) :=
    { index := fun _ ↦ ()
      map := fun _ ↦ 𝟙 _ }
  have hs := s.pullback_isCohomologous hc₀
  have heq : s.pullbackOneCocycle c₀ = c := by
    apply FamilyRefinement.oneCocycle_ext
    apply OneCochain.ext
    funext i j T a b
    have hi : i = default := Subsingleton.elim _ _
    have hj : j = default := Subsingleton.elim _ _
    subst i
    subst j
    simp only [c₀, r, s, FamilyRefinement.pullbackOneCocycle,
      FamilyRefinement.pullbackOneCochain, Category.comp_id]
  rw [heq, FamilyRefinement.pullbackOneCocycle_one] at hs
  exact hs

/-- Fppf Hilbert 90 over a field: every global represented `G_m` class is trivial. -/
theorem multiplicativeFppfHOne_eq_one (K : Type u) [Field K]
    (z : (multiplicativeScheme K).FppfHOne.{u}) : z = 1 := by
  letI : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  induction z using Quot.inductionOn with
  | _ representative =>
      rcases representative with ⟨𝒰, value⟩
      induction value using Quot.inductionOn with
      | _ c =>
          let x₀ : Spec (.of K) := default
          let i : 𝒰.I₀ := 𝒰.idx x₀
          have hi : x₀ ∈ Set.range (𝒰.f i) := by
            exact 𝒰.covers x₀
          obtain ⟨y, hy⟩ := hi
          let j := (𝒰.X i).affineCover.idx y
          have hj : y ∈ Set.range ((𝒰.X i).affineCover.f j) := by
            exact (𝒰.X i).affineCover.covers y
          obtain ⟨w, hw⟩ := hj
          let U := (𝒰.X i).affineCover.X j
          let B := Γ(U, ⊤)
          let e : U ≅ Spec (.of B) := U.isoSpec
          let s : Spec (.of B) ⟶ 𝒰.X i :=
            e.inv ≫ (𝒰.X i).affineCover.f j
          let h : Spec (.of B) ⟶ Spec (.of K) := s ≫ 𝒰.f i
          letI : Algebra K B := (Spec.preimage h).hom.toAlgebra
          have hSpec :
              Spec.map (CommRingCat.ofHom (algebraMap K B)) = h := by
            change Spec.map (Spec.preimage h) = h
            exact Spec.map_preimage h
          let wB : Spec (.of B) := e.hom w
          letI : Nonempty (Spec (.of B)) := ⟨wB⟩
          have hBnonempty : Nonempty (PrimeSpectrum B) := ⟨wB⟩
          letI : Nontrivial B :=
            PrimeSpectrum.nonempty_iff_nontrivial.mp hBnonempty
          have h𝒰 := 𝒰.map_prop i
          letI : Flat (𝒰.f i) := h𝒰.1
          letI : LocallyOfFinitePresentation (𝒰.f i) := h𝒰.2
          letI : Flat s := inferInstance
          letI : LocallyOfFinitePresentation s := inferInstance
          letI : Flat h := inferInstance
          letI : LocallyOfFinitePresentation h := inferInstance
          letI : Surjective h := inferInstance
          let f : Spec (.of B) ⟶ Spec (.of K) :=
            Spec.map (CommRingCat.ofHom (algebraMap K B))
          letI : Flat f := by
            dsimp only [f]
            rw [hSpec]
            infer_instance
          letI : LocallyOfFinitePresentation f := by
            dsimp only [f]
            rw [hSpec]
            infer_instance
          letI : Surjective f := by
            dsimp only [f]
            rw [hSpec]
            infer_instance
          have hf : (algebraMap K B).FaithfullyFlat := by
            exact (flat_and_surjective_SpecMap_iff
              (CommRingCat.ofHom (algebraMap K B))).mp ⟨inferInstance, inferInstance⟩
          let 𝒱 : Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (.of K)) :=
            Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ ↦ Spec (.of B)) (fun _ ↦ f)
              (fun x ↦ ⟨PUnit.unit, wB, Subsingleton.elim _ _⟩)
              (fun _ ↦ ⟨inferInstance, inferInstance⟩)
          let r : 𝒱.Hom 𝒰 :=
            { s₀ := fun _ ↦ i
              h₀ := fun _ ↦ s
              w₀ := fun _ ↦ by
                change s ≫ 𝒰.f i = f
                exact hSpec.symm }
          let c' := (Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle c
          change OneCocycle (pointPresheaf (multiplicativeScheme K))
            (fun _ : PUnit.{u + 1} ↦ testObject (R := K) B) at c'
          have hc' : c'.class = 1 :=
            (constantRepresentedMultiplicativeOneCocycle_isCohomologous_one c' hf).class_eq
          calc
            Scheme.FppfHOne.mk 𝒰 c.class =
                Scheme.FppfHOne.mk 𝒱
                  (Scheme.Cover.Hom.pullbackHOne
                    (pointPresheaf (multiplicativeScheme K)) r c.class) :=
              (Scheme.FppfHOne.class_pullback 𝒰 𝒱 r c.class).symm
            _ = Scheme.FppfHOne.mk 𝒱 c'.class := rfl
            _ = Scheme.FppfHOne.mk 𝒱 1 := congrArg _ hc'
            _ = 1 := Scheme.FppfHOne.mk_one 𝒱

/-- The represented multiplicative fppf `H¹` over a field has exactly one class. -/
instance multiplicativeFppfHOne_subsingleton (K : Type u) [Field K] :
    Subsingleton (multiplicativeScheme K).FppfHOne.{u} :=
  ⟨fun x y ↦ (multiplicativeFppfHOne_eq_one K x).trans
    (multiplicativeFppfHOne_eq_one K y).symm⟩

end AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent
