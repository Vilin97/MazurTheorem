/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
import MazurTorsion.Upstream.AINTLIB.ForMathlib.InvariantBaseChange

/-!
# Flat base change of finite-group quotients

Invariants under a finite group commute with flat base change.  This file
packages that algebraic theorem in the exact form needed for affine scheme
quotients: a flat base change of `Spec A ⟶ Spec Aᴳ` is again the categorical
quotient for the induced action.

The named downstream consumer is the comparison between the quotient of
`C × C^d` and `C × Sym^d(C)`, where flatness comes from smoothness of `C` over
the ground field.
-/

noncomputable section

universe u v

open CategoryTheory Limits TensorProduct
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotientFlatBaseChange

variable {G : Type*} [Group G]
variable {R : Type v} {A : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [MulSemiringAction G A] [SMulCommClass G R A]

/-- If `C` is flat over the invariant ring, then the inclusion
`C ⟶ (A ⊗_{Aᴳ} C)ᴳ`, `c ↦ 1 ⊗ c`, is bijective. -/
theorem bijective_includeRightFixedPoints_of_flat
    [Finite G] [SMulCommClass R G A]
    (C : Type u) [CommRing C]
    [Algebra (FixedPoints.subalgebra R A G) C]
    [Module.Flat (FixedPoints.subalgebra R A G) C] :
    Function.Bijective
      (includeRightFixedPoints (G := G) (R := R) (A := A) C) := by
  classical
  have hbc := fixedPointsBaseChange_bijective_of_flat
    (G := G) (R := FixedPoints.subalgebra R A G) (A := A) (R' := C)
  have hij : Function.Bijective
      (Algebra.ofId (FixedPoints.subalgebra R A G)
        (FixedPoints.subalgebra (FixedPoints.subalgebra R A G) A G)) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (congrArg Subtype.val hxy)
    · rintro ⟨z, hz⟩
      exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩
  have hfun : ∀ c : C,
      includeRightFixedPoints (G := G) (R := R) (A := A) C c =
        fixedPointsBaseChange
          (G := G) (R := FixedPoints.subalgebra R A G) (A := A) (R' := C)
          (Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hij) AlgEquiv.refl
            ((Algebra.TensorProduct.lid
              (FixedPoints.subalgebra R A G) C).symm c)) := by
    intro c
    refine Subtype.ext ?_
    rw [Algebra.TensorProduct.lid_symm_apply]
    simp only [Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul, fixedPointsBaseChange_tmul,
      includeRightFixedPoints_coe, map_one, OneMemClass.coe_one]
    rfl
  have hcomp :
      ⇑(includeRightFixedPoints (G := G) (R := R) (A := A) C) =
        ⇑(fixedPointsBaseChange
          (G := G) (R := FixedPoints.subalgebra R A G) (A := A) (R' := C)) ∘
        ⇑(Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hij) AlgEquiv.refl) ∘
        ⇑(Algebra.TensorProduct.lid
          (FixedPoints.subalgebra R A G) C).symm :=
    funext hfun
  rw [hcomp]
  exact hbc.comp ((Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hij)
    AlgEquiv.refl).bijective.comp
      (Algebra.TensorProduct.lid
        (FixedPoints.subalgebra R A G) C).symm.bijective)

section Affine

variable {B : Type u} [CommRing B] [MulSemiringAction G B]
variable (R : Type v) [CommRing R] [Algebra R B] [SMulCommClass G R B]

/-- A flat affine base change of an affine finite-group quotient has the
categorical quotient universal property. -/
theorem existsUnique_invariantsπ_lift_baseChange_spec_of_flat
    [Finite G] {Y : Scheme.{u}} (C : Type u) [CommRing C]
    (ψ : FixedPoints.subalgebra R B G →+* C) (hψ : RingHom.Flat ψ)
    (f : pullback (invariantsπ G B R)
      (Spec.map (CommRingCat.ofHom ψ)) ⟶ Y)
    (hf : ∀ g : G,
      pullbackSpecSMul G B R (Spec.map (CommRingCat.ofHom ψ)) g ≫ f = f) :
    ∃! q : Spec (CommRingCat.of C) ⟶ Y,
      pullback.snd (invariantsπ G B R)
        (Spec.map (CommRingCat.ofHom ψ)) ≫ q = f := by
  classical
  haveI : SMulCommClass R G B := SMulCommClass.symm G R B
  letI : Algebra (FixedPoints.subalgebra R B G) C := ψ.toAlgebra
  letI : Module.Flat (FixedPoints.subalgebra R B G) C := by
    rw [← RingHom.flat_algebraMap_iff]
    exact hψ
  let e : pullback (invariantsπ G B R)
      (Spec.map (CommRingCat.ofHom ψ)) ≅
      Spec (CommRingCat.of
        (B ⊗[FixedPoints.subalgebra R B G] C)) :=
    pullbackSpecIso (FixedPoints.subalgebra R B G) B C
  have hefst : e.inv ≫
      pullback.fst (invariantsπ G B R) (Spec.map (CommRingCat.ofHom ψ)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := FixedPoints.subalgebra R B G) (A := B) (B := C))) :=
    pullbackSpecIso_inv_fst (FixedPoints.subalgebra R B G) B C
  have hesnd : e.inv ≫
      pullback.snd (invariantsπ G B R) (Spec.map (CommRingCat.ofHom ψ)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := FixedPoints.subalgebra R B G) (A := B) (B := C)).toRingHom) :=
    pullbackSpecIso_inv_snd (FixedPoints.subalgebra R B G) B C
  have hact : ∀ g : G,
      e.inv ≫ pullbackSpecSMul G B R (Spec.map (CommRingCat.ofHom ψ)) g =
        specSMul g ≫ e.inv := by
    intro g
    have hsqL : Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := FixedPoints.subalgebra R B G) (A := B) (B := C))) ≫
          specSMul g =
        specSMul g ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := FixedPoints.subalgebra R B G) (A := B) (B := C))) := by
      rw [specSMul, specSMul, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have hsqR : Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := FixedPoints.subalgebra R B G)
            (A := B) (B := C)).toRingHom) =
        specSMul g ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := FixedPoints.subalgebra R B G)
            (A := B) (B := C)).toRingHom) := by
      rw [specSMul, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext c
      change (1 : B) ⊗ₜ[FixedPoints.subalgebra R B G] c =
        g • ((1 : B) ⊗ₜ[FixedPoints.subalgebra R B G] c)
      rw [MulSemiringAction.smul_tmul_baseChange, smul_one]
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullbackSpecSMul_fst]
      rw [← Category.assoc, hefst]
      exact hsqL
    · simp only [Category.assoc, pullbackSpecSMul_snd]
      rw [hesnd]
      exact hsqR
  have hf' : ∀ g : G, specSMul g ≫ (e.inv ≫ f) = e.inv ≫ f := by
    intro g
    rw [← Category.assoc, ← hact g, Category.assoc, hf g]
  obtain ⟨q₀, hq₀⟩ := exists_invariantsπ_lift G
    (B ⊗[FixedPoints.subalgebra R B G] C)
    (FixedPoints.subalgebra R B G) (e.inv ≫ f) hf'
  let χe : C ≃+* FixedPoints.subalgebra (FixedPoints.subalgebra R B G)
      (B ⊗[FixedPoints.subalgebra R B G] C) G :=
    RingEquiv.ofBijective _
      (bijective_includeRightFixedPoints_of_flat
        (G := G) (R := R) (A := B) C)
  let χinv : CommRingCat.of (FixedPoints.subalgebra
      (FixedPoints.subalgebra R B G)
      (B ⊗[FixedPoints.subalgebra R B G] C) G) ⟶ CommRingCat.of C :=
    CommRingCat.ofHom χe.symm.toRingHom
  let m : Spec (CommRingCat.of C) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra
        (FixedPoints.subalgebra R B G)
        (B ⊗[FixedPoints.subalgebra R B G] C) G)) :=
    Spec.map χinv
  letI : IsIso m := by
    dsimp only [m]
    have hbij : Function.Bijective χinv.hom :=
      ⟨fun _ _ h ↦ χe.symm.injective h,
        fun y ↦ ⟨χe y, χe.symm_apply_apply y⟩⟩
    letI : IsIso χinv :=
      (ConcreteCategory.isIso_iff_bijective χinv).mpr hbij
    infer_instance
  let q : Spec (CommRingCat.of C) ⟶ Y :=
    m ≫ q₀
  have hkey :
      (Algebra.TensorProduct.includeRight
        (R := FixedPoints.subalgebra R B G) (A := B) (B := C)).toRingHom.comp
          χe.symm.toRingHom =
      algebraMap
        (FixedPoints.subalgebra (FixedPoints.subalgebra R B G)
          (B ⊗[FixedPoints.subalgebra R B G] C) G)
        (B ⊗[FixedPoints.subalgebra R B G] C) := by
    ext x
    change (1 : B) ⊗ₜ[FixedPoints.subalgebra R B G] (χe.symm x : C) =
      (x : B ⊗[FixedPoints.subalgebra R B G] C)
    rw [← includeRightFixedPoints_coe
      (G := G) (R := R) (A := B) C (χe.symm x)]
    exact congrArg Subtype.val (χe.apply_symm_apply x)
  have hq : pullback.snd (invariantsπ G B R)
      (Spec.map (CommRingCat.ofHom ψ)) ≫ q = f := by
    rw [← cancel_epi e.inv, ← Category.assoc, hesnd,
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hkey]
    exact hq₀
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  have hpm :
      e.inv ≫ pullback.snd (invariantsπ G B R)
          (Spec.map (CommRingCat.ofHom ψ)) ≫ m =
        invariantsπ G (B ⊗[FixedPoints.subalgebra R B G] C)
          (FixedPoints.subalgebra R B G) := by
    rw [← Category.assoc, hesnd]
    dsimp only [m]
    rw [invariantsπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hkey]
  have hpχ : e.inv ≫ pullback.snd (invariantsπ G B R)
        (Spec.map (CommRingCat.ofHom ψ)) =
      invariantsπ G (B ⊗[FixedPoints.subalgebra R B G] C)
          (FixedPoints.subalgebra R B G) ≫ inv m := by
    apply (cancel_mono m).mp
    rw [Category.assoc, hpm]
    simp
  apply (cancel_epi (inv m)).mp
  apply invariantsπ_hom_ext G
    (B ⊗[FixedPoints.subalgebra R B G] C)
    (FixedPoints.subalgebra R B G)
  have hleft := congrArg (fun t ↦ t ≫ q') hpχ
  have hright := congrArg (fun t ↦ t ≫ q) hpχ
  have hq'e := congrArg (fun t ↦ e.inv ≫ t) hq'
  have hqe := congrArg (fun t ↦ e.inv ≫ t) hq
  simpa only [Category.assoc] using
    hleft.symm.trans (hq'e.trans (hqe.symm.trans hright))

/-- Comparison between two base changes of the same affine quotient. -/
noncomputable def pullbackRes {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (a : W' ⟶ W'') (ha : w = a ≫ j'') :
    pullback (invariantsπ G B R) w ⟶ pullback (invariantsπ G B R) j'' :=
  pullback.map _ _ _ _ (𝟙 _) a (𝟙 _) (by simp)
    (by rw [Category.comp_id, ha])

@[reassoc]
theorem pullbackRes_fst {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (a : W' ⟶ W'') (ha : w = a ≫ j'') :
    pullbackRes (G := G) (B := B) R j'' w a ha ≫
        pullback.fst (invariantsπ G B R) j'' =
      pullback.fst (invariantsπ G B R) w :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem pullbackRes_snd {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (a : W' ⟶ W'') (ha : w = a ≫ j'') :
    pullbackRes (G := G) (B := B) R j'' w a ha ≫
        pullback.snd (invariantsπ G B R) j'' =
      pullback.snd (invariantsπ G B R) w ≫ a :=
  pullback.lift_snd _ _ _

/-- The comparison between base changes intertwines their induced actions. -/
theorem pullbackSpecSMul_pullbackRes {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (a : W' ⟶ W'') (ha : w = a ≫ j'') (g : G) :
    pullbackSpecSMul G B R w g ≫
        pullbackRes (G := G) (B := B) R j'' w a ha =
      pullbackRes (G := G) (B := B) R j'' w a ha ≫
        pullbackSpecSMul G B R j'' g := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackRes_fst, pullbackRes_fst_assoc,
      pullbackSpecSMul_fst]
  · simp only [Category.assoc, pullbackRes_snd, pullbackSpecSMul_snd,
      pullbackSpecSMul_snd_assoc]

/-- Flat affine base change of the invariants quotient, with an arbitrary
affine scheme as base. -/
theorem existsUnique_invariantsπ_lift_baseChange_of_isAffine
    [Finite G] {W Y : Scheme.{u}} [IsAffine W]
    (w : W ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) [Flat w]
    (f : pullback (invariantsπ G B R) w ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R w g ≫ f = f) :
    ∃! q : W ⟶ Y, pullback.snd (invariantsπ G B R) w ≫ q = f := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ w)
  haveI : Flat (W.isoSpec.inv ≫ w) := by infer_instance
  haveI : Flat (Spec.map ψ) := hψ ▸ inferInstance
  have hψflat : RingHom.Flat ψ.hom :=
    Flat.SpecMap_iff.mp (inferInstance : Flat (Spec.map ψ))
  let ρ := pullbackRes (G := G) (B := B) R w
    (Spec.map ψ) W.isoSpec.inv hψ
  letI : IsIso ρ := by
    dsimp only [ρ, pullbackRes]
    infer_instance
  have hfρ : ∀ g : G, pullbackSpecSMul G B R (Spec.map ψ) g ≫
      (ρ ≫ f) = ρ ≫ f := by
    intro g
    rw [← Category.assoc, pullbackSpecSMul_pullbackRes, Category.assoc, hf g]
  obtain ⟨q₀, hq₀, hu₀⟩ :=
    existsUnique_invariantsπ_lift_baseChange_spec_of_flat
      (G := G) (R := R) (B := B) Γ(W, ⊤) ψ.hom hψflat (ρ ≫ f) hfρ
  let q : W ⟶ Y := W.isoSpec.hom ≫ q₀
  have hq : pullback.snd (invariantsπ G B R) w ≫ q = f := by
    apply (cancel_epi ρ).mp
    rw [← Category.assoc, pullbackRes_snd, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact hq₀
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  have hq'₀ : pullback.snd (invariantsπ G B R) (Spec.map ψ) ≫
      (W.isoSpec.inv ≫ q') = ρ ≫ f := by
    rw [← Category.assoc, ← pullbackRes_snd, Category.assoc, hq']
  have hu : W.isoSpec.inv ≫ q' = q₀ := hu₀ _ hq'₀
  apply (cancel_epi W.isoSpec.inv).mp
  rw [hu]
  simp [q]

/-- A flat base change of an affine invariants projection is an epimorphism,
even when the new base scheme is not affine. -/
theorem epi_pullback_snd_invariantsπ_of_flat
    [Finite G] {W : Scheme.{u}}
    (w : W ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) [Flat w] :
    Epi (pullback.snd (invariantsπ G B R) w) := by
  constructor
  intro Y f₁ f₂ h
  apply Scheme.Cover.hom_ext W.affineCover
  intro i
  let wi := W.affineCover.f i ≫ w
  let pi := pullback.snd (invariantsπ G B R) wi
  let ρ := pullbackRes (G := G) (B := B) R w wi
    (W.affineCover.f i) rfl
  haveI : Flat wi := by
    dsimp only [wi]
    infer_instance
  haveI : Epi pi := by
    constructor
    intro Z a b hab
    have ha : ∀ g : G, pullbackSpecSMul G B R wi g ≫ (pi ≫ a) = pi ≫ a := by
      intro g
      rw [← Category.assoc, pullbackSpecSMul_snd]
    obtain ⟨q, -, hu⟩ :=
      existsUnique_invariantsπ_lift_baseChange_of_isAffine
        (G := G) (B := B) R wi (pi ≫ a) ha
    exact (hu a rfl).trans (hu b hab.symm).symm
  apply (cancel_epi pi).mp
  have hρ : ρ ≫ pullback.snd (invariantsπ G B R) w =
      pi ≫ W.affineCover.f i :=
    pullbackRes_snd (G := G) (B := B) R w wi
      (W.affineCover.f i) rfl
  have hρ₁ := congrArg (fun t ↦ t ≫ f₁) hρ
  have hρ₂ := congrArg (fun t ↦ t ≫ f₂) hρ
  have hh := congrArg (fun t ↦ ρ ≫ t) h
  simpa only [Category.assoc] using hρ₁.symm.trans (hh.trans hρ₂)

/-- Flat base change preserves the categorical quotient universal property of
an affine invariants projection, over an arbitrary base scheme. -/
theorem existsUnique_invariantsπ_lift_baseChange_of_flat
    [Finite G] {W Y : Scheme.{u}}
    (w : W ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) [Flat w]
    (f : pullback (invariantsπ G B R) w ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R w g ≫ f = f) :
    ∃! q : W ⟶ Y, pullback.snd (invariantsπ G B R) w ≫ q = f := by
  classical
  have hfx : ∀ (x : W.affineCover.I₀) (g : G),
      pullbackSpecSMul G B R (W.affineCover.f x ≫ w) g ≫
        (pullbackRes (G := G) (B := B) R w (W.affineCover.f x ≫ w)
          (W.affineCover.f x) rfl ≫ f) =
      pullbackRes (G := G) (B := B) R w (W.affineCover.f x ≫ w)
        (W.affineCover.f x) rfl ≫ f := by
    intro x g
    rw [← Category.assoc, pullbackSpecSMul_pullbackRes, Category.assoc, hf g]
  choose qx hqx using fun x : W.affineCover.I₀ ↦
    (existsUnique_invariantsπ_lift_baseChange_of_isAffine
      (G := G) (B := B) R (W.affineCover.f x ≫ w)
      (pullbackRes (G := G) (B := B) R w (W.affineCover.f x ≫ w)
        (W.affineCover.f x) rfl ≫ f) (hfx x)).exists
  have hcompat : ∀ x z : W.affineCover.I₀,
      pullback.fst (W.affineCover.f x) (W.affineCover.f z) ≫ qx x =
      pullback.snd (W.affineCover.f x) (W.affineCover.f z) ≫ qx z := by
    intro x z
    have hbase : pullback.fst (W.affineCover.f x) (W.affineCover.f z) ≫
        W.affineCover.f x ≫ w =
        pullback.snd (W.affineCover.f x) (W.affineCover.f z) ≫
          W.affineCover.f z ≫ w := by
      rw [← Category.assoc, ← Category.assoc, pullback.condition]
    have hσρ : pullbackRes (G := G) (B := B) R (W.affineCover.f x ≫ w)
          (pullback.fst (W.affineCover.f x) (W.affineCover.f z) ≫
            W.affineCover.f x ≫ w)
          (pullback.fst (W.affineCover.f x) (W.affineCover.f z)) rfl ≫
          pullbackRes (G := G) (B := B) R w (W.affineCover.f x ≫ w)
            (W.affineCover.f x) rfl =
        pullbackRes (G := G) (B := B) R (W.affineCover.f z ≫ w)
          (pullback.fst (W.affineCover.f x) (W.affineCover.f z) ≫
            W.affineCover.f x ≫ w)
          (pullback.snd (W.affineCover.f x) (W.affineCover.f z)) hbase ≫
          pullbackRes (G := G) (B := B) R w (W.affineCover.f z ≫ w)
            (W.affineCover.f z) rfl := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullbackRes_fst]
      · simp only [Category.assoc, pullbackRes_snd, pullbackRes_snd_assoc]
        rw [pullback.condition]
    let wxz := pullback.fst (W.affineCover.f x) (W.affineCover.f z) ≫
      W.affineCover.f x ≫ w
    haveI : Flat wxz := by
      dsimp only [wxz]
      infer_instance
    haveI := epi_pullback_snd_invariantsπ_of_flat
      (G := G) (B := B) R wxz
    apply (cancel_epi (pullback.snd (invariantsπ G B R) wxz)).mp
    calc
      pullback.snd (invariantsπ G B R) wxz ≫
          pullback.fst (W.affineCover.f x) (W.affineCover.f z) ≫ qx x =
        (pullback.snd (invariantsπ G B R) wxz ≫
          pullback.fst (W.affineCover.f x) (W.affineCover.f z)) ≫ qx x :=
            (Category.assoc _ _ _).symm
      _ =
        (pullbackRes (G := G) (B := B) R (W.affineCover.f x ≫ w) wxz
          (pullback.fst (W.affineCover.f x) (W.affineCover.f z)) rfl ≫
          pullback.snd (invariantsπ G B R) (W.affineCover.f x ≫ w)) ≫ qx x := by
          rw [pullbackRes_snd]
      _ = pullbackRes (G := G) (B := B) R (W.affineCover.f x ≫ w) wxz
            (pullback.fst (W.affineCover.f x) (W.affineCover.f z)) rfl ≫
          pullback.snd (invariantsπ G B R) (W.affineCover.f x ≫ w) ≫ qx x :=
            Category.assoc _ _ _
      _ = pullbackRes (G := G) (B := B) R (W.affineCover.f x ≫ w) wxz
            (pullback.fst (W.affineCover.f x) (W.affineCover.f z)) rfl ≫
          pullbackRes (G := G) (B := B) R w (W.affineCover.f x ≫ w)
            (W.affineCover.f x) rfl ≫ f := by
          rw [hqx x]
      _ = (pullbackRes (G := G) (B := B) R (W.affineCover.f x ≫ w) wxz
            (pullback.fst (W.affineCover.f x) (W.affineCover.f z)) rfl ≫
          pullbackRes (G := G) (B := B) R w (W.affineCover.f x ≫ w)
            (W.affineCover.f x) rfl) ≫ f :=
          (Category.assoc _ _ _).symm
      _ = (pullbackRes (G := G) (B := B) R (W.affineCover.f z ≫ w) wxz
            (pullback.snd (W.affineCover.f x) (W.affineCover.f z)) hbase ≫
          pullbackRes (G := G) (B := B) R w (W.affineCover.f z ≫ w)
            (W.affineCover.f z) rfl) ≫ f := by
          simpa only [wxz] using congrArg (fun t ↦ t ≫ f) hσρ
      _ = pullbackRes (G := G) (B := B) R (W.affineCover.f z ≫ w) wxz
            (pullback.snd (W.affineCover.f x) (W.affineCover.f z)) hbase ≫
          pullbackRes (G := G) (B := B) R w (W.affineCover.f z ≫ w)
            (W.affineCover.f z) rfl ≫ f :=
          Category.assoc _ _ _
      _ = pullbackRes (G := G) (B := B) R (W.affineCover.f z ≫ w) wxz
            (pullback.snd (W.affineCover.f x) (W.affineCover.f z)) hbase ≫
          pullback.snd (invariantsπ G B R) (W.affineCover.f z ≫ w) ≫ qx z := by
          rw [← hqx z]
      _ = (pullbackRes (G := G) (B := B) R (W.affineCover.f z ≫ w) wxz
            (pullback.snd (W.affineCover.f x) (W.affineCover.f z)) hbase ≫
          pullback.snd (invariantsπ G B R) (W.affineCover.f z ≫ w)) ≫ qx z :=
          (Category.assoc _ _ _).symm
      _ = (pullback.snd (invariantsπ G B R) wxz ≫
          pullback.snd (W.affineCover.f x) (W.affineCover.f z)) ≫ qx z := by
          rw [pullbackRes_snd]
      _ = pullback.snd (invariantsπ G B R) wxz ≫
          pullback.snd (W.affineCover.f x) (W.affineCover.f z) ≫ qx z := by
          rw [Category.assoc]
  have hq : pullback.snd (invariantsπ G B R) w ≫
      W.affineCover.glueMorphisms qx hcompat = f := by
    refine Scheme.Cover.hom_ext
      (W.affineCover.pullback₁ (pullback.snd (invariantsπ G B R) w)) _ _ fun x ↦ ?_
    change pullback.fst (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) ≫
        pullback.snd (invariantsπ G B R) w ≫
          W.affineCover.glueMorphisms qx hcompat =
      pullback.fst (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) ≫ f
    have hcond :
        pullback.fst (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) ≫
            pullback.snd (invariantsπ G B R) w =
          pullback.snd (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) ≫
            W.affineCover.f x :=
      pullback.condition
    rw [← Category.assoc, hcond, Category.assoc]
    rw [W.affineCover.ι_glueMorphisms qx hcompat x]
    let θ : pullback (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) ⟶
        pullback (invariantsπ G B R) (W.affineCover.f x ≫ w) :=
      pullback.lift
        (pullback.fst (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) ≫
          pullback.fst (invariantsπ G B R) w)
        (pullback.snd (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x))
        (by
          rw [Category.assoc, pullback.condition (f := invariantsπ G B R) (g := w),
            ← Category.assoc, hcond, Category.assoc])
    have hθsnd : θ ≫ pullback.snd (invariantsπ G B R) (W.affineCover.f x ≫ w) =
        pullback.snd (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) :=
      pullback.lift_snd _ _ _
    have hθρ : θ ≫ pullbackRes (G := G) (B := B) R w
        (W.affineCover.f x ≫ w) (W.affineCover.f x) rfl =
        pullback.fst (pullback.snd (invariantsπ G B R) w) (W.affineCover.f x) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullbackRes_fst, pullback.lift_fst]
      · rw [Category.assoc, pullbackRes_snd, ← Category.assoc, hθsnd, hcond]
    rw [← hθsnd, Category.assoc, hqx x, ← Category.assoc, hθρ]
  refine ⟨W.affineCover.glueMorphisms qx hcompat, hq, ?_⟩
  intro q' hq'
  haveI := epi_pullback_snd_invariantsπ_of_flat
    (G := G) (B := B) R w
  apply (cancel_epi (pullback.snd (invariantsπ G B R) w)).mp
  exact hq'.trans hq.symm

end Affine

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotientFlatBaseChange
