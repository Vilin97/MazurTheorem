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

namespace AlgebraicGeometry.SchemeAction

open MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotientFlatBaseChange

variable {G : Type*} [Group G] [Finite G]
variable {X : Scheme.{u}} (σ : SchemeAction G X)
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x))
  (hVa : ∀ x, IsAffineOpen (V x)) (hVmem : ∀ x : X, x ∈ V x)

/-- Chart-local form of flat base change for a global finite-group quotient.
The base map is assumed to factor through one quotient chart, where the claim
is transported to the affine invariants theorem. -/
theorem existsUnique_quotientπ_lift_baseChange_of_flat_of_factors
    {WT Y : Scheme.{u}} (x : X) (wq : WT ⟶ σ.quotient V hVs hVa)
    (wc : WT ⟶ (σ.quotientChart V hVs hVa x : Scheme.{u})) [Flat wc]
    (hw : wq = wc ≫ (σ.quotientChart V hVs hVa x).ι)
    (F : pullback (σ.quotientπ V hVs hVa hVmem) wq ⟶ Y)
    (hF : ∀ g : G, σ.pullbackQuotientπSMul V hVs hVa hVmem wq g ≫ F = F) :
    ∃! q : WT ⟶ Y, pullback.snd (σ.quotientπ V hVs hVa hVmem) wq ≫ q = F := by
  classical
  letI := σ.gammaMulSemiringAction (hVs x)
  let jS : WT ⟶ σ.localQuotient (hVs x) :=
    wc ≫ (σ.quotientChartIso V hVs hVa x).inv
  haveI : Flat jS := by
    dsimp only [jS]
    infer_instance
  have sq1 : IsPullback ((hVa x).isoSpec.inv) (invariantsπ G ↑Γ(X, V x) ℤ)
      (σ.localQuotientπ (hVs x) (hVa x)) (𝟙 (σ.localQuotient (hVs x))) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, localQuotientπ_eq σ (hVs x) (hVa x), Iso.inv_hom_id_assoc]
  have sq2 : IsPullback (𝟙 ((V x : Scheme.{u}))) (σ.localQuotientπ (hVs x) (hVa x))
      (σ.localQuotientπ (hVs x) (hVa x) ≫ (σ.quotientChartIso V hVs hVa x).hom)
      ((σ.quotientChartIso V hVs hVa x).hom) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.id_comp]
  have hpaste := (IsPullback.of_hasPullback (invariantsπ G ↑Γ(X, V x) ℤ)
      jS).paste_horiz ((sq1.paste_horiz sq2).paste_horiz
        (σ.isPullback_quotientπ_quotientChart V hVs hVa hVmem x))
  have htop : (((hVa x).isoSpec.inv ≫ 𝟙 (V x : Scheme.{u})) ≫ (V x).ι) =
      (hVa x).isoSpec.inv ≫ (V x).ι := by
    rw [Category.comp_id]
  have hbot : ((𝟙 (σ.localQuotient (hVs x)) ≫
      (σ.quotientChartIso V hVs hVa x).hom) ≫
      (σ.quotientChart V hVs hVa x).ι) =
      (σ.quotientChartIso V hVs hVa x).hom ≫
        (σ.quotientChart V hVs hVa x).ι := by
    rw [Category.id_comp]
  rw [htop, hbot] at hpaste
  have hbot2 : jS ≫ (σ.quotientChartIso V hVs hVa x).hom ≫
      (σ.quotientChart V hVs hVa x).ι = wq := by
    dsimp only [jS]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← hw]
  rw [hbot2] at hpaste
  let E := hpaste.isoPullback
  have hEfst : E.hom ≫ pullback.fst (σ.quotientπ V hVs hVa hVmem) wq =
      pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
        (hVa x).isoSpec.inv ≫ (V x).ι :=
    hpaste.isoPullback_hom_fst
  have hEsnd : E.hom ≫ pullback.snd (σ.quotientπ V hVs hVa hVmem) wq =
      pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) jS :=
    hpaste.isoPullback_hom_snd
  have hact : ∀ g : G, E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g =
      pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫ E.hom := by
    intro g
    refine pullback.hom_ext ?_ ?_
    · calc
        (E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g) ≫
            pullback.fst (σ.quotientπ V hVs hVa hVmem) wq =
          E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g ≫
            pullback.fst (σ.quotientπ V hVs hVa hVmem) wq :=
          Category.assoc _ _ _
        _ = E.hom ≫ pullback.fst (σ.quotientπ V hVs hVa hVmem) wq ≫ σ.hom g := by
          rw [pullbackQuotientπSMul_fst]
        _ = (E.hom ≫ pullback.fst (σ.quotientπ V hVs hVa hVmem) wq) ≫ σ.hom g :=
          (Category.assoc _ _ _).symm
        _ = (pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
            (hVa x).isoSpec.inv ≫ (V x).ι) ≫ σ.hom g := by rw [hEfst]
        _ = pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
            (hVa x).isoSpec.inv ≫ (V x).ι ≫ σ.hom g := by
          rw [Category.assoc, Category.assoc]
        _ = pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
            (hVa x).isoSpec.inv ≫
            (σ.hom g).resLE (V x) (V x) ((hVs x).le_preimage g) ≫ (V x).ι := by
          rw [Scheme.Hom.resLE_comp_ι]
        _ = pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
            ((hVa x).isoSpec.inv ≫
              (σ.hom g).resLE (V x) (V x) ((hVs x).le_preimage g)) ≫ (V x).ι := by
          rw [Category.assoc]
        _ = pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
            (specSMul g ≫ (hVa x).isoSpec.inv) ≫ (V x).ι := by
          rw [specSMul_isoSpec_inv σ (hVs x) (hVa x) g]
        _ = (pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫ specSMul g) ≫
            (hVa x).isoSpec.inv ≫ (V x).ι := by
          rw [Category.assoc, Category.assoc]
        _ = (pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
            pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS) ≫
            (hVa x).isoSpec.inv ≫ (V x).ι := by
          rw [pullbackSpecSMul_fst]
        _ = pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
            (E.hom ≫ pullback.fst (σ.quotientπ V hVs hVa hVmem) wq) := by
          rw [hEfst, Category.assoc]
        _ = (pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫ E.hom) ≫
            pullback.fst (σ.quotientπ V hVs hVa hVmem) wq :=
          (Category.assoc _ _ _).symm
    · calc
        (E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g) ≫
            pullback.snd (σ.quotientπ V hVs hVa hVmem) wq =
          E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g ≫
            pullback.snd (σ.quotientπ V hVs hVa hVmem) wq :=
          Category.assoc _ _ _
        _ = E.hom ≫ pullback.snd (σ.quotientπ V hVs hVa hVmem) wq := by
          rw [pullbackQuotientπSMul_snd]
        _ = pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) jS := hEsnd
        _ = pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
            pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) jS := by
          rw [pullbackSpecSMul_snd]
        _ = pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
            (E.hom ≫ pullback.snd (σ.quotientπ V hVs hVa hVmem) wq) := by
          rw [hEsnd]
        _ = (pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫ E.hom) ≫
            pullback.snd (σ.quotientπ V hVs hVa hVmem) wq :=
          (Category.assoc _ _ _).symm
  have hFE : ∀ g : G, pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
      (E.hom ≫ F) = E.hom ≫ F := by
    intro g
    rw [← Category.assoc, ← hact g, Category.assoc, hF g]
  obtain ⟨q, hq, hu⟩ := existsUnique_invariantsπ_lift_baseChange_of_flat
    (G := G) (B := ↑Γ(X, V x)) ℤ jS (E.hom ≫ F) hFE
  have hq' : pullback.snd (σ.quotientπ V hVs hVa hVmem) wq ≫ q = F := by
    apply (cancel_epi E.hom).mp
    rw [← Category.assoc, hEsnd]
    exact hq
  refine ⟨q, hq', ?_⟩
  intro q' hq''
  apply hu q'
  have hqE := congrArg (fun t ↦ E.hom ≫ t) hq''
  rw [← Category.assoc, hEsnd] at hqE
  exact hqE

/-- After a flat base change, the projection from a global finite-group
quotient is an epimorphism.  This is checked on the quotient-chart cover and
reduced there to the affine invariant-ring theorem. -/
theorem epi_pullback_snd_quotientπ_of_flat
    {W : Scheme.{u}} (w : W ⟶ σ.quotient V hVs hVa) [Flat w] :
    Epi (pullback.snd (σ.quotientπ V hVs hVa hVmem) w) := by
  constructor
  intro Y f₁ f₂ h
  apply Scheme.Cover.hom_ext (σ.chartCover V hVs hVa w)
  intro x
  let wx := pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w
  let wc := pullback.snd w (σ.quotientChart V hVs hVa x).ι
  let p := pullback.snd (σ.quotientπ V hVs hVa hVmem) wx
  let ρ := σ.pullbackResQ V hVs hVa hVmem w wx
    (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl
  haveI : Flat wc := by
    dsimp only [wc]
    infer_instance
  have hwc : wx = wc ≫ (σ.quotientChart V hVs hVa x).ι := by
    dsimp only [wx, wc]
    exact pullback.condition
  have hpinv : ∀ g : G,
      σ.pullbackQuotientπSMul V hVs hVa hVmem wx g ≫
        (p ≫ ((σ.chartCover V hVs hVa w).f x ≫ f₁)) =
      p ≫ ((σ.chartCover V hVs hVa w).f x ≫ f₁) := by
    intro g
    rw [← Category.assoc, pullbackQuotientπSMul_snd]
  obtain ⟨q, -, hu⟩ :=
    σ.existsUnique_quotientπ_lift_baseChange_of_flat_of_factors
      V hVs hVa hVmem x wx wc hwc
      (p ≫ ((σ.chartCover V hVs hVa w).f x ≫ f₁)) hpinv
  have hρ : ρ ≫ pullback.snd (σ.quotientπ V hVs hVa hVmem) w =
      p ≫ (σ.chartCover V hVs hVa w).f x := by
    exact σ.pullbackResQ_snd V hVs hVa hVmem w wx
      (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl
  have hlocal : p ≫ ((σ.chartCover V hVs hVa w).f x ≫ f₁) =
      p ≫ ((σ.chartCover V hVs hVa w).f x ≫ f₂) := by
    have hρ₁ := congrArg (fun t ↦ t ≫ f₁) hρ
    have hρ₂ := congrArg (fun t ↦ t ≫ f₂) hρ
    have hh := congrArg (fun t ↦ ρ ≫ t) h
    simpa only [Category.assoc] using hρ₁.symm.trans (hh.trans hρ₂)
  exact (hu _ rfl).trans (hu _ hlocal.symm).symm

/-- Formation of a global finite-group quotient commutes with flat base
change, expressed by the categorical quotient universal property. -/
theorem existsUnique_quotientπ_lift_baseChange_of_flat
    {W Y : Scheme.{u}} (w : W ⟶ σ.quotient V hVs hVa) [Flat w]
    (F : pullback (σ.quotientπ V hVs hVa hVmem) w ⟶ Y)
    (hF : ∀ g : G, σ.pullbackQuotientπSMul V hVs hVa hVmem w g ≫ F = F) :
    ∃! q : W ⟶ Y, pullback.snd (σ.quotientπ V hVs hVa hVmem) w ≫ q = F := by
  classical
  have hFx : ∀ (x : X) (g : G),
      σ.pullbackQuotientπSMul V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w) g ≫
        (σ.pullbackResQ V hVs hVa hVmem w
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl ≫ F) =
      σ.pullbackResQ V hVs hVa hVmem w
        (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
        (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl ≫ F := by
    intro x g
    rw [← Category.assoc, pullbackQuotientπSMul_pullbackResQ,
      Category.assoc, hF g]
  have hlocal : ∀ x : X, ∃! q : (σ.chartCover V hVs hVa w).X x ⟶ Y,
      pullback.snd (σ.quotientπ V hVs hVa hVmem)
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w) ≫ q =
        σ.pullbackResQ V hVs hVa hVmem w
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl ≫ F := by
    intro x
    letI : Flat (pullback.snd w (σ.quotientChart V hVs hVa x).ι) := by
      infer_instance
    exact σ.existsUnique_quotientπ_lift_baseChange_of_flat_of_factors
      V hVs hVa hVmem x
      (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
      (pullback.snd w (σ.quotientChart V hVs hVa x).ι)
      pullback.condition
      (σ.pullbackResQ V hVs hVa hVmem w
        (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
        (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl ≫ F)
      (hFx x)
  choose qx hqx using fun x : X ↦ (hlocal x).exists
  have hcompat : ∀ x z : X,
      pullback.fst ((σ.chartCover V hVs hVa w).f x)
          ((σ.chartCover V hVs hVa w).f z) ≫ qx x =
      pullback.snd ((σ.chartCover V hVs hVa w).f x)
          ((σ.chartCover V hVs hVa w).f z) ≫ qx z := by
    intro x z
    rw [chartCover_f, chartCover_f]
    have hbase : pullback.fst
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
          (pullback.fst w (σ.quotientChart V hVs hVa z).ι) ≫
          pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w =
        pullback.snd
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
          (pullback.fst w (σ.quotientChart V hVs hVa z).ι) ≫
          pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w := by
      rw [← Category.assoc, ← Category.assoc, pullback.condition]
    let wxz := pullback.fst
      (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
      (pullback.fst w (σ.quotientChart V hVs hVa z).ι) ≫
      pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w
    have hσρ : σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w) wxz
          (pullback.fst
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) rfl ≫
          σ.pullbackResQ V hVs hVa hVmem w
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl =
        σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w) wxz
          (pullback.snd
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) hbase ≫
          σ.pullbackResQ V hVs hVa hVmem w
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι) rfl := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullbackResQ_fst]
      · simp only [Category.assoc, pullbackResQ_snd, pullbackResQ_snd_assoc]
        rw [pullback.condition]
    haveI : Flat wxz := by
      dsimp only [wxz]
      infer_instance
    haveI := σ.epi_pullback_snd_quotientπ_of_flat V hVs hVa hVmem wxz
    apply (cancel_epi (pullback.snd (σ.quotientπ V hVs hVa hVmem) wxz)).mp
    calc
      pullback.snd (σ.quotientπ V hVs hVa hVmem) wxz ≫
          pullback.fst
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι) ≫ qx x =
        (pullback.snd (σ.quotientπ V hVs hVa hVmem) wxz ≫
          pullback.fst
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) ≫ qx x :=
          (Category.assoc _ _ _).symm
      _ = (σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w) wxz
          (pullback.fst
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) rfl ≫
          pullback.snd (σ.quotientπ V hVs hVa hVmem)
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)) ≫ qx x := by
          rw [pullbackResQ_snd]
      _ = σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w) wxz
          (pullback.fst
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) rfl ≫
          σ.pullbackResQ V hVs hVa hVmem w
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl ≫ F := by
          rw [Category.assoc, hqx x]
      _ = (σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w) wxz
          (pullback.fst
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) rfl ≫
          σ.pullbackResQ V hVs hVa hVmem w
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w)
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι) rfl) ≫ F :=
          (Category.assoc _ _ _).symm
      _ = (σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w) wxz
          (pullback.snd
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) hbase ≫
          σ.pullbackResQ V hVs hVa hVmem w
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι) rfl) ≫ F := by
          simpa only [wxz] using congrArg (fun t ↦ t ≫ F) hσρ
      _ = σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w) wxz
          (pullback.snd
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) hbase ≫
          σ.pullbackResQ V hVs hVa hVmem w
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι) rfl ≫ F :=
          Category.assoc _ _ _
      _ = σ.pullbackResQ V hVs hVa hVmem
          (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w) wxz
          (pullback.snd
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι)) hbase ≫
          pullback.snd (σ.quotientπ V hVs hVa hVmem)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι ≫ w) ≫ qx z := by
          rw [← hqx z]
      _ = pullback.snd (σ.quotientπ V hVs hVa hVmem) wxz ≫
          pullback.snd
            (pullback.fst w (σ.quotientChart V hVs hVa x).ι)
            (pullback.fst w (σ.quotientChart V hVs hVa z).ι) ≫ qx z := by
          rw [← Category.assoc, pullbackResQ_snd, Category.assoc]
  let q := (σ.chartCover V hVs hVa w).glueMorphisms qx hcompat
  have hq : pullback.snd (σ.quotientπ V hVs hVa hVmem) w ≫ q = F := by
    refine Scheme.Cover.hom_ext
      ((σ.chartCover V hVs hVa w).pullback₁
        (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)) _ _ fun x ↦ ?_
    change pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
        ((σ.chartCover V hVs hVa w).f x) ≫
        pullback.snd (σ.quotientπ V hVs hVa hVmem) w ≫ q =
      pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
        ((σ.chartCover V hVs hVa w).f x) ≫ F
    have hcond : pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
          ((σ.chartCover V hVs hVa w).f x) ≫
          pullback.snd (σ.quotientπ V hVs hVa hVmem) w =
        pullback.snd (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
          ((σ.chartCover V hVs hVa w).f x) ≫
          (σ.chartCover V hVs hVa w).f x :=
      pullback.condition
    rw [← Category.assoc, hcond, Category.assoc]
    dsimp only [q]
    rw [(σ.chartCover V hVs hVa w).ι_glueMorphisms qx hcompat x]
    let θ : pullback (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
          ((σ.chartCover V hVs hVa w).f x) ⟶
        pullback (σ.quotientπ V hVs hVa hVmem)
          ((σ.chartCover V hVs hVa w).f x ≫ w) :=
      pullback.lift
        (pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
          ((σ.chartCover V hVs hVa w).f x) ≫
          pullback.fst (σ.quotientπ V hVs hVa hVmem) w)
        (pullback.snd (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
          ((σ.chartCover V hVs hVa w).f x))
        (by
          rw [Category.assoc,
            pullback.condition (f := σ.quotientπ V hVs hVa hVmem) (g := w),
            ← Category.assoc, hcond, Category.assoc])
    have hθsnd : θ ≫ pullback.snd (σ.quotientπ V hVs hVa hVmem)
          ((σ.chartCover V hVs hVa w).f x ≫ w) =
        pullback.snd (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
          ((σ.chartCover V hVs hVa w).f x) :=
      pullback.lift_snd _ _ _
    have hθρ : θ ≫ σ.pullbackResQ V hVs hVa hVmem w
          ((σ.chartCover V hVs hVa w).f x ≫ w)
          ((σ.chartCover V hVs hVa w).f x) rfl =
        pullback.fst (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)
          ((σ.chartCover V hVs hVa w).f x) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullbackResQ_fst, pullback.lift_fst]
      · rw [Category.assoc, pullbackResQ_snd, ← Category.assoc, hθsnd, hcond]
    rw [← hθsnd, Category.assoc]
    change θ ≫ pullback.snd (σ.quotientπ V hVs hVa hVmem)
        (pullback.fst w (σ.quotientChart V hVs hVa x).ι ≫ w) ≫ qx x = _
    rw [hqx x, ← Category.assoc, hθρ]
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  haveI := σ.epi_pullback_snd_quotientπ_of_flat V hVs hVa hVmem w
  apply (cancel_epi (pullback.snd (σ.quotientπ V hVs hVa hVmem) w)).mp
  exact hq'.trans hq.symm

end AlgebraicGeometry.SchemeAction
