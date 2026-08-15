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

end Affine

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotientFlatBaseChange
