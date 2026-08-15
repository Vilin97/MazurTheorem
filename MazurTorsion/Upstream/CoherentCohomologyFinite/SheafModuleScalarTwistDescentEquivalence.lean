/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistDescentFunctor

/-!
# Invertibility of scalar twisting on cover descent data

The inverse of a unit cocycle is again a unit cocycle.  Twisting first by
a cocycle and then by its pointwise inverse restores every transition.
Consequently scalar twisting is an equivalence of descent-data categories.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})

namespace CoverDescentData

variable {D}

/-- Pointwise inverse of an overlap-unit family. -/
def inverseCoverUnit
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ) :
    ∀ i j, Γ(D.V (i, j), ⊤)ˣ :=
  fun i j => (a i j)⁻¹

/-- The pointwise inverse of a diagonal-one unit family is diagonal-one. -/
theorem inverseCoverUnit_self
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1) :
    ∀ i, inverseCoverUnit a i i = 1 := by
  intro i
  rw [inverseCoverUnit, hself i, inv_one]

/-- The pointwise inverse of a scalar cover cocycle is again a cocycle. -/
theorem inverseCoverUnit_cocycle
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hcocycle : CoverUnitCocycleCondition D a) :
    CoverUnitCocycleCondition D
      (inverseCoverUnit a) := by
  intro i j k
  change
    (coverUnitPullback₁₂ D a i j k)⁻¹ *
        (coverUnitPullback₂₃ D a i j k)⁻¹ =
      (coverUnitPullback₁₃ D a i j k)⁻¹
  rw [← hcocycle i j k, mul_inv_rev]
  exact mul_comm _ _

/-- Twisting by a unit family and then by its inverse restores the
original transition. -/
theorem scalarTwistedTransition_inverse
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j : D.J) :
    scalarTwistedTransition
        (scalarTwistObject
          a hself hcocycle A)
        (inverseCoverUnit a) i j =
      A.transition i j := by
  change
    (A.transition i j ≪≫ scalarIso _ (a i j)) ≪≫
        scalarIso _ (inverseCoverUnit a i j) =
      A.transition i j
  rw [Iso.trans_assoc, scalarIso_mul]
  simp [inverseCoverUnit]

/-- Twisting by the inverse unit family and then by the original family
also restores the original transition. -/
theorem scalarTwistedTransition_inverse_left
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j : D.J) :
    scalarTwistedTransition
        (scalarTwistObject
          (inverseCoverUnit a)
          (inverseCoverUnit_self a hself)
          (inverseCoverUnit_cocycle a hcocycle) A)
        a i j =
      A.transition i j := by
  change
    (A.transition i j ≪≫
        scalarIso _ (inverseCoverUnit a i j)) ≪≫
      scalarIso _ (a i j) =
        A.transition i j
  rw [Iso.trans_assoc, scalarIso_mul]
  simp [inverseCoverUnit]

/-- The twice-twisted transition as a morphism between the original chart
pullbacks.  This typed wrapper prevents chart-field transparency from
interfering with categorical identity simplification. -/
def scalarTwistedTransitionInverseHom
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j : D.J) :
    (pullback (D.f i j)).obj (A.chart i) ⟶
      (pullback (D.t i j ≫ D.f j i)).obj (A.chart j) :=
  (scalarTwistedTransition
    (scalarTwistObject a hself hcocycle A)
    (inverseCoverUnit a) i j).hom

theorem scalarTwistedTransitionInverseHom_eq
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j : D.J) :
    scalarTwistedTransitionInverseHom A a hself hcocycle i j =
      (A.transition i j).hom :=
  congrArg Iso.hom
    (scalarTwistedTransition_inverse A a hself hcocycle i j)

/-- The reverse-order twice-twisted transition in the original chart
types. -/
def scalarInverseTwistedTransitionHom
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j : D.J) :
    (pullback (D.f i j)).obj (A.chart i) ⟶
      (pullback (D.t i j ≫ D.f j i)).obj (A.chart j) :=
  (scalarTwistedTransition
    (scalarTwistObject (inverseCoverUnit a)
      (inverseCoverUnit_self a hself)
      (inverseCoverUnit_cocycle a hcocycle) A)
    a i j).hom

theorem scalarInverseTwistedTransitionHom_eq
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j : D.J) :
    scalarInverseTwistedTransitionHom A a hself hcocycle i j =
      (A.transition i j).hom :=
  congrArg Iso.hom
    (scalarTwistedTransition_inverse_left A a hself hcocycle i j)

section

variable
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)

local notation "a⁻¹ᶜ" => inverseCoverUnit a

/-- The two successive twists by `a` and `a⁻¹` are canonically the
identity on each descent datum. -/
noncomputable def scalarTwistInverseIso
    (A : CoverDescentData D) :
    (scalarTwistFunctor a hself hcocycle ⋙
      scalarTwistFunctor a⁻¹ᶜ
        (inverseCoverUnit_self a hself)
        (inverseCoverUnit_cocycle a hcocycle)).obj A ≅ A := by
  let g :
      A ⟶
        (scalarTwistFunctor a hself hcocycle ⋙
          scalarTwistFunctor a⁻¹ᶜ
            (inverseCoverUnit_self a hself)
            (inverseCoverUnit_cocycle a hcocycle)).obj A :=
    { app := fun i => 𝟙 (A.chart i)
      compatible := by
        intro i j
        change
          (pullback (D.f i j)).map (𝟙 (A.chart i)) ≫
              scalarTwistedTransitionInverseHom
                A a hself hcocycle i j =
            (A.transition i j).hom ≫
              (pullback (D.t i j ≫ D.f j i)).map
                (𝟙 (A.chart j))
        let t := scalarTwistedTransitionInverseHom
          A a hself hcocycle i j
        let u := (A.transition i j).hom
        have hi := (pullback (D.f i j)).map_id (A.chart i)
        have hj :=
          (pullback (D.t i j ≫ D.f j i)).map_id (A.chart j)
        have ht : t = u :=
          scalarTwistedTransitionInverseHom_eq A a hself hcocycle i j
        rw [hi, hj, Category.id_comp, Category.comp_id]
        exact ht }
  letI : ∀ i, IsIso (g.app i) := by
    intro i
    change IsIso
      (𝟙 (A.chart i) : A.chart i ⟶ A.chart i)
    infer_instance
  exact g.isoOfComponents.symm

@[simp]
theorem scalarTwistInverseIso_inv_app
    (A : CoverDescentData D) (i : D.J) :
    (scalarTwistInverseIso a hself hcocycle A).inv.app i =
      𝟙 (A.chart i) :=
  rfl

/-- Naturality of cancellation of a twist with its inverse. -/
theorem scalarTwistInverseIso_naturality
    {A B : CoverDescentData D} (φ : A ⟶ B) :
    (scalarTwistFunctor a hself hcocycle ⋙
        scalarTwistFunctor a⁻¹ᶜ
          (inverseCoverUnit_self a hself)
          (inverseCoverUnit_cocycle a hcocycle)).map φ ≫
        (scalarTwistInverseIso a hself hcocycle B).hom =
      (scalarTwistInverseIso a hself hcocycle A).hom ≫ φ := by
  let eA := scalarTwistInverseIso a hself hcocycle A
  let eB := scalarTwistInverseIso a hself hcocycle B
  have hinv :
      φ ≫ eB.inv =
        eA.inv ≫
          (scalarTwistFunctor a hself hcocycle ⋙
            scalarTwistFunctor a⁻¹ᶜ
              (inverseCoverUnit_self a hself)
              (inverseCoverUnit_cocycle a hcocycle)).map φ := by
    apply Hom.ext
    intro i
    simp [eA, eB]
  apply (cancel_mono eB.inv).1
  rw [Category.assoc, eB.hom_inv_id, Category.comp_id]
  rw [Category.assoc, hinv, ← Category.assoc,
    eA.hom_inv_id, Category.id_comp]

/-- Cancellation of a twist with its inverse as a natural isomorphism. -/
noncomputable def scalarTwistInverseNatIso :
    scalarTwistFunctor a hself hcocycle ⋙
        scalarTwistFunctor a⁻¹ᶜ
          (inverseCoverUnit_self a hself)
          (inverseCoverUnit_cocycle a hcocycle) ≅
      𝟭 (CoverDescentData D) :=
  NatIso.ofComponents
    (scalarTwistInverseIso a hself hcocycle)
    (fun φ =>
      scalarTwistInverseIso_naturality
        a hself hcocycle φ)

/-- Cancellation in the reverse order. -/
noncomputable def scalarInverseTwistIso
    (A : CoverDescentData D) :
    (scalarTwistFunctor a⁻¹ᶜ
          (inverseCoverUnit_self a hself)
          (inverseCoverUnit_cocycle a hcocycle) ⋙
      scalarTwistFunctor a hself hcocycle).obj A ≅ A := by
  let g :
      A ⟶
        (scalarTwistFunctor a⁻¹ᶜ
              (inverseCoverUnit_self a hself)
              (inverseCoverUnit_cocycle a hcocycle) ⋙
          scalarTwistFunctor a hself hcocycle).obj A :=
    { app := fun i => 𝟙 (A.chart i)
      compatible := by
        intro i j
        change
          (pullback (D.f i j)).map (𝟙 (A.chart i)) ≫
              scalarInverseTwistedTransitionHom
                A a hself hcocycle i j =
            (A.transition i j).hom ≫
              (pullback (D.t i j ≫ D.f j i)).map
                (𝟙 (A.chart j))
        let t := scalarInverseTwistedTransitionHom
          A a hself hcocycle i j
        let u := (A.transition i j).hom
        have hi := (pullback (D.f i j)).map_id (A.chart i)
        have hj :=
          (pullback (D.t i j ≫ D.f j i)).map_id (A.chart j)
        have ht : t = u :=
          scalarInverseTwistedTransitionHom_eq A a hself hcocycle i j
        rw [hi, hj, Category.id_comp, Category.comp_id]
        exact ht }
  letI : ∀ i, IsIso (g.app i) := by
    intro i
    change IsIso
      (𝟙 (A.chart i) : A.chart i ⟶ A.chart i)
    infer_instance
  exact g.isoOfComponents.symm

@[simp]
theorem scalarInverseTwistIso_inv_app
    (A : CoverDescentData D) (i : D.J) :
    (scalarInverseTwistIso a hself hcocycle A).inv.app i =
      𝟙 (A.chart i) :=
  rfl

/-- Naturality of reverse-order cancellation. -/
theorem scalarInverseTwistIso_naturality
    {A B : CoverDescentData D} (φ : A ⟶ B) :
    (scalarTwistFunctor a⁻¹ᶜ
          (inverseCoverUnit_self a hself)
          (inverseCoverUnit_cocycle a hcocycle) ⋙
        scalarTwistFunctor a hself hcocycle).map φ ≫
        (scalarInverseTwistIso a hself hcocycle B).hom =
      (scalarInverseTwistIso a hself hcocycle A).hom ≫ φ := by
  let eA := scalarInverseTwistIso a hself hcocycle A
  let eB := scalarInverseTwistIso a hself hcocycle B
  have hinv :
      φ ≫ eB.inv =
        eA.inv ≫
          (scalarTwistFunctor a⁻¹ᶜ
                (inverseCoverUnit_self a hself)
                (inverseCoverUnit_cocycle a hcocycle) ⋙
            scalarTwistFunctor a hself hcocycle).map φ := by
    apply Hom.ext
    intro i
    simp [eA, eB]
  apply (cancel_mono eB.inv).1
  rw [Category.assoc, eB.hom_inv_id, Category.comp_id]
  rw [Category.assoc, hinv, ← Category.assoc,
    eA.hom_inv_id, Category.id_comp]

/-- Reverse-order cancellation as a natural isomorphism. -/
noncomputable def scalarInverseTwistNatIso :
    scalarTwistFunctor a⁻¹ᶜ
          (inverseCoverUnit_self a hself)
          (inverseCoverUnit_cocycle a hcocycle) ⋙
        scalarTwistFunctor a hself hcocycle ≅
      𝟭 (CoverDescentData D) :=
  NatIso.ofComponents
    (scalarInverseTwistIso a hself hcocycle)
    (fun φ =>
      scalarInverseTwistIso_naturality
        a hself hcocycle φ)

/-- Scalar twisting by a cover-unit cocycle is an equivalence. -/
noncomputable def scalarTwistEquivalence :
    CoverDescentData D ≌ CoverDescentData D where
  functor := scalarTwistFunctor a hself hcocycle
  inverse :=
    scalarTwistFunctor a⁻¹ᶜ
      (inverseCoverUnit_self a hself)
      (inverseCoverUnit_cocycle a hcocycle)
  unitIso :=
    (scalarTwistInverseNatIso
      a hself hcocycle).symm
  counitIso :=
    scalarInverseTwistNatIso
      a hself hcocycle
  functor_unitIso_comp A := by
    apply Hom.ext
    intro i
    simp [scalarTwistInverseNatIso,
      scalarInverseTwistNatIso,
      scalarTwistInverseIso,
      scalarInverseTwistIso,
      Hom.isoOfComponents,
      Hom.inverseOfComponents]

end

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
