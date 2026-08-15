/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistedCoverDescent

/-!
# Scalar twisting as an autoequivalence of cover descent data

Multiplying every overlap transition by a scalar unit leaves the chart
modules unchanged.  A unit cocycle therefore defines an endofunctor on
cover descent data.  Pointwise inversion of the cocycle gives its inverse.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})

namespace CoverDescentData

variable {D}

/-- Modify an arbitrary descent transition by a scalar unit on its target. -/
def scalarTwistedTransition
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (i j : D.J) :
    (pullback (D.f i j)).obj (A.chart i) ≅
      (pullback (D.t i j ≫ D.f j i)).obj
        (A.chart j) :=
  A.transition i j ≪≫
    scalarIso
      ((pullback (D.t i j ≫ D.f j i)).obj
        (A.chart j))
      (a i j)

/-- Scalar twisting preserves the diagonal identity law. -/
theorem scalarTwistedTransition_self
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1) (i : D.J) :
    scalarTwistedTransition A a i i =
      eqToIso (congrArg
        (fun φ => (pullback φ).obj (A.chart i))
        (show D.f i i = D.t i i ≫ D.f i i by
          rw [D.t_id i, Category.id_comp])) := by
  rw [scalarTwistedTransition, hself i,
    scalarIso_one, Iso.trans_refl, A.identity i]

/-- A morphism of descent data remains compatible after both transition
families are modified by the same scalar cocycle. -/
theorem scalarTwistedTransition_naturality
    {A B : CoverDescentData D} (φ : A ⟶ B)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (i j : D.J) :
    (pullback (D.f i j)).map (φ.app i) ≫
      (scalarTwistedTransition B a i j).hom =
      (scalarTwistedTransition A a i j).hom ≫
        (pullback (D.t i j ≫ D.f j i)).map
          (φ.app j) := by
  let q :=
    (pullback (D.t i j ≫ D.f j i)).map
      (φ.app j)
  have hscalar :=
    scalarEndomorphism_naturality q (a i j).val
  change
    (pullback (D.f i j)).map (φ.app i) ≫
        (B.transition i j).hom ≫
        scalarEndomorphism _ (a i j).val =
      (A.transition i j).hom ≫
        scalarEndomorphism _ (a i j).val ≫ q
  rw [← Category.assoc, φ.compatible i j,
    Category.assoc, ← hscalar]

/-- Scalar-twisted arbitrary descent transitions satisfy the cocycle law. -/
theorem scalarTwistedTransition_cocycle
    (A : CoverDescentData D)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j k : D.J) :
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i)
        (scalarTwistedTransition A a i j) ≪≫
      (pullbackCongr (glueData_bridge_mid D i j k)).app
        (A.chart j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j)
        (scalarTwistedTransition A a j k) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
        (A.chart k)
    =
      (pullbackCongr (glueData_bridge_src D i j k)).app
          (A.chart i) ≪≫
        pullbackBaseChangeTransport
          (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i)
          (scalarTwistedTransition A a i k) := by
  have hunit :
      coverUnitPullback₁₂ D a i j k *
          coverUnitPullback₂₃ D a i j k =
        coverUnitPullback₁₃ D a i j k :=
    hcocycle i j k
  have hchain :=
    scalarIso_twisted_chain
      (pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i)
        (A.transition i j))
      ((pullbackCongr (glueData_bridge_mid D i j k)).app
        (A.chart j))
      (pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j)
        (A.transition j k))
      ((pullbackCongr (glueData_bridge_tgt D i j k)).app
        (A.chart k))
      (coverUnitPullback₁₂ D a i j k)
      (coverUnitPullback₂₃ D a i j k)
  unfold scalarTwistedTransition
  rw [pullbackBaseChangeTransport_trans_scalarIso,
    pullbackBaseChangeTransport_trans_scalarIso,
    pullbackBaseChangeTransport_trans_scalarIso]
  change
    (pullbackBaseChangeTransport
          (pullback.fst (D.f i j) (D.f i k))
          (D.f i j) (D.t i j ≫ D.f j i)
          (A.transition i j) ≪≫
        scalarIso _
          (coverUnitPullback₁₂ D a i j k)) ≪≫
      (pullbackCongr (glueData_bridge_mid D i j k)).app
          (A.chart j) ≪≫
      (pullbackBaseChangeTransport
          (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
          (D.f j k) (D.t j k ≫ D.f k j)
          (A.transition j k) ≪≫
        scalarIso _
          (coverUnitPullback₂₃ D a i j k)) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
          (A.chart k) =
    (pullbackCongr (glueData_bridge_src D i j k)).app
          (A.chart i) ≪≫
      (pullbackBaseChangeTransport
          (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i)
          (A.transition i k) ≪≫
        scalarIso _
          (coverUnitPullback₁₃ D a i j k))
  calc
    (pullbackBaseChangeTransport
            (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i)
            (A.transition i j) ≪≫
          scalarIso _
            (coverUnitPullback₁₂ D a i j k)) ≪≫
        (pullbackCongr (glueData_bridge_mid D i j k)).app
            (A.chart j) ≪≫
        (pullbackBaseChangeTransport
            (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j)
            (A.transition j k) ≪≫
          scalarIso _
            (coverUnitPullback₂₃ D a i j k)) ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k)).app
            (A.chart k) =
      (pullbackBaseChangeTransport
            (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i)
            (A.transition i j) ≪≫
        (pullbackCongr (glueData_bridge_mid D i j k)).app
            (A.chart j) ≪≫
        pullbackBaseChangeTransport
            (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j)
            (A.transition j k) ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k)).app
            (A.chart k)) ≪≫
          scalarIso _
            (coverUnitPullback₁₂ D a i j k *
              coverUnitPullback₂₃ D a i j k) := by
        simpa only [Iso.trans_assoc] using hchain
    _ =
      ((pullbackCongr (glueData_bridge_src D i j k)).app
            (A.chart i) ≪≫
        pullbackBaseChangeTransport
            (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i)
            (A.transition i k)) ≪≫
          scalarIso _
            (coverUnitPullback₁₂ D a i j k *
              coverUnitPullback₂₃ D a i j k) := by
        exact congrArg
          (fun e =>
            e ≪≫ scalarIso _
              (coverUnitPullback₁₂ D a i j k *
                coverUnitPullback₂₃ D a i j k))
          (A.cocycle i j k)
    _ =
      ((pullbackCongr (glueData_bridge_src D i j k)).app
            (A.chart i) ≪≫
        pullbackBaseChangeTransport
            (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i)
            (A.transition i k)) ≪≫
          scalarIso _
            (coverUnitPullback₁₃ D a i j k) := by
        rw [hunit]
    _ =
      (pullbackCongr (glueData_bridge_src D i j k)).app
            (A.chart i) ≪≫
        (pullbackBaseChangeTransport
            (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i)
            (A.transition i k) ≪≫
          scalarIso _
            (coverUnitPullback₁₃ D a i j k)) := by
        exact Iso.trans_assoc _ _ _

/-- Twist a cover descent datum by a scalar unit cocycle. -/
noncomputable def scalarTwistObject
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (A : CoverDescentData D) :
    CoverDescentData D where
  chart := A.chart
  transition := scalarTwistedTransition A a
  identity := scalarTwistedTransition_self A a hself
  cocycle := scalarTwistedTransition_cocycle A a hcocycle

/-- Scalar twisting acts identically on chartwise morphisms. -/
noncomputable def scalarTwistFunctor
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a) :
    CoverDescentData D ⥤ CoverDescentData D where
  obj := scalarTwistObject a hself hcocycle
  map {A B} φ :=
    { app := φ.app
      compatible :=
        scalarTwistedTransition_naturality
          φ a }
  map_id A := by
    apply Hom.ext
    intro i
    rfl
  map_comp {A B C} φ ψ := by
    apply Hom.ext
    intro i
    rfl

@[simp]
theorem scalarTwistObject_chart
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (A : CoverDescentData D) (i : D.J) :
    (scalarTwistObject a hself hcocycle A).chart i =
      A.chart i :=
  rfl

@[simp]
theorem scalarTwistFunctor_obj_chart
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (A : CoverDescentData D) (i : D.J) :
    ((scalarTwistFunctor a hself hcocycle).obj A).chart i =
      A.chart i :=
  rfl

@[simp]
theorem scalarTwistFunctor_map_app
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    {A B : CoverDescentData D} (φ : A ⟶ B) (i : D.J) :
    ((scalarTwistFunctor a hself hcocycle).map φ).app i =
      φ.app i :=
  rfl

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
