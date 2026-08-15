/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedEquivalence

/-!
# Natural maps into scalar twists

A scalar unit cocycle changes the transition maps of a cover-descent
datum while leaving its chart modules unchanged.  A family of functions
on the charts therefore gives a morphism from a descent datum to its
scalar twist precisely when the functions transform by that cocycle.

This file packages the resulting morphism, its naturality in the module,
and the corresponding natural transformation after effective descent.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})

namespace CoverDescentData

variable {D}

/--
A family of chart functions is compatible with an overlap-unit cocycle
when the function from the first chart, followed by the transition unit,
equals the function from the second chart on every overlap.
-/
def CoverScalarSectionCompatibility
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (b : ∀ i, Γ(D.U i, ⊤)) : Prop :=
  ∀ i j,
    (D.f i j).appTop (b i) * (a i j).val =
      (D.t i j ≫ D.f j i).appTop (b j)

/--
Multiplication by a compatible chart-function family defines a morphism
from any descent datum to its scalar twist.
-/
noncomputable def scalarTwistHom
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (b : ∀ i, Γ(D.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b)
    (A : CoverDescentData D) :
    A ⟶ (scalarTwistFunctor a hself hcocycle).obj A where
  app i := scalarEndomorphism (A.chart i) (b i)
  compatible := by
    intro i j
    change
      (pullback (D.f i j)).map
            (scalarEndomorphism (A.chart i) (b i)) ≫
          (A.transition i j).hom ≫
          scalarEndomorphism
            ((pullback (D.t i j ≫ D.f j i)).obj
              (A.chart j))
            (a i j).val =
        (A.transition i j).hom ≫
          (pullback (D.t i j ≫ D.f j i)).map
            (scalarEndomorphism (A.chart j) (b j))
    rw [pullback_scalarEndomorphism,
      pullback_scalarEndomorphism]
    rw [← Category.assoc,
      scalarEndomorphism_naturality
        (A.transition i j).hom
        ((D.f i j).appTop (b i))]
    rw [Category.assoc,
      scalarEndomorphism_comp,
      hb i j]

@[simp]
theorem scalarTwistHom_app
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (b : ∀ i, Γ(D.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b)
    (A : CoverDescentData D) (i : D.J) :
    (scalarTwistHom a hself hcocycle b hb A).app i =
      scalarEndomorphism (A.chart i) (b i) :=
  rfl

/--
The compatible chartwise multiplication maps are natural in the descent
datum.
-/
noncomputable def scalarTwistNatTrans
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (b : ∀ i, Γ(D.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b) :
    𝟭 (CoverDescentData D) ⟶
      scalarTwistFunctor a hself hcocycle where
  app A := scalarTwistHom a hself hcocycle b hb A
  naturality {A B} φ := by
    apply Hom.ext
    intro i
    simpa only [comp_app, Functor.id_obj, Functor.id_map,
      scalarTwistFunctor_obj_chart,
      scalarTwistHom_app, scalarTwistFunctor_map_app] using
        (scalarEndomorphism_naturality
          (φ.app i) (b i)).symm

@[simp]
theorem scalarTwistNatTrans_app_app
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (b : ∀ i, Γ(D.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b)
    (A : CoverDescentData D) (i : D.J) :
    ((scalarTwistNatTrans
        a hself hcocycle b hb).app A).app i =
      scalarEndomorphism (A.chart i) (b i) :=
  rfl

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
