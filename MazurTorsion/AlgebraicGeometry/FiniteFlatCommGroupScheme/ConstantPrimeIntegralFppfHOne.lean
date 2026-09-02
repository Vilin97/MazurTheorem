/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtaleIntAlgebraSplitting
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOne

/-!
# Constant cocycles on finite-etale covers of `Spec ℤ`

A singleton cover which has a section has trivial cover-level nonabelian `H¹`: evaluating a
cocycle between the section-retraction of the cover and its identity gives an actual gauge.  We
apply this contraction to a finite etale affine cover of `Spec ℤ`.  The required section is
not assumed as a certificate; it is supplied by the checked classification of finite etale
integer algebras.

Consequently every represented constant-group cocycle on a positive-rank finite etale singleton
cover is a coboundary.  The final theorems expose the genuine order-five and order-eleven
cover-level endpoints.

This file does not claim that an arbitrary fppf cocycle is represented by such a finite etale
cover.  Constructing that torsor cover, and comparing its splitting gauge with the original
cocycle, is the remaining effective-descent boundary for global constant-group `FppfHOne`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

universe u

private theorem singletonOneCocycle_isCohomologous_one_of_basePoint
    {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (U : Over S)
    (σ : Over.mk (𝟙 S) ⟶ U)
    (c : OneCocycle F (fun _ : Unit ↦ U)) :
    c.IsCohomologous 1 := by
  let π : U ⟶ Over.mk (𝟙 S) := Over.mkIdTerminal.from U
  let q : U ⟶ U := π ≫ σ
  let α : ZeroCochain F (fun _ : Unit ↦ U) :=
    fun _ ↦ c.ev () () q (𝟙 U)
  refine ⟨α, ?_⟩
  intro i j T a b
  cases i
  cases j
  change
    F.map a.op (c.ev () () q (𝟙 U)) * c.ev () () a b =
      (1 : F.obj (Opposite.op T)) * F.map b.op (c.ev () () q (𝟙 U))
  rw [c.ev_precomp () () a q (𝟙 U), c.ev_precomp () () b q (𝟙 U),
    Category.comp_id, Category.comp_id, one_mul]
  have hbase : a ≫ π = b ≫ π := Over.mkIdTerminal.hom_ext _ _
  have hq : a ≫ q = b ≫ q := by
    change a ≫ π ≫ σ = b ≫ π ≫ σ
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ σ) hbase
  rw [hq]
  exact c.ev_trans () () () (b ≫ q) a b

private noncomputable def finiteEtaleIntBasePoint
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B) :
    Over.mk (𝟙 (Spec (.of ℤ))) ⟶ AffineCommGroupScheme.testObject (R := ℤ) B :=
  (AffineCommGroupScheme.baseIsoSelfTestObject ℤ).hom ≫
    AffineCommGroupScheme.testObjectMap (exists_intAlgHom B hB).some

/-- Every represented constant-group cocycle on a positive-rank finite etale singleton cover of
`Spec ℤ` is an actual coboundary.  The base point used in the gauge is the integral section
constructed by `exists_intAlgHom`. -/
theorem finiteEtaleConstantOneCocycle_isCohomologous_one
    (G : Type) [CommGroup G] [Fintype G]
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B)
    (c : OneCocycle (pointPresheaf (constantScheme ℤ G))
      (fun _ : Unit ↦ AffineCommGroupScheme.testObject (R := ℤ) B)) :
    c.IsCohomologous 1 :=
  singletonOneCocycle_isCohomologous_one_of_basePoint
    (pointPresheaf (constantScheme ℤ G))
    (AffineCommGroupScheme.testObject (R := ℤ) B)
    (finiteEtaleIntBasePoint B hB) c

/-- Cover-level represented constant `H¹` is trivial on every positive-rank finite etale
singleton cover of `Spec ℤ`. -/
theorem finiteEtaleConstantHOne_eq_one
    (G : Type) [CommGroup G] [Fintype G]
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B)
    (z : H1 (pointPresheaf (constantScheme ℤ G))
      (fun _ : Unit ↦ AffineCommGroupScheme.testObject (R := ℤ) B)) :
    z = 1 := by
  induction z using Quot.inductionOn with
  | _ c =>
      exact (finiteEtaleConstantOneCocycle_isCohomologous_one G B hB c).class_eq

/-- The genuine order-five endpoint: a represented constant-five class on a rank-five finite
etale singleton cover of `Spec ℤ` is trivial. -/
theorem constantFiveFiniteEtaleSingletonHOne_eq_one
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 5)
    (z : H1 (pointPresheaf (constantScheme ℤ (Multiplicative (ZMod 5))))
      (fun _ : Unit ↦ AffineCommGroupScheme.testObject (R := ℤ) B)) :
    z = 1 :=
  finiteEtaleConstantHOne_eq_one (Multiplicative (ZMod 5)) B (by simp [hrank]) z

/-- The genuine order-eleven endpoint: a represented constant-eleven class on a rank-eleven
finite etale singleton cover of `Spec ℤ` is trivial. -/
theorem constantElevenFiniteEtaleSingletonHOne_eq_one
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 11)
    (z : H1 (pointPresheaf (constantScheme ℤ (Multiplicative (ZMod 11))))
      (fun _ : Unit ↦ AffineCommGroupScheme.testObject (R := ℤ) B)) :
    z = 1 :=
  finiteEtaleConstantHOne_eq_one (Multiplicative (ZMod 11)) B (by simp [hrank]) z

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale
