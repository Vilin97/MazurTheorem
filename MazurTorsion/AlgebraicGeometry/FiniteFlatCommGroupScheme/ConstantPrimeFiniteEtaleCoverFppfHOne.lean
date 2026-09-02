/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeIntegralFppfHOne

/-!
# Finite-etale constant cocycles as genuine global fppf classes

A positive-rank finite etale integer algebra has an integral point.  Its affine spectrum is
therefore not merely a formal singleton family: the structural morphism is etale and surjective,
so it defines an actual fppf `Scheme.Cover` of `Spec ℤ`.

The cover-level contraction proved in `ConstantPrimeIntegralFppfHOne` then shows that every
represented constant-group class on this cover is trivial.  Applying the real globalization map
`Scheme.FppfHOne.mk` proves that its image is the distinguished global class.  Concrete order-five
and order-eleven endpoints are included below.

This closes the cover-to-global quotient step for classes already represented on a finite etale
singleton cover.  It does not assert the still-missing effective-descent theorem which constructs
such a torsor cover from an arbitrary fppf cocycle.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

private noncomputable def finiteEtaleIntSection
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B) :
    Spec (.of ℤ) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (exists_intAlgHom B hB).some.toRingHom)

private theorem finiteEtaleIntSection_comp_structureMap
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B) :
    finiteEtaleIntSection B hB ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) =
      𝟙 (Spec (.of ℤ)) := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
  ext z
  exact (exists_intAlgHom B hB).some.commutes z

/-- The actual singleton fppf cover of `Spec ℤ` defined by a positive-rank finite etale
integer algebra.  Its index type is `Unit`, matching the cover-level contraction API. -/
noncomputable def finiteEtaleIntSingletonCover
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B) :
    Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of ℤ)) := by
  let f : Spec (.of B) ⟶ Spec (.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ B))
  letI : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  letI : Surjective f := ⟨by
    intro z
    refine ⟨finiteEtaleIntSection B hB z, ?_⟩
    have hz := congrArg
      (fun g : Spec (.of ℤ) ⟶ Spec (.of ℤ) ↦ g z)
      (finiteEtaleIntSection_comp_structureMap B hB)
    simpa [f] using hz⟩
  refine
    { I₀ := Unit
      X := fun _ ↦ Spec (.of B)
      f := fun _ ↦ f
      mem₀ := ?_ }
  rw [PreZeroHypercover.presieve₀, Presieve.ofArrows_of_unique]
  exact Scheme.Hom.singleton_mem_fppfPrecoverage f

/-- The sole object of the finite etale singleton cover is the expected affine test object in
the slice over `Spec ℤ`. -/
theorem finiteEtaleIntSingletonCover_overFamily
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B) :
    (finiteEtaleIntSingletonCover B hB).overFamily =
      (fun _ : Unit ↦ AffineCommGroupScheme.testObject (R := ℤ) B) := by
  rfl

/-- Every represented constant-group class on the actual finite etale singleton cover maps to
the distinguished global fppf class. -/
theorem finiteEtaleConstantFppfHOneClass_eq_one
    (G : Type) [CommGroup G] [Fintype G]
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hB : 0 < Module.finrank ℤ B)
    (z : H1 (pointPresheaf (constantScheme ℤ G))
      (finiteEtaleIntSingletonCover B hB).overFamily) :
  Scheme.FppfHOne.mk (finiteEtaleIntSingletonCover B hB) z =
      (1 : (constantScheme ℤ G).FppfHOne.{0}) := by
  have hz : z = 1 := finiteEtaleConstantHOne_eq_one G B hB z
  rw [hz]
  exact Scheme.FppfHOne.mk_one (finiteEtaleIntSingletonCover B hB)

/-- The genuine order-five global endpoint for a rank-five finite etale singleton cover. -/
theorem constantFiveFiniteEtaleFppfHOneClass_eq_one
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 5)
    (z : H1 (pointPresheaf (constantScheme ℤ (Multiplicative (ZMod 5))))
      (finiteEtaleIntSingletonCover B (by simp [hrank])).overFamily) :
    Scheme.FppfHOne.mk (finiteEtaleIntSingletonCover B (by simp [hrank])) z =
      (1 : (constantScheme ℤ (Multiplicative (ZMod 5))).FppfHOne.{0}) :=
  finiteEtaleConstantFppfHOneClass_eq_one
    (Multiplicative (ZMod 5)) B (by simp [hrank]) z

/-- The genuine order-eleven global endpoint for a rank-eleven finite etale singleton cover. -/
theorem constantElevenFiniteEtaleFppfHOneClass_eq_one
    (B : Type) [CommRing B] [Module.Finite ℤ B] [Algebra.Etale ℤ B]
    (hrank : Module.finrank ℤ B = 11)
    (z : H1 (pointPresheaf (constantScheme ℤ (Multiplicative (ZMod 11))))
      (finiteEtaleIntSingletonCover B (by simp [hrank])).overFamily) :
    Scheme.FppfHOne.mk (finiteEtaleIntSingletonCover B (by simp [hrank])) z =
      (1 : (constantScheme ℤ (Multiplicative (ZMod 11))).FppfHOne.{0}) :=
  finiteEtaleConstantFppfHOneClass_eq_one
    (Multiplicative (ZMod 11)) B (by simp [hrank]) z

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale
