/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.Etale
import MazurTorsion.Upstream.AINTLIB.ForMathlib.InvariantTorsor

/-!
# Finite étale cancellation along a split cover ([GHB6-RING])

The ring-level core of KM 7.1.3(6) (freeness-sharpened): in a tower `R → B → A` with
`B → A` formally étale, flat and **split** (a `B`-linear retraction of `algebraMap B A`),
if `R → A` is finite étale then `R → B` is étale (and module-finite).

This is étale *source-cancellation* — cancel the **second** factor of `R → B → A` — which
mathlib does not provide (its `RingHom.Etale.codescendsAlong_faithfullyFlat` and the scheme
`DescendsAlong` instances are *base-change* descent). The splitting (available for the
invariants inclusion `Aᴳ ↪ A` of a free action via the trace, `exists_traceInvariants_eq_one`)
replaces the flat-spreading argument (Stacks 02JO) the general fppf statement would need:

* finiteness and flatness of `B` over `R` pass through the retract directly;
* `A` is a finite projective `R`-module (`Module.FinitePresentation.of_finite_of_finitePresentation`
  + `Module.Flat.projective_of_finitePresentation`), so its retract `B` is finite projective,
  hence a finitely presented `R`-module, hence a finitely presented `R`-algebra;
* `Ω[B⁄R]` vanishes because `A ⊗[B] Ω[B⁄R] ≅ Ω[A⁄R] = 0`
  (`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`) and `A` is faithfully flat over `B`;
* `Algebra.Etale.of_formallyUnramified_of_flat` (Stacks 08WD) assembles étaleness from
  finite presentation + flatness + unramifiedness — no smoothness argument needed.

The invariants instantiation (`RingHom.invariantsCorestrict_finite` /
`RingHom.invariantsCorestrict_etale`) feeds the scheme-level [GHB6] discharge in
`ForMathlib/SchemeActionFree.lean`: the descended structure map of a free quotient is
finite étale over each affine chart of the base.
-/

universe u v

open TensorProduct

section Retract

variable (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]

/-- A flat algebra with a linear retraction of its unit is faithfully flat: `N ≅ N ⊗[B] B`
is a retract of `N ⊗[B] A`, so triviality reflects. -/
theorem Module.FaithfullyFlat.of_flat_of_retract [Module.Flat B A]
    (ρ : A →ₗ[B] B) (hρ : ρ.comp (Algebra.linearMap B A) = LinearMap.id) :
    Module.FaithfullyFlat B A := by
  refine (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality B A).mpr
    ⟨inferInstance, fun N _ _ hN => ?_⟩
  haveI := hN
  have hmid : (ρ.lTensor N).comp ((Algebra.linearMap B A).lTensor N) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hρ, LinearMap.lTensor_id]
  refine subsingleton_of_forall_eq 0 fun n => ?_
  have h1 : (ρ.lTensor N) (((Algebra.linearMap B A).lTensor N)
      ((TensorProduct.rid B N).symm n)) = (TensorProduct.rid B N).symm n :=
    LinearMap.congr_fun hmid ((TensorProduct.rid B N).symm n)
  have h0 : ((Algebra.linearMap B A).lTensor N) ((TensorProduct.rid B N).symm n) = 0 :=
    Subsingleton.elim _ _
  have h2 : ((TensorProduct.rid B N).symm n : N ⊗[B] B) = 0 := by
    rw [← h1, h0, map_zero]
  have h3 := congrArg (TensorProduct.rid B N) h2
  simpa using h3

variable {R B A}

/-- Module-finiteness cancels along a split second factor: if `A` is a finite `R`-module and
`B → A` has a `B`-linear retraction, then `B` is a finite `R`-module. -/
theorem Module.Finite.of_comp_of_retract [Module.Finite R A]
    (ρ : A →ₗ[B] B) (hρ : ρ.comp (Algebra.linearMap B A) = LinearMap.id) :
    Module.Finite R B :=
  Module.Finite.of_surjective (ρ.restrictScalars R)
    (fun b => ⟨algebraMap B A b, LinearMap.congr_fun hρ b⟩)

/-- **Finite étale cancellation along a split cover** (the [GHB6-RING] crown; KM 7.1.3(6),
ring level). In a tower `R → B → A` with `B → A` formally étale, flat and split by a
`B`-linear retraction, if `R → A` is finite étale then `R → B` is étale. -/
theorem Algebra.Etale.of_comp_of_retract [Module.Finite R A] [Algebra.Etale R A]
    [Algebra.FormallyEtale B A] [Module.Flat B A]
    (ρ : A →ₗ[B] B) (hρ : ρ.comp (Algebra.linearMap B A) = LinearMap.id) :
    Algebra.Etale R B := by
  haveI hff : Module.FaithfullyFlat B A := .of_flat_of_retract B A ρ hρ
  -- `A` is flat over `R` (étale ⟹ smooth ⟹ flat)
  haveI : Algebra.Smooth R A := ⟨inferInstance, inferInstance⟩
  -- `B` is a finite flat `R`-module (retract of the finite flat `A`)
  haveI : Module.Finite R B := .of_comp_of_retract ρ hρ
  haveI : Module.Flat R B := Module.Flat.of_retract
    ((Algebra.linearMap B A).restrictScalars R) (ρ.restrictScalars R)
    (by ext b; exact LinearMap.congr_fun hρ b)
  -- `A` is a finite projective `R`-module, so its retract `B` is finite projective,
  -- hence a finitely presented `R`-module, hence a finitely presented `R`-algebra
  haveI : Module.FinitePresentation R A := .of_finite_of_finitePresentation R A
  haveI : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  haveI : Module.Projective R B := Module.Projective.of_split
    ((Algebra.linearMap B A).restrictScalars R) (ρ.restrictScalars R)
    (by ext b; exact LinearMap.congr_fun hρ b)
  haveI : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  haveI : Algebra.FinitePresentation R B := .of_finitePresentation R B
  -- `Ω[B⁄R]` vanishes: `A ⊗[B] Ω[B⁄R] ≅ Ω[A⁄R] = 0` and `A` is faithfully flat over `B`
  haveI : Subsingleton (A ⊗[B] Ω[B⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B A).toEquiv.subsingleton
  haveI : Subsingleton (Ω[B⁄R]) :=
    Module.FaithfullyFlat.lTensor_reflects_triviality B A (Ω[B⁄R])
  haveI : Algebra.FormallyUnramified R B := ⟨inferInstance⟩
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Retract

section Invariants

variable (G : Type*) [Group G] [_root_.Finite G] (R₀ : Type v) (A : Type u) [CommRing R₀]
  [CommRing A] [Algebra R₀ A] [MulSemiringAction G A] [SMulCommClass G R₀ A]
  [SMulCommClass R₀ G A]

omit [SMulCommClass R₀ G A] in
/-- The trace retraction `a ↦ tr(c·a)` of the invariants inclusion `Aᴳ ↪ A` of a free
action, where `tr(c) = 1` (`exists_traceInvariants_eq_one`). -/
theorem exists_retract_invariants (hfree : IsFreeAlgebraAction G R₀ A) :
    ∃ ρ : A →ₗ[FixedPoints.subalgebra R₀ A G] FixedPoints.subalgebra R₀ A G,
      ρ.comp (Algebra.linearMap (FixedPoints.subalgebra R₀ A G) A) = LinearMap.id := by
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := exists_traceInvariants_eq_one G R₀ A hfree
  refine ⟨(traceLinear G R₀ A).comp
    (LinearMap.mulLeft (FixedPoints.subalgebra R₀ A G) c), ?_⟩
  refine LinearMap.ext fun b => ?_
  change traceLinear G R₀ A (c * algebraMap (FixedPoints.subalgebra R₀ A G) A b) = b
  have hsm : c * algebraMap (FixedPoints.subalgebra R₀ A G) A b = b • c := by
    rw [Algebra.smul_def, mul_comm]
  rw [hsm, map_smul, hc, smul_eq_mul, mul_one]

variable {G R₀ A}

/-- The corestriction of an invariant ring map to the invariants subalgebra. -/
def RingHom.invariantsCorestrict {R : Type*} [CommRing R] (φ : R →+* A)
    (hφ : ∀ (g : G) (r : R), g • φ r = φ r) :
    R →+* FixedPoints.subalgebra R₀ A G :=
  φ.codRestrict _ fun r g => hφ g r

variable {R : Type u} [CommRing R] (φ : R →+* A) (hφ : ∀ (g : G) (r : R), g • φ r = φ r)

omit [SMulCommClass R₀ G A] in
/-- **[GHB6-RING], finiteness of the invariants base** — if `R → A` is module-finite and the
`G`-action is free, the corestriction `R → Aᴳ` is module-finite. -/
theorem RingHom.invariantsCorestrict_finite
    (hfree : IsFreeAlgebraAction G R₀ A) (hfin : φ.Finite) :
    (φ.invariantsCorestrict (R₀ := R₀) hφ).Finite := by
  algebraize [φ, (φ.invariantsCorestrict (R₀ := R₀) hφ)]
  haveI : IsScalarTower R (FixedPoints.subalgebra R₀ A G) A :=
    .of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]; rfl
  haveI : Module.Finite R A := hfin
  obtain ⟨ρ, hρ⟩ := exists_retract_invariants G R₀ A hfree
  exact Module.Finite.of_comp_of_retract ρ hρ

omit [SMulCommClass R₀ G A] in
/-- **[GHB6-RING], étaleness of the invariants base** — if `R → A` is finite étale and the
`G`-action is free, the corestriction `R → Aᴳ` is étale. -/
theorem RingHom.invariantsCorestrict_etale
    (hfree : IsFreeAlgebraAction G R₀ A) (hfin : φ.Finite) (het : φ.Etale) :
    (φ.invariantsCorestrict (R₀ := R₀) hφ).Etale := by
  algebraize [φ, (φ.invariantsCorestrict (R₀ := R₀) hφ)]
  haveI : IsScalarTower R (FixedPoints.subalgebra R₀ A G) A :=
    .of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]; rfl
  haveI : Module.Finite R A := hfin
  haveI : Algebra.Etale R A := het
  haveI : Algebra.Etale (FixedPoints.subalgebra R₀ A G) A :=
    Algebra.Etale.of_isFreeAlgebraAction G R₀ A hfree
  haveI : Module.Flat (FixedPoints.subalgebra R₀ A G) A := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_retract_invariants G R₀ A hfree
  exact Algebra.Etale.of_comp_of_retract ρ hρ

end Invariants
