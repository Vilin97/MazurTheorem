/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtLinearDimensionShift
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Linear Ext from an acyclic source resolution

For a source resolution whose terms are Ext-acyclic against `B`, the
usual source-variable long-exact-sequence argument identifies `Ext` with
the homology of the coefficient-linear contravariant Hom complex.  The
comparison here lands in `ModuleCat R`; in particular, it preserves the
module structure needed for finite-generation arguments over an affine
base.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe w v u

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- Contravariant Hom into `B`, valued in modules over the coefficient
ring. -/
noncomputable abbrev linearContravariantHomFunctor (R : Type w)
    [CommRing R] [Linear R C] (B : C) :
    Cᵒᵖ ⥤ ModuleCat.{v} R :=
  (linearYoneda R C).obj B

/-- A representable coefficient-linear Hom functor is left exact. -/
instance linearContravariantHomFunctor_preservesFiniteLimits
    (B : C) :
    PreservesFiniteLimits (linearContravariantHomFunctor R B) := by
  letI :
      PreservesFiniteLimits
        (linearContravariantHomFunctor R B ⋙
          forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) := by
    change PreservesFiniteLimits (preadditiveYoneda.obj B)
    infer_instance
  exact
    preservesFiniteLimits_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

end CategoryTheory

namespace ChainComplex

universe w v u

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- Apply coefficient-linear contravariant Hom into `B` degreewise to a
chain complex. -/
noncomputable abbrev linearContravariantHomCocomplex
    (K : ChainComplex C ℕ) (R : Type w) [CommRing R] [Linear R C]
    (B : C) :
    CochainComplex (ModuleCat.{v} R) ℕ :=
  ((CategoryTheory.linearContravariantHomFunctor R B).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    K.opCocomplex

end ChainComplex

namespace CategoryTheory

universe w v u

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{v} C] [CategoryWithHomology C]

section SourceSyzygies

/-- The first Ext connecting map, written on the literal value of the
linear Yoneda functor at the cycles object. -/
noncomputable def sourceSyzygyCyclesHomToExtOneLinear
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1)) :
    (linearContravariantHomFunctor R B).obj
        (K.opCocomplex.cycles (q + 1)) →ₗ[R]
      Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1 := by
  change
    ((sourceSyzygyShortComplex K q).X₁ ⟶ B) →ₗ[R]
      Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1
  exact sourceSyzygyHomToExtOneLinear (R := R) K B q h

lemma sourceSyzygyCyclesHomToExtOneLinear_surjective
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (hacyclic :
      Subsingleton (Abelian.Ext.{v} (K.X q) B 1)) :
    Function.Surjective
      (sourceSyzygyCyclesHomToExtOneLinear (R := R) K B q h) := by
  change Function.Surjective
    (sourceSyzygyHomToExtOneLinear (R := R) K B q h)
  exact sourceSyzygyHomToExtOneLinear_surjective
    (R := R) K B q h hacyclic

/-- In the coefficient-linear Hom complex, the boundaries at the next
syzygy are exactly the kernel of the first Ext connecting map. -/
lemma sourceSyzygyLinearHomBoundaryRange_eq_ker
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1)) :
    LinearMap.range
        (((linearContravariantHomFunctor R B).map
          (K.opCocomplex.toCycles q (q + 1))).hom) =
      LinearMap.ker
        (sourceSyzygyCyclesHomToExtOneLinear (R := R) K B q h) := by
  let S := sourceSyzygyShortComplex K q
  let hS : S.ShortExact := sourceSyzygyShortExact K q h
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let yu : S.X₂ ⟶ B := y
    rw [LinearMap.mem_ker]
    change
      hS.extClass.comp
        (Abelian.Ext.mk₀ (S.f ≫ yu))
        (by omega : 1 + 0 = 1) = 0
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Abelian.Ext.mk₀ yu)
  · intro hx
    let xu : S.X₁ ⟶ B := x
    rw [LinearMap.mem_ker] at hx
    have hδ :
        hS.extClass.comp
          (Abelian.Ext.mk₀ xu)
          (by omega : 1 + 0 = 1) = 0 := by
      exact hx
    obtain ⟨z, hz⟩ :=
      Abelian.Ext.contravariant_sequence_exact₁
        hS B (Abelian.Ext.mk₀ xu)
          (by omega : 1 + 0 = 1) hδ
    refine
      ⟨Abelian.Ext.linearEquiv₀ (R := R) z, ?_⟩
    change
      S.f ≫ Abelian.Ext.linearEquiv₀ (R := R) z = xu
    apply (Abelian.Ext.mk₀_bijective _ _).injective
    calc
      Abelian.Ext.mk₀
          (S.f ≫ Abelian.Ext.linearEquiv₀ (R := R) z) =
          (Abelian.Ext.mk₀ S.f).comp
            (Abelian.Ext.mk₀
              (Abelian.Ext.linearEquiv₀ (R := R) z))
            (zero_add 0) :=
        (Abelian.Ext.mk₀_comp_mk₀ _ _).symm
      _ = (Abelian.Ext.mk₀ S.f).comp z (zero_add 0) := by
        rw [Abelian.Ext.mk₀_linearEquiv₀_apply]
      _ = Abelian.Ext.mk₀ xu := hz

/-- The cokernel at the end of the first source dimension-shift step is
linearly isomorphic to the first Ext group of the preceding syzygy. -/
noncomputable def sourceSyzygyLinearCokernelIsoExtOne
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (hacyclic :
      Subsingleton (Abelian.Ext.{v} (K.X q) B 1)) :
    cokernel
        ((linearContravariantHomFunctor R B).map
          (K.opCocomplex.toCycles q (q + 1))) ≅
      ModuleCat.of R
        (Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1) := by
  let f :=
    (linearContravariantHomFunctor R B).map
      (K.opCocomplex.toCycles q (q + 1))
  let δ :=
    sourceSyzygyCyclesHomToExtOneLinear (R := R) K B q h
  exact
    ModuleCat.cokernelIsoRangeQuotient f ≪≫
      ((Submodule.quotEquivOfEq
          (LinearMap.range f.hom)
          (LinearMap.ker δ)
          (sourceSyzygyLinearHomBoundaryRange_eq_ker
            (R := R) K B q h)).trans
        (δ.quotKerEquivOfSurjective
          (sourceSyzygyCyclesHomToExtOneLinear_surjective
            (R := R) K B q h hacyclic))).toModuleIso

/-- Positive-degree homology of the coefficient-linear Hom complex is
the first Ext group at the corresponding source syzygy. -/
noncomputable def linearContravariantHomHomologyIsoSyzygyExtOne
    (K : ChainComplex C ℕ) (B : C) (q : ℕ)
    (h : K.ExactAt (q + 1))
    (hacyclic :
      Subsingleton (Abelian.Ext.{v} (K.X q) B 1)) :
    (K.linearContravariantHomCocomplex R B).homology (q + 1) ≅
      ModuleCat.of R
        (Abelian.Ext.{v} (sourceSyzygyShortComplex K q).X₃ B 1) :=
  (linearContravariantHomFunctor R B).cohomologyAppliedResolutionIso
      K.opCocomplex q ≪≫
    sourceSyzygyLinearCokernelIsoExtOne
      (R := R) K B q h hacyclic

/-- **Coefficient-linear source acyclic resolution theorem.**

This is the projective-free source-resolution comparison: it requires
only the long exact sequence for `Ext`, so it applies to sheaf
categories even when they do not have enough projectives. -/
noncomputable def extLinearIsoHomologyOfAcyclicCoresolution
    (K : ChainComplex C ℕ) {A B : C}
    (e : K.opcycles 0 ≅ A)
    (hexact : ∀ q, K.ExactAt (q + 1))
    (hacyclic :
      ∀ q m, Subsingleton (Abelian.Ext.{v} (K.X q) B (m + 1)))
    (n : ℕ) :
    ModuleCat.of R (Abelian.Ext.{v} A B n) ≅
      (K.linearContravariantHomCocomplex R B).homology n := by
  cases n with
  | zero =>
      let eExtZero :
          ModuleCat.of R
              (Abelian.Ext.{v}
                (sourceSyzygyShortComplex K 0).X₃ B 0) ≅
            ModuleCat.of R
              ((sourceSyzygyShortComplex K 0).X₃ ⟶ B) :=
        (Abelian.Ext.linearEquiv₀
          (R := R)
          (X := (sourceSyzygyShortComplex K 0).X₃)
          (Y := B)).toModuleIso
      let eCycles :
          ModuleCat.of R
              ((sourceSyzygyShortComplex K 0).X₃ ⟶ B) ≅
            (linearContravariantHomFunctor R B).obj
              (K.opCocomplex.cycles 0) :=
        Iso.refl _
      exact
        (sourceAugmentationExtLinearEquiv
          (R := R) K e B 0).toModuleIso ≪≫
          eExtZero ≪≫
          eCycles ≪≫
          (linearContravariantHomFunctor R B).gHomologyZeroIso
            K.opCocomplex
  | succ m =>
      let stair :=
        sourceExtStaircaseLinearEquiv
          (R := R) K B hexact hacyclic m 0
      rw [Nat.zero_add] at stair
      let stairIso :
          ModuleCat.of R
              (Abelian.Ext.{v}
                (sourceSyzygyShortComplex K 0).X₃ B (m + 1)) ≅
            ModuleCat.of R
              (Abelian.Ext.{v}
                (sourceSyzygyShortComplex K m).X₃ B 1) :=
        stair.toModuleIso
      exact
        (sourceAugmentationExtLinearEquiv
          (R := R) K e B (m + 1)).toModuleIso ≪≫
          stairIso ≪≫
          (linearContravariantHomHomologyIsoSyzygyExtOne
            (R := R) K B m (hexact m) (hacyclic m 0)).symm

end SourceSyzygies

end CategoryTheory
