/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOpenCohomology

/-!
# Higher cohomology vanishes on affine schemes

The categorical induction is first stated using the four stability
properties of quasicoherent modules that it consumes.  The affine
tilde-counit theorem supplies those properties in the final corollaries.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Limits Opposite TopCat TopCat.Sheaf

noncomputable local instance affineVanishingCohomologyAddCommGroup
    {Y : TopCat.{u}}
    (G : TopCat.Sheaf AddCommGrpCat.{u} Y) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
The reducible object-property head used by the affine-vanishing induction.
Keeping this implementation detail separate leaves public signatures on
Mathlib's canonical quasicoherence predicate.
-/
abbrev affineVanishingQuasicoherent (X : Scheme.{u}) :
    ObjectProperty X.Modules :=
  Quasicoherent

variable
  (quasicoherentFiniteLimits :
    ∀ (Y : Scheme.{u}) [IsAffine Y]
    (I : Type u) [Finite I],
    (affineVanishingQuasicoherent Y).IsClosedUnderLimitsOfShape (Discrete I))
  (quasicoherentParallelPairColimits :
    ∀ (Y : Scheme.{u}) [IsAffine Y],
    (affineVanishingQuasicoherent Y).IsClosedUnderColimitsOfShape
      WalkingParallelPair)
  (quasicoherentPushforward :
    ∀ {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ Z) (M : Y.Modules) [Quasicoherent M],
    Quasicoherent ((pushforward f).obj M))
  (quasicoherentGlobalSectionsSurjective :
    ∀ {Y : Scheme.{u}} [IsAffine Y]
    {M N : Y.Modules} (f : M ⟶ N)
    [Quasicoherent M] [Quasicoherent N] [Epi f],
    Function.Surjective (f.val.app (op ⊤)).hom)

include quasicoherentFiniteLimits quasicoherentPushforward in
/-- A finite product of pushforward restrictions is quasicoherent,
assuming the two stability properties used in the proof. -/
lemma coverSheaf_isQuasicoherent_of_tools
    {X : Scheme.{u}} [IsAffine X]
    (F : X.Modules) [Quasicoherent F]
    {I : Type u} (U : I → X.Opens)
    [Finite I] [∀ i, IsAffine (U i)] :
    Quasicoherent (∏ᶜ fun i ↦ (restrictFunctor (U i).ι ⋙
      pushforward (U i).ι).obj F) := by
  letI := quasicoherentFiniteLimits X I
  refine (affineVanishingQuasicoherent X).prop_limit
    (Discrete.functor _) (fun i => ?_)
  simp only [Functor.comp_obj, Discrete.functor_obj_eq_as]
  exact quasicoherentPushforward
    (U i.as).ι (F.restrict (U i.as).ι)

include quasicoherentFiniteLimits
  quasicoherentParallelPairColimits
  quasicoherentPushforward
  quasicoherentGlobalSectionsSurjective in
/--
The categorical affine-vanishing induction, parameterized by the four
quasicoherent stability facts it needs.
-/
theorem affineHigherCohomologySubsingleton_of_tools
    {X : Scheme.{u}} (F : X.Modules)
    [IsAffine X] [Quasicoherent F] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F.underlyingSheaf (n + 1)) := by
  revert F X
  refine Nat.case_strong_induction_on
    (p := fun n => ∀ {X : Scheme.{u}} (F : X.Modules)
      [IsAffine X] [Quasicoherent F],
      Subsingleton
        (CategoryTheory.Sheaf.H F.underlyingSheaf (n + 1)))
    n ?_ ?_
  · intro X F _ _
    refine subsingleton_of_forall_eq 0 (fun c => ?_)
    obtain ⟨I, U', hU', vanish⟩ :=
      TopCat.Sheaf.kempf_local_vanishing F.underlyingSheaf 0
        (isBasis_affineOpens X)
        ((diagonal_isAffine_iff_forall_isAffineOpen_inf (𝟙 X)).mp
          (fun _ _ _ _ => inferInstance))
        (by omega) c
    obtain ⟨ι, hU⟩ :=
      CompactSpace.isOpenCover_elim_finite_subcover hU'
    let U : ι → X.Opens := ι.restrict U'
    have : Mono (F.toCoverSheaf U) :=
      F.toCoverSheaf_mono hU
    let S := ShortComplex.mk
      (F.toCoverSheaf U)
      (cokernel.π (F.toCoverSheaf U))
      (cokernel.condition (F.toCoverSheaf U))
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk
        (ShortComplex.exact_cokernel (F.toCoverSheaf U))
    let Ssheaf := S.map (toUnderlyingSheaf X)
    have hSsheaf : Ssheaf.ShortExact :=
      ShortComplex.ShortExact.map_of_exact hS
        (toUnderlyingSheaf X)
    have hsurjective :
        Function.Surjective
          (CategoryTheory.Sheaf.H.map Ssheaf.g 0) := by
      rw [← Equiv.comp_surjective
        (CategoryTheory.Sheaf.H.map Ssheaf.g 0)
        (CategoryTheory.Sheaf.H.equiv₀
          Ssheaf.X₃ Limits.isTerminalTop).toEquiv]
      conv =>
        arg 1
        equals
          (Ssheaf.g.hom.app (op ⊤)) ∘
            (CategoryTheory.Sheaf.H.equiv₀
              Ssheaf.X₂ Limits.isTerminalTop).toEquiv =>
          ext x
          exact
            (CategoryTheory.Sheaf.H.equiv₀_naturality
              Limits.isTerminalTop Ssheaf.g x).symm
      rw [Equiv.surjective_comp
        (CategoryTheory.Sheaf.H.equiv₀
          Ssheaf.X₂ Limits.isTerminalTop).toEquiv
        (Ssheaf.g.hom.app (op ⊤))]
      haveI : ∀ i, IsAffine (U i) :=
        fun i => (vanish i).1
      have hX₂ : Quasicoherent S.X₂ :=
        coverSheaf_isQuasicoherent_of_tools
          quasicoherentFiniteLimits
          quasicoherentPushforward F U
      letI : Quasicoherent S.X₂ := hX₂
      letI := quasicoherentParallelPairColimits X
      have hX₃ : Quasicoherent S.X₃ :=
        (affineVanishingQuasicoherent X).prop_colimit
          (parallelPair _ 0)
          (by rintro ⟨_, _⟩ <;> simpa)
      letI : Quasicoherent S.X₃ := hX₃
      exact quasicoherentGlobalSectionsSurjective S.g
    obtain ⟨x₃, hx₃⟩ :=
      CategoryTheory.Sheaf.H.longSequence_exact₁
        hSsheaf 0 1 rfl c
        (F.toCoverSheaf_H_map_zero U 1 c
          (fun i => (vanish i).2))
    obtain ⟨x₂, hx₂⟩ := hsurjective x₃
    rw [← hx₃, ← hx₂]
    exact CategoryTheory.Sheaf.H.longSequence_comp_zero₃
      hSsheaf 0 1 rfl x₂
  · intro n hi X F _ _
    refine subsingleton_of_forall_eq 0 (fun c => ?_)
    obtain ⟨I, U', hU', vanish⟩ :=
      TopCat.Sheaf.kempf_local_vanishing
        F.underlyingSheaf (n + 1)
        (isBasis_affineOpens X)
        ((diagonal_isAffine_iff_forall_isAffineOpen_inf (𝟙 X)).mp
          (fun _ _ _ _ => inferInstance))
        (by
          intro r U hr₁ hr₂ hU
          haveI : IsAffine U := hU
          have hvanish :=
            hi (r - 1) (by omega)
              (F.restrict (Scheme.Opens.ι U))
          rw [Nat.sub_add_cancel hr₁] at hvanish
          exact hvanish)
        c
    obtain ⟨ι, hU⟩ :=
      CompactSpace.isOpenCover_elim_finite_subcover hU'
    let U : ι → X.Opens := ι.restrict U'
    have : Mono (F.toCoverSheaf U) :=
      F.toCoverSheaf_mono hU
    let S := ShortComplex.mk
      (F.toCoverSheaf U)
      (cokernel.π (F.toCoverSheaf U))
      (cokernel.condition (F.toCoverSheaf U))
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk
        (ShortComplex.exact_cokernel (F.toCoverSheaf U))
    let Ssheaf := S.map (toUnderlyingSheaf X)
    have hSsheaf : Ssheaf.ShortExact :=
      ShortComplex.ShortExact.map_of_exact hS
        (toUnderlyingSheaf X)
    have hinjective :
        Function.Injective
          (CategoryTheory.Sheaf.H.map
            (F.toCoverSheaf U).underlyingSheafHom
            (n + 1 + 1)) := by
      haveI : ∀ i, IsAffine (U i) :=
        fun i => (vanish i).1
      have hX₂ : Quasicoherent S.X₂ :=
        coverSheaf_isQuasicoherent_of_tools
          quasicoherentFiniteLimits
          quasicoherentPushforward F U
      letI : Quasicoherent S.X₂ := hX₂
      letI := quasicoherentParallelPairColimits X
      have hX₃ : Quasicoherent S.X₃ :=
        (affineVanishingQuasicoherent X).prop_colimit
          (parallelPair _ 0)
          (by rintro ⟨_, _⟩ <;> simpa)
      letI : Quasicoherent S.X₃ := hX₃
      refine (injective_iff_map_eq_zero _).mpr
        (fun z hz => ?_)
      obtain ⟨x₃, hx₃⟩ :=
        CategoryTheory.Sheaf.H.longSequence_exact₁
          hSsheaf (n + 1) (n + 1 + 1) rfl z hz
      have hzero :
          Subsingleton
            (CategoryTheory.Sheaf.H Ssheaf.X₃ (n + 1)) :=
        hi n (le_refl n) S.X₃
      rw [← hx₃, Subsingleton.elim x₃ 0, map_zero]
      rfl
    apply hinjective
    rw [map_zero]
    exact F.toCoverSheaf_H_map_zero U (n + 1 + 1) c
      (fun i => (vanish i).2)

section TildeCounit

variable [∀ R : CommRingCat.{u},
  HasQuasicoherentTildeCounit R]

/-- Every positive-degree cohomology group of a quasicoherent module
on an affine scheme is trivial. -/
theorem subsingleton_H_of_isAffine
    {X : Scheme.{u}} (F : X.Modules)
    [IsAffine X] [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H F.underlyingSheaf (n + 1)) := by
  refine affineHigherCohomologySubsingleton_of_tools
    ?_ ?_ ?_ ?_ F n
  · intro Y _ I _
    change (isQuasicoherentCohomology Y).IsClosedUnderLimitsOfShape (Discrete I)
    infer_instance
  · intro Y _
    change (isQuasicoherentCohomology Y).IsClosedUnderColimitsOfShape WalkingParallelPair
    infer_instance
  · intro Y Z _ _ f M _
    infer_instance
  · intro Y _ M N f _ _ _
    exact isQuasicoherent_surjective_of_epi_coherentCohomology f

/-- Typeclass form of affine vanishing. -/
instance affineHigherCohomologySubsingleton
    {X : Scheme.{u}} (F : X.Modules)
    [IsAffine X] [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H F.underlyingSheaf (n + 1)) :=
  subsingleton_H_of_isAffine F n

/--
Objectwise positive cohomology over an affine open vanishes.  This is
the form consumed by Mathlib's Mayer--Vietoris sequence.
-/
theorem subsingleton_H'_of_isAffineOpen
    {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens)
    [IsAffine U] (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H' F.underlyingSheaf (n + 1) U) := by
  apply
    TopCat.Sheaf.OpenCohomology.subsingleton_H'_of_subsingleton_restrict_H
      F.underlyingSheaf U n
  change Subsingleton
    (CategoryTheory.Sheaf.H
      (F.restrict (Scheme.Opens.ι U)).underlyingSheaf
      (n + 1))
  exact subsingleton_H_of_isAffine
    (F.restrict (Scheme.Opens.ι U)) n

end TildeCounit

end AlgebraicGeometry.Scheme.Modules
