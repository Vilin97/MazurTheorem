/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Reflection of invertibility through affine tilde

This file proves the algebraic localization criterion needed to reflect rank-one local
freeness through the affine tilde equivalence.  The key missing upstream ingredient is supplied
without a freeness hypothesis: duals of finite projective modules commute with base change.

The final geometric step refines a Tau Ceti local-trivialization atlas on `Spec R` to principal
opens and applies this criterion.
-/

open CategoryTheory
open TopologicalSpace
open scoped TensorProduct

namespace MazurTorsion.AlgebraicGeometry

universe u

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace AffineTilde

section DualBaseChange

variable {R A V W : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]

/-- The canonical base-change map from the base change of a dual to the dual of the base
change.  Unlike the currently pinned `IsBaseChange.toDualBaseChange`, this definition is not
restricted to globally free modules. -/
noncomputable def dualBaseChangeHom {j : V →ₗ[R] W} (hj : IsBaseChange A j) :
    A ⊗[R] Module.Dual R V →ₗ[A] Module.Dual A W where
  toAddHom := (TensorProduct.lift
    { toFun := fun a ↦ a • hj.toDual
      map_add' := fun a b ↦ by simp [add_smul]
      map_smul' := fun r a ↦ by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_tmul', mul_smul]

@[simp]
lemma dualBaseChangeHom_tmul_apply {j : V →ₗ[R] W} (hj : IsBaseChange A j)
    (a : A) (f : Module.Dual R V) (v : V) :
    dualBaseChangeHom hj (a ⊗ₜ[R] f) (j v) = a * algebraMap R A (f v) := by
  simp [dualBaseChangeHom, IsBaseChange.toDual_comp_apply]

/-- Taking duals commutes with arbitrary base change for finite projective modules.  The pinned
upstream theorem has a global-freeness hypothesis; the proof here uses a finite split free
presentation, hence applies to the projective modules arising from Zariski-local freeness. -/
theorem dualBaseChangeHom_bijective_of_finite_projective
    [Module.Finite R V] [Module.Projective R V]
    {j : V →ₗ[R] W} (hj : IsBaseChange A j) :
    Function.Bijective (dualBaseChangeHom hj) := by
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R V
  let v : Fin n → V := fun k ↦ p (Pi.single k 1)
  let φ : Fin n → Module.Dual R V := fun k ↦
    (LinearMap.proj k).comp i
  have hframe (x : V) : ∑ k, φ k x • v k = x := by
    calc
      ∑ k, φ k x • v k = p (∑ k, (i x k) • Pi.single k (1 : R)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        simp only [v, φ, LinearMap.comp_apply, LinearMap.proj_apply, map_smul]
      _ = p (i x) := by rw [← pi_eq_sum_univ' (i x)]
      _ = x := LinearMap.congr_fun hpi x
  have hdual (f : Module.Dual R V) : ∑ k, f (v k) • φ k = f := by
    apply LinearMap.ext
    intro x
    calc
      (∑ k, f (v k) • φ k) x = ∑ k, f (v k) * φ k x := by simp
      _ = f (∑ k, φ k x • v k) := by
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro k _hk
        exact mul_comm _ _
      _ = f x := by rw [hframe]
  let inv : Module.Dual A W →ₗ[A] A ⊗[R] Module.Dual R V :=
    { toFun := fun h ↦ ∑ k, h (j (v k)) ⊗ₜ[R] φ k
      map_add' := by
        intro f g
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _hk
        rw [LinearMap.add_apply, TensorProduct.add_tmul]
      map_smul' := by
        intro a f
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        simp only [LinearMap.smul_apply, RingHom.id_apply, TensorProduct.smul_tmul'] }
  have hleft : Function.LeftInverse inv (dualBaseChangeHom hj) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [inv]
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul a f =>
        calc
          inv (dualBaseChangeHom hj (a ⊗ₜ[R] f)) =
              ∑ k, (a * algebraMap R A (f (v k))) ⊗ₜ[R] φ k := by
                change (∑ k, dualBaseChangeHom hj (a ⊗ₜ[R] f) (j (v k)) ⊗ₜ[R] φ k) = _
                apply Finset.sum_congr rfl
                intro k _hk
                rw [dualBaseChangeHom_tmul_apply]
          _ = ∑ k, a ⊗ₜ[R] (f (v k) • φ k) := by
                apply Finset.sum_congr rfl
                intro k _hk
                rw [TensorProduct.tmul_smul]
                congr 1
                rw [Algebra.smul_def, mul_comm]
          _ = a ⊗ₜ[R] (∑ k, f (v k) • φ k) := by rw [TensorProduct.tmul_sum]
          _ = a ⊗ₜ[R] f := by rw [hdual]
  have hright : Function.RightInverse inv (dualBaseChangeHom hj) := by
    intro h
    apply hj.algHom_ext
    intro x
    calc
      dualBaseChangeHom hj (inv h) (j x) =
          ∑ k, h (j (v k)) * algebraMap R A (φ k x) := by
            change dualBaseChangeHom hj
              (∑ k, h (j (v k)) ⊗ₜ[R] φ k) (j x) = _
            rw [map_sum, LinearMap.sum_apply]
            apply Finset.sum_congr rfl
            intro k _hk
            rw [dualBaseChangeHom_tmul_apply]
      _ = ∑ k, algebraMap R A (φ k x) • h (j (v k)) := by
            apply Finset.sum_congr rfl
            intro k _hk
            simp only [smul_eq_mul, mul_comm]
      _ = h (∑ k, algebraMap R A (φ k x) • j (v k)) := by
            rw [map_sum]
            simp only [map_smul]
      _ = h (∑ k, j (φ k x • v k)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k _hk
            rw [map_smul, IsScalarTower.algebraMap_smul]
      _ = h (j (∑ k, φ k x • v k)) := by simp only [map_sum]
      _ = h (j x) := by rw [hframe]
  exact ⟨hleft.injective, hright.surjective⟩

/-- The explicit equivalence induced by the finite-projective dual base-change theorem. -/
noncomputable def dualBaseChangeEquivOfFiniteProjective
    [Module.Finite R V] [Module.Projective R V]
    {j : V →ₗ[R] W} (hj : IsBaseChange A j) :
    A ⊗[R] Module.Dual R V ≃ₗ[A] Module.Dual A W :=
  LinearEquiv.ofBijective (dualBaseChangeHom hj)
    (dualBaseChangeHom_bijective_of_finite_projective hj)

@[simp]
lemma dualBaseChangeEquivOfFiniteProjective_apply
    [Module.Finite R V] [Module.Projective R V]
    {j : V →ₗ[R] W} (hj : IsBaseChange A j)
    (x : A ⊗[R] Module.Dual R V) :
    dualBaseChangeEquivOfFiniteProjective hj x = dualBaseChangeHom hj x := rfl

/-- The canonical dual map is itself a base change for finite projective modules. -/
theorem dual_isBaseChange_of_finite_projective
    [Module.Finite R V] [Module.Projective R V]
    {j : V →ₗ[R] W} (hj : IsBaseChange A j) :
    IsBaseChange A hj.toDual := by
  apply IsBaseChange.of_equiv (dualBaseChangeEquivOfFiniteProjective hj)
  intro f
  rw [dualBaseChangeEquivOfFiniteProjective_apply]
  apply hj.algHom_ext
  intro v
  rw [dualBaseChangeHom_tmul_apply, one_mul, IsBaseChange.toDual_comp_apply]

/-- After a finite-projective base change, evaluation of a dual vector against a vector is the
base change of the original evaluation pairing.  This is the local equivalence used below to
descend invertibility. -/
noncomputable def baseChangedContractLeftEquiv
    [Module.Finite R V] [Module.Projective R V] [Module.Invertible A W]
    {j : V →ₗ[R] W} (hj : IsBaseChange A j) :
    A ⊗[R] (Module.Dual R V ⊗[R] V) ≃ₗ[A] A :=
  TensorProduct.AlgebraTensorModule.distribBaseChange R A (Module.Dual R V) V ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr
      (dualBaseChangeEquivOfFiniteProjective hj) hj.equiv ≪≫ₗ
    Module.Invertible.linearEquiv A W

@[simp]
lemma baseChangedContractLeftEquiv_tmul
    [Module.Finite R V] [Module.Projective R V] [Module.Invertible A W]
    {j : V →ₗ[R] W} (hj : IsBaseChange A j)
    (a : A) (f : Module.Dual R V) (v : V) :
    baseChangedContractLeftEquiv hj (a ⊗ₜ[R] (f ⊗ₜ[R] v)) =
      a * algebraMap R A (f v) := by
  simp [baseChangedContractLeftEquiv, Module.Invertible.linearEquiv,
    dualBaseChangeEquivOfFiniteProjective_apply]

end DualBaseChange

section LocalInvertibility

variable {R M : Type u}
variable [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Freeness over an arbitrary model of an away localization transfers to Mathlib's canonical
localized module.  Keeping this comparison explicit lets geometric section rings be used directly
in the descent criterion. -/
theorem free_localizedModule_away_of_isLocalization
    {r : R} {A W : Type u} [CommRing A] [Algebra R A] [IsLocalization.Away r A]
    [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
    (j : M →ₗ[R] W) [IsLocalizedModule.Away r j] [Module.Free A W] :
    Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  let σ := (IsLocalization.algEquiv (Submonoid.powers r)
    (Localization.Away r) A).toRingEquiv
  have hfree : Module.Free (Localization.Away r) (LocalizedModule.Away r M) ↔
      Module.Free A W := by
    apply Module.Free.iff_of_equiv (σ := σ)
    refine { __ := IsLocalizedModule.iso (Submonoid.powers r) j, map_smul' := ?_ }
    intro a x
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (S := Localization.Away r) (Submonoid.powers r) a
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units j s)).1
    simp [σ, ← map_smul, ← smul_assoc]
  exact hfree.mpr inferInstance

/-- A module is invertible if it is locally isomorphic to the base ring on principal opens whose
defining elements generate the unit ideal.  The local models may be arbitrary localization rings,
which is the form supplied by sections of the structure sheaf on a basic open. -/
theorem invertible_of_away_local_equiv
    (s : Set R) (hs : Ideal.span s = ⊤)
    (A : s → Type u) [∀ r, CommRing (A r)] [∀ r, Algebra R (A r)]
    [∀ r, IsLocalization.Away r.1 (A r)]
    (W : s → Type u) [∀ r, AddCommGroup (W r)] [∀ r, Module R (W r)]
    [∀ r, Module (A r) (W r)] [∀ r, IsScalarTower R (A r) (W r)]
    (j : ∀ r, M →ₗ[R] W r) [∀ r, IsLocalizedModule.Away r.1 (j r)]
    (e : ∀ r, W r ≃ₗ[A r] A r) :
    Module.Invertible R M := by
  have hlocalFP (r : s) : Module.FinitePresentation (A r) (W r) := by
    exact Module.FinitePresentation.of_equiv (e r).symm
  letI : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs j hlocalFP
  have hcanonicalFree (r : s) :
      Module.Free (Localization.Away r.1) (LocalizedModule.Away r.1 M) := by
    letI : Module.Free (A r) (W r) := Module.Free.of_equiv (e r).symm
    exact free_localizedModule_away_of_isLocalization
      (r := r.1) (A := A r) (W := W r) (j r)
  have hfreeLocus : Module.freeLocus R M = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro p
    have hnsub : ¬ s ⊆ p.asIdeal := by
      intro hsub
      apply p.isPrime.ne_top
      apply top_unique
      rw [← hs]
      exact Ideal.span_le.mpr hsub
    obtain ⟨r, hrs, hrp⟩ := Set.not_subset.mp hnsub
    let r' : s := ⟨r, hrs⟩
    have hproj : Module.Projective (Localization.Away r)
        (LocalizedModule.Away r M) := by
      letI := hcanonicalFree r'
      infer_instance
    exact (Module.basicOpen_subset_freeLocus_iff.mpr hproj) hrp
  letI : Module.Projective R M :=
    Module.freeLocus_eq_univ_iff.mp hfreeLocus
  refine ⟨bijective_of_isLocalized_span s hs
    (fun r ↦ A r ⊗[R] (Module.Dual R M ⊗[R] M))
    (fun r ↦ TensorProduct.mk R (A r) (Module.Dual R M ⊗[R] M) 1)
    A (fun r ↦ Algebra.linearMap R (A r)) (contractLeft R M) ?_⟩
  intro r
  letI : Module.Invertible (A r) (W r) :=
    Module.Invertible.congr (e r).symm
  have hj : IsBaseChange (A r) (j r) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers r.1) (A r) (j r)
  let E : A r ⊗[R] (Module.Dual R M ⊗[R] M) ≃ₗ[A r] A r :=
    baseChangedContractLeftEquiv hj
  have hE (x : Module.Dual R M ⊗[R] M) :
      E (1 ⊗ₜ[R] x) = algebraMap R (A r) (contractLeft R M x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
        exact (map_add (algebraMap R (A r)) _ _).symm
    | tmul f m => simp [E]
  have hmap : IsLocalizedModule.map (Submonoid.powers r.1)
      (TensorProduct.mk R (A r) (Module.Dual R M ⊗[R] M) 1)
      (Algebra.linearMap R (A r)) (contractLeft R M) =
      E.toLinearMap.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.1)
      (TensorProduct.mk R (A r) (Module.Dual R M ⊗[R] M) 1)
      (Algebra.linearMap R (A r))
    apply LinearMap.ext
    intro x
    change IsLocalizedModule.map (Submonoid.powers r.1)
      (TensorProduct.mk R (A r) (Module.Dual R M ⊗[R] M) 1)
      (Algebra.linearMap R (A r)) (contractLeft R M)
        ((TensorProduct.mk R (A r) (Module.Dual R M ⊗[R] M) 1) x) =
      E ((TensorProduct.mk R (A r) (Module.Dual R M ⊗[R] M) 1) x)
    rw [IsLocalizedModule.map_apply]
    exact (hE x).symm
  rw [hmap]
  exact E.bijective

end LocalInvertibility

section GeometricReflection

private noncomputable def freePUnitIsoForReflection
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    _root_.SheafOfModules.free (R := S) PUnit.{u + 1} ≅
      _root_.SheafOfModules.unit S :=
  Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit S)

variable (R : Type u) [CommRing R]
variable (M : ModuleCat.{u} R)

/-- Evaluating a local rank-one trivialization of `tilde M` on a smaller principal open gives
the section-module equivalence required by `invertible_of_away_local_equiv`. -/
private noncomputable def tildeSectionsEquivOfAtlas
    (t : TauCeti.SheafOfModules.LocalTrivializations.{u, u, u}
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) M))
    (f : R) (i : t.I) (h : PrimeSpectrum.basicOpen f ≤ t.X i) :
    (structureSheafInType R M).obj.obj (.op (PrimeSpectrum.basicOpen f)) ≃ₗ[
      (structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f))]
      (structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f)) := by
  let Y : Over (t.X i) := Over.mk (homOfLE h)
  let E := freePUnitIsoForReflection.symm ≪≫ t.iso i
  exact ((SheafOfModules.evaluation
    ((_root_.AlgebraicGeometry.Spec (CommRingCat.of R)).ringCatSheaf.over (t.X i))
    (.op Y)).mapIso E).symm.toLinearEquiv

/-- Affine tilde reflects invertibility.  The proof refines a rank-one local atlas to the
principal-open basis, then descends the resulting sectionwise rank-one equivalences through
`invertible_of_away_local_equiv`. -/
theorem tildeReflectsInvertibility : TildeReflectsInvertibility R := by
  intro M hM
  letI : SheafOfModules.isInvertible
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) M) := hM
  let t : TauCeti.SheafOfModules.LocalTrivializations.{u, u, u}
      (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R) M) :=
    TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible.{u, u, u} _
  let s : Set R := { f | ∃ i, PrimeSpectrum.basicOpen f ≤ t.X i }
  have hs : Ideal.span s = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro p _hp
    have htcover : TopologicalSpace.IsOpenCover t.X :=
      (Opens.coversTop_iff
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) t.X).mp t.coversTop
    obtain ⟨i, hpi⟩ := htcover.exists_mem p
    obtain ⟨_, ⟨f, rfl⟩, hpf, hfX⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        hpi (t.X i).isOpen
    have hle : PrimeSpectrum.basicOpen f ≤ t.X i := hfX
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨f, ⟨⟨i, hle⟩, hpf⟩⟩
  exact invertible_of_away_local_equiv (M := M) s hs
    (fun r ↦ (structureSheafInType R R).obj.obj
      (.op (PrimeSpectrum.basicOpen r.1)))
    (fun r ↦ (structureSheafInType R M).obj.obj
      (.op (PrimeSpectrum.basicOpen r.1)))
    (fun r ↦ StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen r.1))
    (fun r ↦ tildeSectionsEquivOfAtlas R M t r.1
      r.property.choose r.property.choose_spec)

/-- The checked downstream tensor-inverse consumer of affine tilde reflection. -/
theorem tensorInverseComparison :
    TensorInverseComparison
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  tensorInverseComparison_of_tildeReflectsInvertibility R
    (tildeReflectsInvertibility R)

end GeometricReflection

end AffineTilde

end MazurTorsion.AlgebraicGeometry
