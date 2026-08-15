/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib

/-!
# Finite distinguished-open covers for affine quasicoherent sheaves

Quasicoherence in Mathlib is presented by arbitrary local presentations.
On an affine scheme, quasi-compactness refines that cover to finitely many
distinguished opens.  This file packages that topological reduction without
using any cohomology or localization-of-sections theorem.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/--
An open cover of `Spec R` admits a finite distinguished-open refinement
whose defining elements generate the unit ideal.
-/
theorem exists_finite_basicOpen_refinement
    {ι : Type*} (U : ι → (Spec R).Opens)
    (hU : ⨆ i, U i = ⊤) :
    ∃ (n : ℕ) (f : Fin n → R) (φ : Fin n → ι),
      (∀ j, PrimeSpectrum.basicOpen (f j) ≤ U (φ j)) ∧
        Ideal.span (Set.range f) = ⊤ := by
  classical
  have hpoint : ∀ x : PrimeSpectrum R, ∃ (g : R) (i : ι),
      x ∈ PrimeSpectrum.basicOpen g ∧
        PrimeSpectrum.basicOpen g ≤ U i := by
    intro x
    have hx : x ∈ (⊤ : (Spec R).Opens) := trivial
    rw [← hU] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨V, hV, hxV, hVU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (PrimeSpectrum.isBasis_basic_opens (R := R))) hi
    obtain ⟨g, rfl⟩ := hV
    exact ⟨g, i, hxV, hVU⟩
  choose g φ hxg hgU using hpoint
  have hcover : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ x, (PrimeSpectrum.basicOpen (g x) :
        Set (PrimeSpectrum R)) :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hxg x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (PrimeSpectrum.basicOpen (g x) :
      Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (g x)).isOpen) hcover
  let e := t.equivFin
  refine ⟨t.card, fun j => g (e.symm j).val,
    fun j => φ (e.symm j).val, fun j => hgU _, ?_⟩
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  have hx := ht (Set.mem_univ x)
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨e ⟨y, hy⟩, ?_⟩
  rw [Equiv.symm_apply_apply]
  exact hxy

/--
A categorical cover of the terminal open has supremum `⊤`.
-/
theorem iSup_eq_top_of_coversTop
    {T : Type*} [TopologicalSpace T] {ι : Type*}
    (U : ι → TopologicalSpace.Opens T)
    (hU : (Opens.grothendieckTopology T).CoversTop U) :
    ⨆ i, U i = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨V, f, hf, hx⟩ :=
    hU ⊤ x (TopologicalSpace.Opens.mem_top x)
  obtain ⟨i, ⟨g⟩⟩ := hf
  exact ⟨i, (leOfHom g) hx⟩

/--
The local presentation cover supplied by quasicoherence on `Spec R`
admits a finite distinguished-open refinement.
-/
theorem finite_basicOpen_presentation_cover
    (F : (Spec R).Modules) [hF : F.IsQuasicoherent] :
    ∃ (q : SheafOfModules.QuasicoherentData.{u, u, u, u} F)
      (n : ℕ) (g : Fin n → R) (φ : Fin n → q.I),
      (∀ j, PrimeSpectrum.basicOpen (g j) ≤ q.X (φ j)) ∧
        Ideal.span (Set.range g) = ⊤ := by
  obtain ⟨q⟩ := hF.nonempty_quasicoherentData
  have htop : ⨆ i, q.X i = ⊤ :=
    iSup_eq_top_of_coversTop q.X q.coversTop
  obtain ⟨n, g, φ, hg, hspan⟩ :=
    exists_finite_basicOpen_refinement q.X htop
  exact ⟨q, n, g, φ, hg, hspan⟩

end AlgebraicGeometry.Scheme.Modules
