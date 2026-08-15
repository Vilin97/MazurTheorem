/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Open covers and covers of the terminal object

Mathlib uses both the lattice-theoretic notion that a family of open
subsets has supremum `⊤` and the site-theoretic predicate
`GrothendieckTopology.CoversTop`.  This file records the conversion from
the former to the latter for the ordinary opens site.
-/

open CategoryTheory TopologicalSpace

universe u v

namespace TopologicalSpace.Opens

/--
A family of open subsets whose supremum is the whole space covers the
terminal object of the ordinary opens site.
-/
theorem coversTop_of_iSup_eq_top
    {T : Type u} [TopologicalSpace T] {ι : Type v}
    (U : ι → Opens T) (hU : ⨆ i, U i = ⊤) :
    (Opens.grothendieckTopology T).CoversTop U := by
  intro W x hx
  have hxTop : x ∈ (⊤ : Opens T) := trivial
  rw [← hU, Opens.mem_iSup] at hxTop
  obtain ⟨i, hxi⟩ := hxTop
  refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, hx, hxi⟩
  rw [Sieve.mem_ofObjects_iff]
  exact ⟨i, ⟨homOfLE inf_le_right⟩⟩

/--
For the ordinary opens site, covering the terminal object is equivalent
to having supremum `⊤`.
-/
theorem coversTop_iff_iSup_eq_top
    {T : Type u} [TopologicalSpace T] {ι : Type v}
    (U : ι → Opens T) :
    (Opens.grothendieckTopology T).CoversTop U ↔
      ⨆ i, U i = ⊤ := by
  constructor
  · intro hU
    rw [eq_top_iff]
    intro x _
    rw [Opens.mem_iSup]
    obtain ⟨V, f, hf, hx⟩ :=
      hU ⊤ x (Opens.mem_top x)
    obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
    exact ⟨i, (leOfHom g) hx⟩
  · exact coversTop_of_iSup_eq_top U

end TopologicalSpace.Opens
