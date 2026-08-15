/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Topology.Sheaves.Sheaf
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafTerminalCohomology

/-!
# Finite-cover Čech consequences for sheaf cohomology

Mathlib defines the unnormalised Čech cochain complex of a family of
objects, but at this pin it does not yet contain a comparison
quasi-isomorphism with derived sheaf cohomology.  This file records the
strongest comparison consequence available directly from the
Mayer--Vietoris long exact sequence: an acyclic finite cover bounds
cohomological dimension by one less than the number of cover members.
-/

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison

variable {T : TopCat.{u}}

/-- The unnormalised Čech cochain complex of an open family with coefficients
in an abelian sheaf. -/
noncomputable def cechComplex {ι : Type u}
    (U : ι → Opens T)
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (CategoryTheory.cechComplexFunctor U).obj F.obj

/-- Čech cohomology, defined as homology of the unnormalised Čech cochain
complex. -/
noncomputable abbrev cechCohomology {ι : Type u}
    (U : ι → Opens T)
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    AddCommGrpCat.{u} :=
  (cechComplex U F).homology n

/-- The union of a finite subfamily of opens. -/
def finiteUnion {ι : Type u} (U : ι → Opens T)
    (s : Finset ι) : Opens T :=
  ⨆ i ∈ s, U i

/-- The intersection of a finite subfamily of opens.  The empty
intersection is `⊤`. -/
def finiteIntersection {ι : Type u} (U : ι → Opens T)
    (s : Finset ι) : Opens T :=
  ⨅ i ∈ s, U i

@[simp]
lemma finiteUnion_empty {ι : Type u} (U : ι → Opens T) :
    finiteUnion U ∅ = ⊥ := by
  simp [finiteUnion]

@[simp]
lemma finiteUnion_singleton {ι : Type u} (U : ι → Opens T)
    (i : ι) :
    finiteUnion U {i} = U i := by
  unfold finiteUnion
  exact Finset.iSup_singleton i U

@[simp]
lemma finiteUnion_insert {ι : Type u} [DecidableEq ι]
    (U : ι → Opens T)
    (i : ι) (s : Finset ι) :
    finiteUnion U (insert i s) =
      U i ⊔ finiteUnion U s := by
  unfold finiteUnion
  exact Finset.iSup_insert i s U

@[simp]
lemma finiteIntersection_empty {ι : Type u} (U : ι → Opens T) :
    finiteIntersection U ∅ = ⊤ := by
  simp [finiteIntersection]

@[simp]
lemma finiteIntersection_singleton {ι : Type u}
    (U : ι → Opens T) (i : ι) :
    finiteIntersection U {i} = U i := by
  unfold finiteIntersection
  exact Finset.iInf_singleton i U

@[simp]
lemma finiteIntersection_insert {ι : Type u} [DecidableEq ι]
    (U : ι → Opens T)
    (i : ι) (s : Finset ι) :
    finiteIntersection U (insert i s) =
      U i ⊓ finiteIntersection U s := by
  unfold finiteIntersection
  exact Finset.iInf_insert i s U

/-- Intersecting a finite union with a fixed open distributes over the
family. -/
lemma finiteUnion_inf {ι : Type u} (U : ι → Opens T)
    (s : Finset ι) (V : Opens T) :
    finiteUnion U s ⊓ V =
      finiteUnion (fun i => U i ⊓ V) s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [finiteUnion_insert, finiteUnion_insert, inf_sup_right, ih]

/-- On a nonempty finite family, pointwise intersection with a fixed open
may be pulled outside the finite intersection. -/
lemma finiteIntersection_inf {ι : Type u} (U : ι → Opens T)
    (s : Finset ι) (hs : s.Nonempty) (V : Opens T) :
    finiteIntersection (fun i => U i ⊓ V) s =
      finiteIntersection U s ⊓ V := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
      by_cases hs' : s.Nonempty
      · simp only [finiteIntersection_insert, ih hs']
        ac_rfl
      · rw [Finset.not_nonempty_iff_eq_empty.mp hs']
        rw [finiteIntersection_insert, finiteIntersection_empty,
          finiteIntersection_insert, finiteIntersection_empty]
        simp

section MayerVietoris

variable [HasExt.{u}
  (CategoryTheory.Sheaf
    (Opens.grothendieckTopology T) AddCommGrpCat.{u})]

noncomputable local instance sheafCechCohomologyAddCommGroup
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H F n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
If degree `q - 1` vanishes on `U ∩ V` and degree `q` vanishes on `U`
and `V`, then degree `q` vanishes on `U ∪ V`.
-/
lemma subsingleton_H'_sup
    (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (U V : Opens T) (q : ℕ) (hq : 0 < q)
    (hInter :
      Subsingleton
        (CategoryTheory.Sheaf.H'.{u} F (q - 1) (U ⊓ V)))
    (hU :
      Subsingleton
        (CategoryTheory.Sheaf.H'.{u} F q U))
    (hV :
      Subsingleton
        (CategoryTheory.Sheaf.H'.{u} F q V)) :
    Subsingleton
      (CategoryTheory.Sheaf.H'.{u} F q (U ⊔ V)) := by
  letI := hInter
  letI := hU
  letI := hV
  let S := Opens.mayerVietorisSquare U V
  have hsucc : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hexact := S.sequence_exact F (q - 1) q hsucc
  constructor
  intro x y
  suffices ∀ z : CategoryTheory.Sheaf.H'.{u} F q (U ⊔ V), z = 0 by
    rw [this x, this y]
  intro z
  have hz :
      S.toBiprod F q z = 0 := by
    rw [@CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_apply
      _ _ _ _ _ _ S F q z]
    apply
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
    ext
    · exact @Subsingleton.elim _ hU _ _
    · exact @Subsingleton.elim _ hV _ _
  have hshort := hexact.exact 2 (by omega)
  obtain ⟨w, hw⟩ :=
    (ShortComplex.ab_exact_iff _).mp hshort z hz
  rw [← hw, @Subsingleton.elim _ hInter w 0]
  change (S.δ F (q - 1) q hsucc).hom 0 = 0
  exact (S.δ F (q - 1) q hsucc).hom.map_zero

/--
All positive-degree cohomology groups vanish on the nonempty intersections
drawn from `s`.
-/
def IsAcyclicOnIntersections {ι : Type u}
    (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (U : ι → Opens T) (s : Finset ι) : Prop :=
  ∀ (t : Finset ι), t.Nonempty → t ⊆ s →
    ∀ (q : ℕ), 0 < q →
      Subsingleton
        (CategoryTheory.Sheaf.H'.{u} F q
          (finiteIntersection U t))

/--
An acyclic finite cover with `r` members has cohomological dimension at
most `r - 1`.

More precisely, if all nonempty intersections drawn from `s` are
acyclic, then `H^q` of their union vanishes whenever `s.card ≤ q`.
This is the cohomological-dimension consequence of the Čech comparison
that can be proved at this Mathlib pin using the Mayer--Vietoris exact
sequence alone.
-/
theorem subsingleton_H'_finiteUnion_of_acyclicIntersections
    {ι : Type u}
    (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (U : ι → Opens T) (s : Finset ι)
    (hs : s.Nonempty)
    (hacyclic : IsAcyclicOnIntersections F U s)
    (q : ℕ) (hq : s.card ≤ q) :
    Subsingleton
      (CategoryTheory.Sheaf.H'.{u} F q (finiteUnion U s)) := by
  classical
  induction s using Finset.induction_on generalizing U q with
  | empty => simp at hs
  | @insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi] at hq
      have hqpos : 0 < q := by omega
      by_cases hs' : s.Nonempty
      · rw [finiteUnion_insert, sup_comm]
        apply subsingleton_H'_sup F
          (finiteUnion U s) (U i) q hqpos
        · rw [finiteUnion_inf]
          apply ih (fun j => U j ⊓ U i) hs'
          · intro t ht hts r hr
            have hsub :
                insert i t ⊆ insert i s :=
              Finset.insert_subset_insert i hts
            have h :=
              hacyclic (insert i t) (by simp) hsub r hr
            have hintersection :
                finiteIntersection (fun j => U j ⊓ U i) t =
                  finiteIntersection U (insert i t) := by
              calc
                finiteIntersection (fun j => U j ⊓ U i) t =
                    finiteIntersection U t ⊓ U i :=
                  finiteIntersection_inf U t ht (U i)
                _ = U i ⊓ finiteIntersection U t := inf_comm _ _
                _ = finiteIntersection U (insert i t) :=
                  (finiteIntersection_insert U i t).symm
            rw [hintersection]
            exact h
          · omega
        · apply ih U hs'
          · intro t ht hts r hr
            exact hacyclic t ht
              (hts.trans (Finset.subset_insert i s)) r hr
          · omega
        · have h :=
            hacyclic {i} (by simp) (by simp) q hqpos
          simpa using h
      · have hs_empty : s = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        have h :=
          hacyclic {i} (by simp) (by simp) q hqpos
        simpa using h

/--
For a finite nonempty acyclic open cover, cohomology of the top open
vanishes in degrees at least the cardinality of the cover.
-/
theorem subsingleton_H'_top_of_finite_acyclicCover
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (U : ι → Opens T)
    (hcover : finiteUnion U Finset.univ = ⊤)
    (hacyclic :
      IsAcyclicOnIntersections F U Finset.univ)
    (q : ℕ) (hq : Fintype.card ι ≤ q) :
    Subsingleton
      (CategoryTheory.Sheaf.H'.{u} F q (⊤ : Opens T)) := by
  rw [← hcover]
  apply
    subsingleton_H'_finiteUnion_of_acyclicIntersections
      F U Finset.univ Finset.univ_nonempty hacyclic q
  simpa using hq

/--
Global sheaf cohomology has the same finite-cover dimension bound.
-/
theorem subsingleton_H_of_finite_acyclicCover
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (U : ι → Opens T)
    (hcover : finiteUnion U Finset.univ = ⊤)
    (hacyclic :
      IsAcyclicOnIntersections F U Finset.univ)
    (q : ℕ) (hq : Fintype.card ι ≤ q) :
    Subsingleton (CategoryTheory.Sheaf.H.{u} F q) := by
  let htop :=
    subsingleton_H'_top_of_finite_acyclicCover
      F U hcover hacyclic q hq
  let e :=
    CategoryTheory.Sheaf.H'_terminal_addEquiv_H
      F q (isTerminalTop : IsTerminal (⊤ : Opens T))
  constructor
  intro x y
  apply e.symm.injective
  exact @Subsingleton.elim _ htop _ _

end MayerVietoris

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison
