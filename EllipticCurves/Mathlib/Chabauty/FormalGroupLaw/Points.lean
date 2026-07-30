/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/Series/FormalGroupLaw/Points.lean`).

module

public import EllipticCurves.Mathlib.Chabauty.FormalGroupLaw.Basic

@[expose] public section


/-!
# Points of a formal group law in the maximal ideal

In the standing setting of the `p`-adic kit and for finite `ι`, the tuples
`ChabautyColeman.FormalGroupLaw.Points` with entries in the maximal ideal form a commutative
monoid under evaluation of `F` (addition is total on `𝔪`-tuples since the values of series with
vanishing constant term stay in `𝔪`); each monoid axiom is the corresponding formal axiom of
`F`, evaluated via `ChabautyColeman.MvPSeries.eval_subst`. Inverses are not constructed here.

## Main definitions
* `ChabautyColeman.FormalGroupLaw.Points`: the `𝔪`-tuples, with their `AddCommMonoid` structure.

Blueprint node: `def:fgl`.
-/


open MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace ChabautyColeman

namespace FormalGroupLaw

variable {O : Type*} [CommRing O] {ι : Type*} (Φ : FormalGroupLaw O ι)
variable [IsLocalRing O]

/-- The `𝔪`-points of a formal group law: tuples with entries in the maximal ideal.
The group law is evaluation of `F`. -/
def Points (_Φ : FormalGroupLaw O ι) := ι → maximalIdeal O

instance : Zero Φ.Points := ⟨fun _ ↦ 0⟩

@[simp]
lemma zero_apply_coe (i : ι) : ((0 : Φ.Points) i : O) = 0 := rfl

/-- The evaluation-point family attached to a pair of points: the first block of
variables gets `z`, the second `w`. -/
def pairFam (z w : Φ.Points) : ι ⊕ ι → O :=
  Sum.elim (fun j ↦ (z j : O)) fun j ↦ (w j : O)

lemma pairFam_mem (z w : Φ.Points) (s : ι ⊕ ι) :
    pairFam Φ z w s ∈ maximalIdeal O := by
  rcases s with j | j
  · exact (z j).2
  · exact (w j).2

section points

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [Finite ι]

lemma hasEval_coe (z : Φ.Points) :
    MvPowerSeries.HasEval fun j : ι ↦ (z j : O) :=
  MvPSeries.hasEval_of_mem fun j ↦ (z j).2

lemma hasEval_pairFam (z w : Φ.Points) :
    MvPowerSeries.HasEval (pairFam Φ z w) :=
  MvPSeries.hasEval_of_mem (pairFam_mem Φ z w)

variable [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

noncomputable instance : Add Φ.Points :=
  ⟨fun z w i ↦ ⟨MvPSeries.eval (pairFam Φ z w) (Φ.F i),
    MvPSeries.eval_mem_maximalIdeal (hasEval_pairFam Φ z w) (pairFam_mem Φ z w) (Φ.F i)
      (by rw [Φ.zero_constantCoeff i]; exact zero_mem _)⟩⟩

@[simp]
lemma add_apply_coe (z w : Φ.Points) (i : ι) :
    ((z + w) i : O) = MvPSeries.eval (pairFam Φ z w) (Φ.F i) := rfl

noncomputable instance : AddCommMonoid Φ.Points where
  add := (· + ·)
  zero := 0
  nsmul := nsmulRec
  add_zero z := by
    funext i
    refine Subtype.ext ?_
    have hax := congrArg (MvPSeries.eval fun j : ι ↦ (z j : O)) (Φ.add_zero' i)
    rw [MvPSeries.eval_subst (hasEval_coe Φ z) hasSubst_unitR, MvPSeries.eval_X] at hax
    have hfam : (fun s : ι ⊕ ι ↦ MvPSeries.eval (fun j : ι ↦ (z j : O))
          ((Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O) s))
        = pairFam Φ z 0 := by
      funext s
      rcases s with j | j <;> simp [pairFam]
    rw [hfam] at hax
    rw [add_apply_coe]
    exact hax
  zero_add z := by
    funext i
    refine Subtype.ext ?_
    have hax := congrArg (MvPSeries.eval fun j : ι ↦ (z j : O)) (Φ.zero_add' i)
    rw [MvPSeries.eval_subst (hasEval_coe Φ z) hasSubst_unitL, MvPSeries.eval_X] at hax
    have hfam : (fun s : ι ⊕ ι ↦ MvPSeries.eval (fun j : ι ↦ (z j : O))
          ((Sum.elim (fun _ ↦ 0) MvPowerSeries.X : ι ⊕ ι → MvPowerSeries ι O) s))
        = pairFam Φ 0 z := by
      funext s
      rcases s with j | j <;> simp [pairFam]
    rw [hfam] at hax
    rw [add_apply_coe]
    exact hax
  add_comm z w := by
    funext i
    refine Subtype.ext ?_
    have hax := congrArg (MvPSeries.eval (pairFam Φ z w)) (Φ.comm' i)
    rw [MvPSeries.eval_subst (hasEval_pairFam Φ z w) hasSubst_swap] at hax
    have hfam : (fun s : ι ⊕ ι ↦ MvPSeries.eval (pairFam Φ z w)
          (MvPowerSeries.X s.swap : MvPowerSeries (ι ⊕ ι) O))
        = pairFam Φ w z := by
      funext s
      rcases s with j | j <;> simp [pairFam]
    rw [hfam] at hax
    rw [add_apply_coe, add_apply_coe]
    exact hax.symm
  add_assoc z w u := by
    funext i
    refine Subtype.ext ?_
    set p3 : ι ⊕ ι ⊕ ι → O :=
      Sum.elim (fun j ↦ (z j : O)) (Sum.elim (fun j ↦ (w j : O)) fun j ↦ (u j : O))
      with hp3def
    have hp3mem (s : ι ⊕ ι ⊕ ι) : p3 s ∈ maximalIdeal O := by
      rcases s with j | j | j
      · exact (z j).2
      · exact (w j).2
      · exact (u j).2
    have hp3 : MvPowerSeries.HasEval p3 := MvPSeries.hasEval_of_mem hp3mem
    have hax := congrArg (MvPSeries.eval p3) (Φ.assoc' i)
    rw [MvPSeries.eval_subst hp3 (hasSubst_assocLeft Φ),
      MvPSeries.eval_subst hp3 (hasSubst_assocRight Φ)] at hax
    have hleft : (fun s : ι ⊕ ι ↦ MvPSeries.eval p3 (assocLeftFam Φ.F s))
        = pairFam Φ (z + w) u := by
      funext s
      rcases s with j | j
      · have h1 : MvPSeries.eval p3 (assocLeftFam Φ.F (Sum.inl j))
            = MvPSeries.eval (fun s' ↦ MvPSeries.eval p3
              ((Sum.elim (fun a : ι ↦ X (Sum.inl a))
                (fun b : ι ↦ X (Sum.inr (Sum.inl b)))
                : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) s')) (Φ.F j) :=
          MvPSeries.eval_subst hp3 hasSubst_emb12 (Φ.F j)
        have h2 : (fun s' : ι ⊕ ι ↦ MvPSeries.eval p3
              ((Sum.elim (fun a : ι ↦ X (Sum.inl a))
                (fun b : ι ↦ X (Sum.inr (Sum.inl b)))
                : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) s'))
            = pairFam Φ z w := by
          funext s'
          rcases s' with a | b <;> simp [pairFam, hp3def]
        rw [h2] at h1
        have h3 : pairFam Φ (z + w) u (Sum.inl j) = ((z + w) j : O) := rfl
        rw [h1, h3, add_apply_coe]
      · simp [assocLeftFam, pairFam, hp3def]
    have hright : (fun s : ι ⊕ ι ↦ MvPSeries.eval p3 (assocRightFam Φ.F s))
        = pairFam Φ z (w + u) := by
      funext s
      rcases s with j | j
      · simp [assocRightFam, pairFam, hp3def]
      · have h1 : MvPSeries.eval p3 (assocRightFam Φ.F (Sum.inr j))
            = MvPSeries.eval (fun s' ↦ MvPSeries.eval p3
              ((Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a)))
                (fun b : ι ↦ X (Sum.inr (Sum.inr b)))
                : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) s')) (Φ.F j) :=
          MvPSeries.eval_subst hp3 hasSubst_emb23 (Φ.F j)
        have h2 : (fun s' : ι ⊕ ι ↦ MvPSeries.eval p3
              ((Sum.elim (fun a : ι ↦ X (Sum.inr (Sum.inl a)))
                (fun b : ι ↦ X (Sum.inr (Sum.inr b)))
                : ι ⊕ ι → MvPowerSeries (ι ⊕ ι ⊕ ι) O) s'))
            = pairFam Φ w u := by
          funext s'
          rcases s' with a | b <;> simp [pairFam, hp3def]
        rw [h2] at h1
        have h3 : pairFam Φ z (w + u) (Sum.inr j) = ((w + u) j : O) := rfl
        rw [h1, h3, add_apply_coe]
    rw [hleft, hright] at hax
    rw [add_apply_coe, add_apply_coe]
    exact hax

end points

end FormalGroupLaw

end ChabautyColeman

end
