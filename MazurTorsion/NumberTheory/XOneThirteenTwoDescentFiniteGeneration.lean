/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# A finite-generation bridge for a two-descent

This file records a generic consequence of the structure theorem for
finitely generated abelian groups.  If multiplication by two is surjective
on a finitely generated abelian group, its free summand must vanish, so the
group is finite.

The declarations are purely abstract.  In particular, this file does not
assert that a Jacobian is finitely generated, that its mod-two quotient is
trivial, or that any Selmer computation has been completed.
-/

namespace MazurTorsion.XOneThirteenTwoDescentFiniteGeneration

open scoped DirectSum

variable {A : Type*} [AddCommGroup A]

/-- The quotient by the image of multiplication by two is trivial exactly
when multiplication by two is surjective. -/
theorem quotient_by_doubles_subsingleton_iff :
    Subsingleton (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) ↔
      Function.Surjective (fun x : A ↦ 2 • x) := by
  rw [QuotientAddGroup.subsingleton_iff, AddMonoidHom.range_eq_top]
  simp only [Function.Surjective, nsmulAddMonoidHom_apply]

/-- A finitely generated abelian group on which doubling is surjective is
finite. -/
theorem finite_of_surjective_double [AddGroup.FG A]
    (hdouble : Function.Surjective (fun x : A ↦ 2 • x)) : Finite A := by
  obtain ⟨n, ι, hι, p, hp, e, ⟨equiv⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod A
  have hfree : Function.Surjective
      (fun x : Fin n →₀ ℤ ↦ 2 • x) := by
    intro z
    obtain ⟨x, hx⟩ := hdouble (equiv.symm (z, 0))
    refine ⟨(equiv x).1, ?_⟩
    have he := congrArg equiv hx
    simpa using congrArg Prod.fst he
  have hn : n = 0 := by
    by_contra hn
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let z : Fin n →₀ ℤ := Finsupp.single i 1
    obtain ⟨x, hx⟩ := hfree z
    have hxi := DFunLike.congr_fun hx i
    apply Int.not_even_one
    refine ⟨x i, ?_⟩
    simpa only [z, two_nsmul, Finsupp.add_apply,
      Finsupp.single_eq_same] using hxi.symm
  subst n
  letI : ∀ i, NeZero (p i ^ e i) := fun i ↦
    ⟨pow_ne_zero _ (hp i).ne_zero⟩
  letI : ∀ i, Fintype (ZMod (p i ^ e i)) := fun i ↦
    ZMod.fintype (p i ^ e i)
  letI : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact Finite.of_equiv _ equiv.symm.toEquiv

/-- Triviality of the quotient by doubles implies finiteness for a finitely
generated abelian group. -/
theorem finite_of_quotient_by_doubles_subsingleton [AddGroup.FG A]
    (hquot : Subsingleton (A ⧸ (nsmulAddMonoidHom (α := A) 2).range)) :
    Finite A :=
  finite_of_surjective_double
    (quotient_by_doubles_subsingleton_iff.mp hquot)

end MazurTorsion.XOneThirteenTwoDescentFiniteGeneration
