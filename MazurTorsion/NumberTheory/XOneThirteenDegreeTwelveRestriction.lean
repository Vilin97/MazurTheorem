/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Data.ZMod.Basic

/-!
# Degree-twelve restriction with coefficients of characteristic nineteen

This file isolates the group-cohomological injectivity used in a
Mazur--Tate base-change argument.  Let `S` be a normal subgroup of `G` whose
finite quotient has cardinality `12`.  For a trivial representation on a
`ZMod 19`-module, restriction

`H^1(G, M) -> H^1(S, M)`

is injective.  Mathlib's inflation--restriction sequence reduces this to the
vanishing of `H^1(G / S, M)`.  For trivial coefficients this group is the
group of additive homomorphisms from `Additive (G / S)` to `M`; every such
homomorphism is killed by both `12` and `19`, hence is zero.

All group-theoretic and coefficient hypotheses are explicit.  In particular,
nothing here constructs a Galois group or asserts that a field extension has
degree `12`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Representation

namespace MazurTorsion.XOneThirteenDegreeTwelveRestriction

universe u

/-- A homomorphism from a group of cardinality `12` to an additive
`ZMod 19`-module is zero. -/
theorem addMonoidHom_eq_zero_of_card_eq_twelve
    {Q M : Type u} [Group Q] [Finite Q]
    [AddCommGroup M] [Module (ZMod 19) M]
    (hcard : Nat.card Q = 12)
    (f : Additive Q →+ M) :
    f = 0 := by
  apply AddMonoidHom.ext
  intro q
  have hdomain : 12 • q = 0 := by
    change q.toMul ^ 12 = 1
    rw [← hcard]
    exact pow_card_eq_one'
  have htwelve : 12 • f q = 0 := by
    rw [← map_nsmul, hdomain, map_zero]
  have hnineteen : 19 • f q = 0 :=
    ZModModule.char_nsmul_eq_zero 19 (f q)
  calc
    f q = 8 • (12 • f q) - 5 • (19 • f q) := by abel
    _ = 0 := by rw [htwelve, hnineteen]; simp

/-- A trivial representation remains trivial on the invariant module after
factoring its action through a normal quotient. -/
theorem quotientToInvariants_isTrivial
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) [A.IsTrivial]
    (S : Subgroup G) [S.Normal] :
    (A.quotientToInvariants S).IsTrivial := by
  constructor
  intro q
  induction q using QuotientGroup.induction_on with
  | _ g =>
      ext x
      change A.ρ g x.1 = x.1
      exact A.ρ.isTrivial_apply g x.1

/-- For trivial coefficients in a `ZMod 19`-module, the restriction term in
inflation--restriction is a monomorphism when the quotient has cardinality
`12`. -/
theorem h1_restriction_mono_of_quotient_card_eq_twelve
    {G M : Type} [Group G]
    (S : Subgroup G) [S.Normal] [Finite (G ⧸ S)]
    [AddCommGroup M] [Module (ZMod 19) M]
    (hcard : Nat.card (G ⧸ S) = 12) :
    Mono
      (groupCohomology.H1InfRes
        (Rep.trivial (ZMod 19) G M) S).g := by
  let A : Rep (ZMod 19) G := Rep.trivial (ZMod 19) G M
  letI : (A.quotientToInvariants S).IsTrivial :=
    quotientToInvariants_isTrivial A S
  haveI : Subsingleton
      (Additive (G ⧸ S) →+ (A.quotientToInvariants S)) :=
    ⟨fun f g => by
      rw [addMonoidHom_eq_zero_of_card_eq_twelve hcard f,
        addMonoidHom_eq_zero_of_card_eq_twelve hcard g]⟩
  have hsource :
      IsZero (groupCohomology (A.quotientToInvariants S) 1) :=
    (groupCohomology.H1IsoOfIsTrivial
      (A.quotientToInvariants S)).isZero_iff.mpr
        (ModuleCat.isZero_of_subsingleton _)
  exact (groupCohomology.H1InfRes_exact A S).mono_g
    (hsource.eq_of_src _ _)

/-- Elementwise form of the degree-twelve base-change endpoint: restriction
on first group cohomology is injective. -/
theorem h1_restriction_injective_of_quotient_card_eq_twelve
    {G M : Type} [Group G]
    (S : Subgroup G) [S.Normal] [Finite (G ⧸ S)]
    [AddCommGroup M] [Module (ZMod 19) M]
    (hcard : Nat.card (G ⧸ S) = 12) :
    Function.Injective
      (groupCohomology.H1InfRes
        (Rep.trivial (ZMod 19) G M) S).g := by
  letI := h1_restriction_mono_of_quotient_card_eq_twelve
    (G := G) (M := M) S hcard
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The concrete coefficient specialization to the trivial `ZMod 19`
representation. -/
theorem h1_zmod_nineteen_restriction_injective
    {G : Type} [Group G]
    (S : Subgroup G) [S.Normal] [Finite (G ⧸ S)]
    (hcard : Nat.card (G ⧸ S) = 12) :
    Function.Injective
      (groupCohomology.H1InfRes
        (Rep.trivial (ZMod 19) G (ZMod 19)) S).g :=
  h1_restriction_injective_of_quotient_card_eq_twelve
    (G := G) (M := ZMod 19) S hcard

end MazurTorsion.XOneThirteenDegreeTwelveRestriction
