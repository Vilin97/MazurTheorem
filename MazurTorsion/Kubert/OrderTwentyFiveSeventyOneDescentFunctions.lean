/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCuspDivisorOrders

/-!
# Explicit order-twenty-five 71-descent functions

The determinant calculation behind the cuspidal subgroup gives more than an
annihilation statement.  If `g₀, …, g₄` have the five cyclic principal cusp
divisors, then

`12g₀ - 14g₁ - 5g₂ + 11g₃`

has principal divisor `71 • ([c₀] - [c₁])`.  In a multiplicative function
field written additively, this is the rational function used for the
`71`-Kummer descent.  This file checks that identity and all five rotations.

`orderTwentyFive_exists_seventyOneDescentFunctions_of_orderRelations` is the
named consumer of the pointwise modular-unit order interface.
-/

namespace MazurTorsion.Kubert

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

/-- The integral combination of four cyclic modular functions selected by
the determinant-`71` row certificate. -/
def orderTwentyFiveSeventyOneDescentCombination
    {G : Type*} [AddCommGroup G] (g0 g1 g2 g3 : G) : G :=
  12 • g0 - 14 • g1 - 5 • g2 + 11 • g3

/-- Cyclic rotation preserves the five principal cusp-divisor relations. -/
theorem orderTwentyFiveCuspPrincipalDivisorRelations_rotate
    {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G) (c0 c1 c2 c3 c4 : Y)
    (h : orderTwentyFiveCuspPrincipalDivisorRelations S c0 c1 c2 c3 c4) :
    orderTwentyFiveCuspPrincipalDivisorRelations S c1 c2 c3 c4 c0 := by
  rcases h with ⟨g0, g1, g2, g3, g4, h0, h1, h2, h3, h4⟩
  refine ⟨g1, g2, g3, g4, g0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [orderTwentyFiveCuspDivisorZero,
      orderTwentyFiveCuspDivisorOne] using h1
  · simpa [orderTwentyFiveCuspDivisorOne,
      orderTwentyFiveCuspDivisorTwo] using h2
  · simpa [orderTwentyFiveCuspDivisorTwo,
      orderTwentyFiveCuspDivisorThree] using h3
  · simpa [orderTwentyFiveCuspDivisorThree,
      orderTwentyFiveCuspDivisorFour] using h4
  · simpa [orderTwentyFiveCuspDivisorFour,
      orderTwentyFiveCuspDivisorZero] using h0

/-- The explicit integral combination has divisor `71` times the first
adjacent cusp difference. -/
theorem orderTwentyFive_exists_seventyOneDescentFunction
    {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G) (c0 c1 c2 c3 c4 : Y)
    (h : orderTwentyFiveCuspPrincipalDivisorRelations S c0 c1 c2 c3 c4) :
    ∃ g : G,
      S.principalDivisor g = 71 • (ofPoint c0 - ofPoint c1) := by
  rcases h with ⟨g0, g1, g2, g3, _g4, h0, h1, h2, h3, _h4⟩
  refine ⟨orderTwentyFiveSeventyOneDescentCombination g0 g1 g2 g3, ?_⟩
  change S.principalHom
      (12 • g0 - 14 • g1 - 5 • g2 + 11 • g3) = _
  rw [map_add, map_sub, map_sub, map_nsmul, map_nsmul, map_nsmul,
    map_nsmul]
  simp only [S.principalHom_apply]
  rw [← h0, ← h1, ← h2, ← h3]
  simp only [orderTwentyFiveCuspDivisorZero,
    orderTwentyFiveCuspDivisorOne, orderTwentyFiveCuspDivisorTwo,
    orderTwentyFiveCuspDivisorThree]
  abel

/-- All five adjacent cusp differences have cyclically related
`71`-descent functions. -/
theorem orderTwentyFive_exists_seventyOneDescentFunctions
    {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G) (c0 c1 c2 c3 c4 : Y)
    (h : orderTwentyFiveCuspPrincipalDivisorRelations S c0 c1 c2 c3 c4) :
    ∃ g01 g12 g23 g34 g40 : G,
      S.principalDivisor g01 = 71 • (ofPoint c0 - ofPoint c1) ∧
      S.principalDivisor g12 = 71 • (ofPoint c1 - ofPoint c2) ∧
      S.principalDivisor g23 = 71 • (ofPoint c2 - ofPoint c3) ∧
      S.principalDivisor g34 = 71 • (ofPoint c3 - ofPoint c4) ∧
      S.principalDivisor g40 = 71 • (ofPoint c4 - ofPoint c0) := by
  have h1 := orderTwentyFiveCuspPrincipalDivisorRelations_rotate
    S c0 c1 c2 c3 c4 h
  have h2 := orderTwentyFiveCuspPrincipalDivisorRelations_rotate
    S c1 c2 c3 c4 c0 h1
  have h3 := orderTwentyFiveCuspPrincipalDivisorRelations_rotate
    S c2 c3 c4 c0 c1 h2
  have h4 := orderTwentyFiveCuspPrincipalDivisorRelations_rotate
    S c3 c4 c0 c1 c2 h3
  rcases orderTwentyFive_exists_seventyOneDescentFunction
      S c0 c1 c2 c3 c4 h with ⟨g01, hg01⟩
  rcases orderTwentyFive_exists_seventyOneDescentFunction
      S c1 c2 c3 c4 c0 h1 with ⟨g12, hg12⟩
  rcases orderTwentyFive_exists_seventyOneDescentFunction
      S c2 c3 c4 c0 c1 h2 with ⟨g23, hg23⟩
  rcases orderTwentyFive_exists_seventyOneDescentFunction
      S c3 c4 c0 c1 c2 h3 with ⟨g34, hg34⟩
  rcases orderTwentyFive_exists_seventyOneDescentFunction
      S c4 c0 c1 c2 c3 h4 with ⟨g40, hg40⟩
  exact ⟨g01, g12, g23, g34, g40, hg01, hg12, hg23, hg34, hg40⟩

/-- Pointwise modular-unit orders produce all five explicit global
`71`-descent functions. -/
theorem orderTwentyFive_exists_seventyOneDescentFunctions_of_orderRelations
    {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G) (c0 c1 c2 c3 c4 : Y)
    (h : orderTwentyFiveCuspOrderRelations S c0 c1 c2 c3 c4) :
    ∃ g01 g12 g23 g34 g40 : G,
      S.principalDivisor g01 = 71 • (ofPoint c0 - ofPoint c1) ∧
      S.principalDivisor g12 = 71 • (ofPoint c1 - ofPoint c2) ∧
      S.principalDivisor g23 = 71 • (ofPoint c2 - ofPoint c3) ∧
      S.principalDivisor g34 = 71 • (ofPoint c3 - ofPoint c4) ∧
      S.principalDivisor g40 = 71 • (ofPoint c4 - ofPoint c0) :=
  orderTwentyFive_exists_seventyOneDescentFunctions S c0 c1 c2 c3 c4
    (orderTwentyFiveCuspPrincipalDivisorRelations_of_orderRelations
      S c0 c1 c2 c3 c4 h)

end MazurTorsion.Kubert
