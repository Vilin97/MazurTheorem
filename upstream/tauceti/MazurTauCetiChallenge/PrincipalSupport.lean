/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Finite support of scheme-theoretic orders

This is the global finiteness input needed to package Tau Ceti's existing
local order maps as a principal-divisor order system. It is an upstream
challenge: the theorem is open and earns no Mazur completion credit.
-/

public section

open AlgebraicGeometry

namespace MazurTauCetiChallenge

universe u

/-- A nonzero rational function on a Noetherian integral scheme has
nonzero order at only finitely many codimension-one points. -/
theorem finite_support_orderAt
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (g : Additive X.functionFieldˣ) :
    (Function.support fun x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X =>
      TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt x g).Finite :=
  TauCeti.AlgebraicGeometry.SchemeWeilDivisor.finite_support_orderAt X g

/-- The order system unlocked by `finite_support_orderAt`. This definition is
an acceptance consumer for the challenge theorem. -/
noncomputable def orderSystem
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] :
    TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ) :=
  TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem X

end MazurTauCetiChallenge
