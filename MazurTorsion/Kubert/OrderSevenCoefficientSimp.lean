/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.NormNum

/-!
# Order-seven coefficient simplification

This module registers the dedicated simplifier used by the generated
order-seven coefficient certificates.
-/

public meta section

register_simp_attr orderSevenCoefficient

/-- Normalize the bounded convolution blocks used by order-seven coefficient certificates. -/
macro "order_seven_normalize_coefficient_sum" : tactic =>
  do
    let stx ← `(tactic|
      (first
        | conv_lhs =>
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      (first
        | conv_lhs =>
          rhs
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      (first
        | conv_lhs =>
          rhs
          rhs
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      (first
        | conv_lhs =>
          rhs
          rhs
          rhs
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      (first
        | conv_lhs =>
          rhs
          rhs
          rhs
          rhs
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      (first
        | conv_lhs =>
          rhs
          rhs
          rhs
          rhs
          rhs
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      (first
        | conv_lhs =>
          rhs
          rhs
          rhs
          rhs
          rhs
          rhs
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      (first
        | conv_lhs =>
          rhs
          rhs
          rhs
          rhs
          rhs
          rhs
          rhs
          lhs
          simp (config := { failIfUnchanged := false }) only
            [Finset.sum_range_succ, orderSevenCoefficient]
          norm_num
        | skip) <;>
      norm_num [Finset.sum_range_succ])
    return ⟨stx.raw.rewriteBottomUp fun
      | .ident info rawVal val pre => .ident info rawVal val.eraseMacroScopes pre
      | other => other⟩
