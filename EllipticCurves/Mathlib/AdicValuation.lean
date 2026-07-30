/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
-/
module

public import Mathlib

@[expose] public section

/-!
# The residue map on `v`-integral elements of the fraction field

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R`.
An element of `K` of `v`-adic valuation at most `1` is congruent to an element of `R` modulo
elements of valuation `< 1` (`exists_valuation_sub_lt_of_integer`), and the class in
`R ⧸ v.asIdeal` of such an approximant does not depend on its choice.  This file packages the
resulting *residue map* as a ring homomorphism
`residueHom : (v.valuation K).integer →+* R ⧸ v.asIdeal`
on the subring of `v`-integral elements of `K`, extending `Ideal.Quotient.mk v.asIdeal`
(`residueHom_algebraMap`); an unfolding requires only *some* approximant (`residueHom_eq`).

It also provides the `R`-algebra structure on `(v.valuation K).integer` and the `Field`
instance on `R ⧸ v.asIdeal` (the ideal is maximal).
-/

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/- Implementation note (upstreaming): Mathlib deliberately keeps `Ideal.Quotient.field` a *local*
instance (cf. `RingTheory/DedekindDomain/Different.lean`, `RingTheory/Artinian/Module.lean`),
since maximality of a general ideal is not inferable.  Here the ideal is `v.asIdeal` for a
height-one prime `v` of a Dedekind domain, whose maximality is an instance
(`HeightOneSpectrum.isMaximal`), so the `Field` instance is keyed on `v` and safe to make global;
be prepared to demote it to a local instance if upstream review prefers that. -/
noncomputable instance : Field (R ⧸ v.asIdeal) := Ideal.Quotient.field _

noncomputable instance : Algebra R (v.valuation K).integer :=
  ((algebraMap R K).codRestrict (v.valuation K).integer fun r ↦ v.valuation_le_one r).toAlgebra

instance : IsScalarTower R (v.valuation K).integer K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

@[simp] lemma coe_algebraMap_integer (r : R) :
    ((algebraMap R (v.valuation K).integer r : (v.valuation K).integer) : K)
      = algebraMap R K r := rfl

/-- The distinguished `R`-approximant of a `v`-integral element of `K` (an element of `R`
congruent to it modulo valuation `< 1`).  Implementation detail of `residueHom`; use that (and
`residueHom_eq`) instead. -/
noncomputable def residueAux (x : (v.valuation K).integer) : R :=
  (v.exists_valuation_sub_lt_of_integer x.2 1).choose

private lemma valuation_sub_residueAux_lt (x : (v.valuation K).integer) :
    v.valuation K (algebraMap R K (residueAux v x) - x) < 1 :=
  lt_of_lt_of_eq (v.exists_valuation_sub_lt_of_integer x.2 1).choose_spec Units.val_one

/-- Two `R`-approximants of the same `v`-integral element agree modulo `v`. -/
private lemma mk_eq_mk_of_close {x : (v.valuation K).integer} {a b : R}
    (ha : v.valuation K (algebraMap R K a - x) < 1)
    (hb : v.valuation K (algebraMap R K b - x) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← intValuation_lt_one_iff_mem, ← valuation_of_algebraMap (K := K),
    Algebra.cast, map_sub (algebraMap R K)]
  calc v.valuation K (algebraMap R K a - algebraMap R K b)
      = v.valuation K ((algebraMap R K a - x) - (algebraMap R K b - x)) := by ring_nf
    _ ≤ max (v.valuation K (algebraMap R K a - x)) (v.valuation K (algebraMap R K b - x)) :=
        Valuation.map_sub _ _ _
    _ < 1 := max_lt ha hb

/-- An approximant of a `v`-integral element is itself `v`-integral in `K`. -/
private lemma valuation_le_one_of_close {x : (v.valuation K).integer} {a : R}
    (ha : v.valuation K (algebraMap R K a - x) < 1) :
    v.valuation K (algebraMap R K a) ≤ 1 := by
  calc v.valuation K (algebraMap R K a)
      = v.valuation K ((algebraMap R K a - x) + x) := by ring_nf
    _ ≤ max (v.valuation K (algebraMap R K a - x)) (v.valuation K x) := Valuation.map_add _ _ _
    _ ≤ 1 := max_le ha.le x.2

/-- The **residue map** on the `v`-integral elements of `K`, with values in the residue field
`R ⧸ v.asIdeal`: the class of any `R`-approximant within valuation `< 1`.  It extends
`Ideal.Quotient.mk v.asIdeal` (`residueHom_algebraMap`). -/
noncomputable def residueHom : (v.valuation K).integer →+* R ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (residueAux v x)
  map_one' := by
    rw [mk_eq_mk_of_close v (valuation_sub_residueAux_lt v 1) (b := 1) (by simp), map_one]
  map_mul' x y := by
    rw [← map_mul]
    refine mk_eq_mk_of_close v (valuation_sub_residueAux_lt v (x * y)) ?_
    have hx := valuation_sub_residueAux_lt v x
    have hy := valuation_sub_residueAux_lt v y
    calc v.valuation K (algebraMap R K (residueAux v x * residueAux v y) - (x * y : _))
        = v.valuation K (algebraMap R K (residueAux v x) * (algebraMap R K (residueAux v y) - y)
            + (y : K) * (algebraMap R K (residueAux v x) - x)) := by push_cast; ring_nf
      _ ≤ max (v.valuation K (algebraMap R K (residueAux v x)
              * (algebraMap R K (residueAux v y) - y)))
            (v.valuation K ((y : K) * (algebraMap R K (residueAux v x) - x))) :=
          Valuation.map_add _ _ _
      _ < 1 := by
          rw [map_mul, map_mul]
          refine max_lt (lt_of_le_of_lt (mul_le_of_le_one_left' ?_) hy)
            (lt_of_le_of_lt (mul_le_of_le_one_left' y.2) hx)
          exact valuation_le_one_of_close v hx
  map_zero' := by
    rw [mk_eq_mk_of_close v (valuation_sub_residueAux_lt v 0) (b := 0) (by simp), map_zero]
  map_add' x y := by
    rw [← map_add]
    refine mk_eq_mk_of_close v (valuation_sub_residueAux_lt v (x + y)) ?_
    have hx := valuation_sub_residueAux_lt v x
    have hy := valuation_sub_residueAux_lt v y
    calc v.valuation K (algebraMap R K (residueAux v x + residueAux v y) - (x + y : _))
        = v.valuation K ((algebraMap R K (residueAux v x) - x)
            + (algebraMap R K (residueAux v y) - y)) := by push_cast; ring_nf
      _ ≤ _ := Valuation.map_add _ _ _
      _ < 1 := max_lt hx hy

/-- Unfolding lemma for `residueHom`: the residue of `x` is the class of *any* `R`-approximant
of `x` within valuation `< 1`. -/
lemma residueHom_eq {x : (v.valuation K).integer} {a : R}
    (h : v.valuation K (algebraMap R K a - x) < 1) :
    residueHom v x = Ideal.Quotient.mk v.asIdeal a :=
  mk_eq_mk_of_close v (valuation_sub_residueAux_lt v x) h

@[simp] lemma residueHom_algebraMap (r : R) :
    residueHom v (algebraMap R (v.valuation K).integer r) = Ideal.Quotient.mk v.asIdeal r :=
  residueHom_eq v (by simp)

end IsDedekindDomain.HeightOneSpectrum

end
