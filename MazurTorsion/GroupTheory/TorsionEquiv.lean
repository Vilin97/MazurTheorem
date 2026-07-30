/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.GroupTheory.Torsion

/-!
# Transporting torsion subgroups along additive equivalences

An additive equivalence preserves finite additive order, so it restricts to an equivalence of
torsion subgroups. This small bridge lets arithmetic arguments change Weierstrass models without
rebuilding their torsion-subtype maps by hand.
-/

@[expose] public section

namespace MazurTorsion

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- An additive equivalence maps a finite-order element to a finite-order element. -/
theorem isOfFinAddOrder_addEquiv
    (e : G ≃+ H) {x : G} (hx : IsOfFinAddOrder x) :
    IsOfFinAddOrder (e x) := by
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n, hn, ?_⟩
  simpa using congrArg e hnx

/-- The restriction of an additive equivalence to the torsion subgroups. -/
def torsionAddEquiv (e : G ≃+ H) :
    AddCommGroup.torsion G ≃+ AddCommGroup.torsion H where
  toFun x :=
    ⟨e x, isOfFinAddOrder_addEquiv e x.property⟩
  invFun y :=
    ⟨e.symm y, isOfFinAddOrder_addEquiv e.symm y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (e.map_add x y)

@[simp]
theorem torsionAddEquiv_apply_coe (e : G ≃+ H)
    (x : AddCommGroup.torsion G) :
    ((torsionAddEquiv e x : AddCommGroup.torsion H) : H) = e x :=
  rfl

@[simp]
theorem torsionAddEquiv_symm (e : G ≃+ H) :
    (torsionAddEquiv e).symm = torsionAddEquiv e.symm :=
  rfl

@[simp]
theorem addOrderOf_torsionAddEquiv (e : G ≃+ H)
    (x : AddCommGroup.torsion G) :
    addOrderOf (torsionAddEquiv e x) = addOrderOf x := by
  exact (torsionAddEquiv e).addOrderOf_eq x

end MazurTorsion
