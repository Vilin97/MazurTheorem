/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ElementaryGlobalSections
import MazurTorsion.GroupTheory.IndexNSmulFG

/-!
# The finite-flat Kummer rank-zero criterion

This file proves the numerical endpoint of Mazur's finite-flat rank-zero argument.  Let `A` be a
finitely generated abelian group and let `p` be prime.  If its Kummer quotient `A / pA` injects
into a finite commutative group whose cardinality is no larger than the cardinality of `A[p]`,
then `A` has rank zero.  The proof uses the checked index formula

`[A : pA] = p ^ rank(A) * |A[p]|`.

The final theorem is a geometric consumer rather than an abstract restatement.  Its target is
the repository's actual common-refinement fppf `H¹` of a finite-flat commutative group scheme.
It obtains the required cohomology bound from an honest two-factor admissible filtration and
the complete checked low-degree fppf exact sequence.

The remaining arithmetic inputs stay explicit: a future Eisenstein-quotient consumer must
construct its Mordell--Weil Kummer homomorphism, certify the two elementary endpoint `H¹`
groups, prove finiteness of the middle `H¹`, and identify the `p`-torsion cardinality.  No
constant-factor cohomology calculation or Raynaud uniqueness theorem is asserted here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u v

/-- The numerical Kummer criterion for a finitely generated abelian group.  The Kummer map is a
homomorphism from the actual multiplication-by-`p` quotient; its injectivity makes this quotient
finite and lets the cohomological cardinal bound control its index. -/
theorem finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    {H : Type v} [CommGroup H] [Finite H]
    (p torsionLength : ℕ) (hp : p.Prime)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →* H)
    (hkummer : Function.Injective kummer)
    (hcohomology : Nat.card H ≤ p ^ torsionLength) :
    Module.finrank ℤ A = 0 := by
  letI : Finite (A ⧸ (nsmulAddMonoidHom (α := A) p).range) :=
    Finite.of_injective kummer hkummer
  have hindex :
      (nsmulAddMonoidHom (α := A) p).range.index ≤ p ^ torsionLength := by
    rw [AddSubgroup.index_eq_card]
    exact (Nat.card_le_card_of_injective kummer hkummer).trans hcohomology
  have hformula := AddSubgroup.index_range_nsmul_of_fg A hp.ne_zero
  rw [hformula, hkernel] at hindex
  have hpow : p ^ Module.finrank ℤ A ≤ 1 := by
    apply Nat.le_of_mul_le_mul_right (b := 1) (c := p ^ torsionLength)
    · simpa using hindex
    · exact pow_pos hp.pos _
  have hpowequal : p ^ Module.finrank ℤ A = 1 :=
    le_antisymm hpow (Nat.one_le_pow _ _ hp.pos)
  simpa [hp.ne_one] using hpowequal

/-- The same Kummer bound makes the finitely generated abelian group finite, not merely rank
zero.  This is useful when the downstream quotient collision needs an actual finite group. -/
theorem finite_of_injective_kummer_of_card_le_torsion
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    {H : Type v} [CommGroup H] [Finite H]
    (p torsionLength : ℕ) (hp : p.Prime)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →* H)
    (hkummer : Function.Injective kummer)
    (hcohomology : Nat.card H ≤ p ^ torsionLength) :
    Finite A := by
  letI : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hrank := finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    p torsionLength hp hkernel kummer hkummer hcohomology
  have hmoduleTorsion : Module.IsTorsion ℤ A :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp hrank
  exact AddCommGroup.finite_of_fg_torsion A
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

namespace AdmissibleFiltrationStep

/-- A two-factor admissible finite-flat filtration over `Spec ℤ` supplies the cohomological
side of the Kummer rank-zero criterion.  In particular, this theorem consumes the actual
represented finite-flat `H¹` carrier and the checked low-degree fppf exact sequence; it does not
accept an unrelated finite group with a numerical bound. -/
theorem finrank_eq_zero_of_fppfKummer_int
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{0})
    (middleHOneFinite : Finite G.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →*
        G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hp2 : p ≠ 2)
    (hbound :
      middleHZeroData.length + kernelHOneData.length +
          quotientHOneData.length ≤
        torsionLength + D.kernelFactor.hZeroLength +
          D.quotientFactor.hZeroLength) :
    Module.finrank ℤ A = 0 := by
  letI : Finite G.FppfHOne.{0} := middleHOneFinite
  apply finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    p torsionLength D.prime hkernel kummer hkummer
  exact D.fppfHOne_natCard_le_pow_int middleHZeroData kernelHOneData
    middleHOneFinite quotientHOneData hp2 torsionLength hbound

/-- The same genuine finite-flat Kummer input makes the Mordell--Weil group finite.  This is the
form needed when the later formal-immersion argument uses finiteness rather than a rank equation. -/
theorem finite_of_fppfKummer_int
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{0})
    (middleHOneFinite : Finite G.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →*
        G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hp2 : p ≠ 2)
    (hbound :
      middleHZeroData.length + kernelHOneData.length +
          quotientHOneData.length ≤
        torsionLength + D.kernelFactor.hZeroLength +
          D.quotientFactor.hZeroLength) :
    Finite A := by
  letI : Finite G.FppfHOne.{0} := middleHOneFinite
  apply finite_of_injective_kummer_of_card_le_torsion
    p torsionLength D.prime hkernel kummer hkummer
  exact D.fppfHOne_natCard_le_pow_int middleHZeroData kernelHOneData
    middleHOneFinite quotientHOneData hp2 torsionLength hbound

end AdmissibleFiltrationStep

end AlgebraicGeometry.FiniteFlatCommGroupScheme
