/-
This exact-pin integration harness uses reduction infrastructure and transport patterns derived
from Michael Stoll's EllipticCurves repository at commit
3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f, released under Apache 2.0; see LICENSE.
The harness itself is new for the LeanPool exceptional-cubic endpoint.
-/
module

public import EllipticCurves.ReductionAtPrime

@[expose] public section

/-!
# Reduction of the exceptional cubic modulo five

This file is an exact-pin integration test for the reduction-at-a-prime API.  It treats the
integral model

`y² = x³ + 2x² - 3x`

of the exceptional cubic used in the Mazur theorem development.  Reduction at `(5)` is
injective on rational torsion, and the reduced curve has exactly eight points.  Consequently,
once finiteness of the rational point group is supplied by the independent descent argument,
the rational point group has cardinality at most eight.
-/

open WeierstrassCurve

namespace ExceptionalCubicReduction

open WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The exceptional cubic as an integral Weierstrass model. -/
def integralCurve : WeierstrassCurve ℤ :=
  ⟨0, 2, 0, -3, 0⟩

/-- The exceptional cubic over the rationals. -/
def curve : Affine ℚ :=
  ⟨0, 2, 0, -3, 0⟩

lemma map_integralCurve : integralCurve.map (algebraMap ℤ ℚ) = curve := by
  ext <;> simp [integralCurve, curve]

lemma discriminant_integralCurve : integralCurve.Δ = 2304 := by
  norm_num [integralCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : curve.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero, ← map_integralCurve, map_Δ,
    discriminant_integralCurve]
  norm_num

/-- The height-one prime `(p)` of `ℤ`. -/
def intPrime (p : ℕ) [Fact p.Prime] : HeightOneSpectrum ℤ :=
  .ofPrime (p := Ideal.span {(p : ℤ)})
    (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp Fact.out))

@[simp] lemma intPrime_asIdeal (p : ℕ) [Fact p.Prime] :
    (intPrime p).asIdeal = Ideal.span {(p : ℤ)} :=
  rfl

instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℤ ⧸ (intPrime p).asIdeal) :=
  (Int.quotientSpanNatEquivZMod p).toEquiv.decidableEq

lemma isElliptic_redCurve {p : ℕ} [Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ integralCurve.Δ) :
    (redCurve (intPrime p) integralCurve).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  change (integralCurve.map (algebraMap ℤ (ℤ ⧸ (intPrime p).asIdeal))).Δ ≠ 0
  rwa [Ne, map_Δ, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
    intPrime_asIdeal, Ideal.mem_span_singleton]

instance : (redCurve (intPrime 5) integralCurve).IsElliptic :=
  isElliptic_redCurve (by norm_num [discriminant_integralCurve])

/-- The concrete reduction over `ZMod 5`. -/
def curveModFive : WeierstrassCurve (ZMod 5) :=
  ⟨0, 2, 0, -3, 0⟩

instance : curveModFive.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

noncomputable def residueFiveAlgEquiv :
    (ℤ ⧸ (intPrime 5).asIdeal) ≃ₐ[ℤ] ZMod 5 :=
  AlgEquiv.ofRingEquiv (f := Int.quotientSpanNatEquivZMod 5) fun x ↦ by
    simp only [algebraMap_int_eq, eq_intCast, map_intCast]

lemma baseChange_modFive :
    ((integralCurve.toAffine ⁄ (ZMod 5)) : WeierstrassCurve _).toAffine =
      curveModFive.toAffine := by
  ext <;> decide +kernel

/-- Identification of the abstract residue-field point group with the computable `ZMod 5`
point group. -/
noncomputable def reducedPointEquiv :
    (redCurve (intPrime 5) integralCurve).Point ≃+ curveModFive.toAffine.Point :=
  (Point.mapEquiv (W' := integralCurve.toAffine) residueFiveAlgEquiv).trans
    (Point.congr baseChange_modFive)

noncomputable instance : Finite (redCurve (intPrime 5) integralCurve).Point :=
  .of_equiv curveModFive.toAffine.Point reducedPointEquiv.symm.toEquiv

/-- The reduction modulo five has exactly eight points. -/
theorem card_reducedCurve : Nat.card (redCurve (intPrime 5) integralCurve).Point = 8 := by
  calc
    Nat.card (redCurve (intPrime 5) integralCurve).Point =
        Fintype.card curveModFive.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans Nat.card_eq_fintype_card
    _ = 8 := by decide

lemma five_mem_prime : (5 : ℤ) ∈ (intPrime 5).asIdeal :=
  Ideal.mem_span_singleton_self 5

lemma five_not_mem_prime_pow_four :
    (5 : ℤ) ∉ (intPrime 5).asIdeal ^ (5 - 1) := by
  rw [intPrime_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  norm_num

/-- Reduction at five, restricted to the rational torsion subgroup. -/
noncomputable def torsionReduction :
    AddCommGroup.torsion curve.Point →+
      (redCurve (intPrime 5) integralCurve).Point :=
  (redHom (intPrime 5) map_integralCurve).comp
    (AddSubgroup.subtype (AddCommGroup.torsion curve.Point))

/-- Reduction at five is injective on rational torsion. -/
theorem torsionReduction_injective : Function.Injective torsionReduction := by
  intro P Q hPQ
  change redHom (intPrime 5) map_integralCurve (P : curve.Point) =
    redHom (intPrime 5) map_integralCurve (Q : curve.Point) at hPQ
  let D : AddCommGroup.torsion curve.Point := P - Q
  have hDfin : IsOfFinAddOrder (D : curve.Point) := D.property
  have hDred : red (intPrime 5) map_integralCurve (D : curve.Point) = 0 := by
    change redHom (intPrime 5) map_integralCurve (D : curve.Point) = 0
    change redHom (intPrime 5) map_integralCurve
      ((P : curve.Point) - (Q : curve.Point)) = 0
    rw [map_sub, hPQ, sub_self]
  have hDzero : (D : curve.Point) = 0 :=
    eq_zero_of_isOfFinAddOrder_of_red_eq_zero (intPrime 5) map_integralCurve
      (by norm_num) five_mem_prime five_not_mem_prime_pow_four hDfin hDred
  apply Subtype.ext
  exact sub_eq_zero.mp hDzero

/-- If the rational point group is finite, reduction at five is injective on all of it. -/
theorem reduction_injective_of_finite [Finite curve.Point] :
    Function.Injective (redHom (intPrime 5) map_integralCurve) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero (intPrime 5) map_integralCurve
    (by norm_num) five_mem_prime five_not_mem_prime_pow_four
    (isOfFinAddOrder_of_finite (P - Q))
  change redHom (intPrime 5) map_integralCurve (P - Q) = 0
  rw [map_sub, hPQ, sub_self]

/-- Once an independent descent supplies finiteness, the exceptional cubic has at most eight
rational points. -/
theorem point_card_le_eight [Finite curve.Point] :
    Nat.card curve.Point ≤ 8 := by
  calc
    Nat.card curve.Point ≤ Nat.card (redCurve (intPrime 5) integralCurve).Point :=
      Nat.card_le_card_of_injective (redHom (intPrime 5) map_integralCurve)
        reduction_injective_of_finite
    _ = 8 := card_reducedCurve

end ExceptionalCubicReduction

end
