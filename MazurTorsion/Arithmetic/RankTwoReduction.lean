/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import MazurTorsion.Arithmetic.LowTorsionObstructions
import MazurTorsion.Foundations.NaiveHeightDescent
import MazurTorsion.GroupTheory.FiniteClassification
import MazurTorsion.NumberTheory.RatNorthcott

/-!
# Rank-two reduction for rational elliptic-curve torsion

This file joins the compiled low-level torsion obstructions to the finite-abelian classification.
It proves rational-torsion finiteness from naïve-height descent, derives the rank-two normal form,
then exposes only the remaining arithmetic inputs to the classification.
-/

open scoped WeierstrassCurve.Affine
namespace MazurTorsion
variable (E : WeierstrassCurve ℚ)
/-- Convert the generic finite-group shape into the elliptic-curve classification predicate. -/
theorem hasMazurClassification_of_groupShape
    (h : HasMazurGroupShape (RationalTorsion E)) :
    HasMazurClassification E := by
  rcases h with ⟨n, hn, he⟩ | ⟨n, hn, he⟩
  · exact Or.inl ⟨n, hn, he⟩
  · right
    simp only [allowedBicyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp [bicyclicParameters], by simpa using he⟩
    · exact ⟨2, by simp [bicyclicParameters], by simpa using he⟩
    · exact ⟨3, by simp [bicyclicParameters], by simpa using he⟩
    · exact ⟨4, by simp [bicyclicParameters], by simpa using he⟩
/-- Under a finite rank-two presentation, the already-compiled `2`, `3`, and `4` obstructions
leave exactly four arithmetic subgroup exclusions to obtain Mazur's classification. -/
theorem hasMazurClassification_of_rankTwo
    (horders : ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders)
    (h55 : ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E))
    (h77 : ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E))
    (h210 : ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E))
    (h212 : ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E))
    {m n : ℕ} (hmn : m ∣ n)
    (e : RationalTorsion E ≃+ (ZMod m × ZMod n)) :
    HasMazurClassification E := by
  let havoid : AvoidsMazurForbiddenSubgroups (RationalTorsion E) :=
    { c2Cube := rationalTorsion_forbids_zmod_two_cube E
      c3Square := rationalTorsion_forbids_zmod_three_square E
      c4Square := rationalTorsion_forbids_zmod_four_square E
      c5Square := h55
      c7Square := h77
      c2c10 := h210
      c2c12 := h212 }
  exact hasMazurClassification_of_groupShape E <|
    hasMazurGroupShape_of_rankTwo horders havoid hmn e

/-- Rational torsion is finite by Northcott and the naïve-height parallelogram law. -/
theorem rationalTorsion_finite [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite := by
  letI : (E⁄ℚ).IsElliptic := inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  obtain ⟨_, hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law (E⁄ℚ)
  exact Set.finite_coe_iff.mp (AddCommGroup.finite_torsion_of_descent' hC)

/-- Allowed element orders and the four elementary rank obstructions put finite rational torsion
in rank-two invariant-factor form. -/
theorem rationalTorsion_hasRankTwoPresentation
    (hfinite : (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite)
    (horders : ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders)
    (h55 : ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E))
    (h77 : ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E)) :
    ∃ m n : ℕ, m ∣ n ∧ Nonempty (RationalTorsion E ≃+ (ZMod m × ZMod n)) := by
  letI : Fintype (RationalTorsion E) := hfinite.fintype
  exact exists_rankTwoPresentation_of_allowed_orders_and_forbidden horders
    (rationalTorsion_forbids_zmod_two_cube E)
    (rationalTorsion_forbids_zmod_three_square E) h55 h77

/-- Package the finite-branch classification from the five remaining mathematical inputs. -/
theorem hasMazurClassificationIfFinite_of_rankTwo_inputs
    (horders : ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders)
    (h55 : ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E))
    (h77 : ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E))
    (h210 : ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E))
    (h212 : ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E)) :
    HasMazurClassificationIfFinite E := by
  intro hfinite
  obtain ⟨m, n, hmn, ⟨e⟩⟩ :=
    rationalTorsion_hasRankTwoPresentation E hfinite horders h55 h77
  exact hasMazurClassification_of_rankTwo E horders h55 h77 h210 h212 hmn e
/-- Exact LeanPool cardinality target, reduced to the five remaining arithmetic inputs. -/
theorem torsion_ncard_le_of_rankTwo_inputs [E.IsElliptic]
    (horders : ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders)
    (h55 : ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E))
    (h77 : ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E))
    (h210 : ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E))
    (h212 : ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E)) :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 :=
  torsion_ncard_le_of_classification E <|
    (hasMazurClassificationIfFinite_of_rankTwo_inputs E horders h55 h77 h210 h212)
      (rationalTorsion_finite E)
end MazurTorsion
