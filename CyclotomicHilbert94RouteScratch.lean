import MazurTorsion.NumberTheory.CyclotomicCapitulation
import MazurTorsion.NumberTheory.CyclotomicPseudoUnitUnramified
import MazurTorsion.NumberTheory.CyclotomicSelmerClassGroup
import MazurTorsion.NumberTheory.KummerArtinProduct

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- The full honest Hilbert--94 consequence of the two local pseudo-unit
hypotheses: a nontrivial exponent-`p`, Galois-stable capitulation orbit. -/
theorem scratch_localPseudoUnit_exists_nontrivial_p_torsion_capitulating_orbit
    (hp : 2 < p)
    (E : InverseExtension p L)
    (hdiv : E.kummerPresentation.HasPDivisibleFiniteDivisor E)
    (hlocal : E.kummerPresentation.IsPthPowerAtCyclotomicPrime E) :
    ∃ c : ClassGroup
        (NumberField.RingOfIntegers (PrimeCyclotomicField p)),
      c ≠ 1 ∧ c ^ p = 1 ∧
        ∀ σ : Gal(PrimeCyclotomicField p/ℚ),
          E.capitulationHom (classGroupAutomorphism p σ c) = 1 := by
  have hunramified : E.IsUnramifiedAtFinitePlaces :=
    E.isUnramifiedAtFinitePlaces_of_pseudoUnit_locallyPrimary hdiv hlocal
  exact E.exists_nontrivial_p_torsion_capitulating_orbit hp hunramified

/-- The canonical Kummer divisor-root class supplied by the same hypotheses
has the square-direct-character action, and is either nontrivial or leaves
the unresolved global-unit branch. -/
theorem scratch_localPseudoUnit_canonicalRootClass_package
    (E : InverseExtension p L)
    (hdiv : E.kummerPresentation.HasPDivisibleFiniteDivisor E)
    (hlocal : E.kummerPresentation.IsPthPowerAtCyclotomicPrime E) :
    let c := ClassGroup.mk (PrimeCyclotomicField p)
      E.unramifiedRadicandRootIdeal
    c ^ p = 1 ∧
      (∀ σ : Gal(PrimeCyclotomicField p/ℚ),
        classGroupAutomorphism p σ c =
          c ^ (((((directCharacter p σ) ^ 2 : (ZMod p)ˣ) :
            ZMod p)).val)) ∧
      (c ≠ 1 ∨
        ∃ (u : (NumberField.RingOfIntegers
              (PrimeCyclotomicField p))ˣ)
            (y : (PrimeCyclotomicField p)ˣ),
          E.kummerPresentation.radicand =
            algebraMap
              (NumberField.RingOfIntegers (PrimeCyclotomicField p))
              (PrimeCyclotomicField p) (u : _) *
              (y : PrimeCyclotomicField p) ^ p) := by
  have hunramified : E.IsUnramifiedAtFinitePlaces :=
    E.isUnramifiedAtFinitePlaces_of_pseudoUnit_locallyPrimary hdiv hlocal
  dsimp only
  refine ⟨E.unramifiedRadicandClass_pow_eq_one hunramified, ?_,
    (E.unramifiedRadicand_class_or_unit hunramified).2⟩
  intro σ
  exact E.classGroupAutomorphism_unramifiedRadicandRootClass
    hunramified σ

end NumberTheory.CyclotomicCharacter.InverseExtension
