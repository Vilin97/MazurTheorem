import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "05 — Mazur's prime-order argument" =>

:::group "prime_argument"
Mazur's 1978 degree-one formal-immersion argument at the single auxiliary
prime five.  Potentially multiplicative reduction gives a cusp collision;
formal immersion makes that impossible. Tame fibre arithmetic then gives
good reduction, and a finite enumeration over `𝔽₅` finishes. Stage
weight: 100 points.
:::

:::theorem "MT-PRIME-SEMISTABLE" (parent := "prime_argument") (uses := "MT-X0-MODULI, MT-X0-EISENSTEIN-QUOTIENT, MT-EC-ISOGENY-WEIL") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "medium")
*Attach the modular point and its finite quotient image.* A rational point of
prime order gives a rational cyclic subgroup, hence an $`X_0(N)` point. Its
image in the rank-zero Eisenstein quotient has finite order.

*Status:* `blocked`. The immutable identifier records the former semistability
node; no semistability theorem is required by the revised route.

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.xZeroPoint_of_rationalPrimeTorsion`
* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.eisensteinImage_isTorsion`
:::

:::theorem "MT-PRIME-OUTSIDE-IDENTITY" (parent := "prime_argument") (uses := "MT-PRIME-SEMISTABLE, MT-X0-CUSPS") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "medium")
*Detect cusp reduction at five.* Potentially multiplicative reduction sends
the classifying point to a cusp.  Atkin--Lehner transport moves that cusp to
infinity, the point where the formal-immersion API is normalized.

*Status:* `blocked`.

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.xZeroPoint_specializesToInfinity_of_potentiallyMultiplicativeAtFive`
:::

:::theorem "MT-PRIME-EISENSTEIN-SPECIALIZATION" (parent := "prime_argument") (uses := "MT-PRIME-OUTSIDE-IDENTITY, MT-X0-EISENSTEIN-QUOTIENT, MT-NERON-SPECIALIZATION") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*Formal immersion forces potentially good reduction at five.* A finite-order
quotient section that specializes to zero is zero because $`e=1<5-1`.
The modular section and the cusp would then cross with equal images, contrary
to formal immersion.

*Status:* `blocked`.

The local collision endpoint now compiles over the actual completed integer
ring at five. Equality of the modular and cusp closed points transports formal
immersion to the modular point; equality of their quotient sections then
forces equality of the integral sections, contradicting their supplied
distinctness and proving the `j`-valuation bound. What remains here is to
construct those modular and cusp sections and prove their bad-valuation
specialization and Eisenstein-quotient equality.

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.primeTorsion_potentiallyGoodReductionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_formalImmersionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_quotientCotangentCertificateAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_quotientCotangentAtFive_of_nonsingularReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_mappedIdealCotangentAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_mappedCotangentAtFive_of_nonsingularReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_mappedIdealDegreeOneCotangentAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_mappedDegreeOneCotangentAtFive_of_nonsingularReduction`
:::

:::theorem "MT-PRIME-DIVISION-FIELD" (parent := "prime_argument") (uses := "MT-PRIME-EISENSTEIN-SPECIALIZATION, MT-NERON-SPECIALIZATION") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "small")
*Preserve the marked torsion under specialization.* Since $`N\ne5`, the
prime-to-residue-characteristic specialization theorem keeps the marked
point's exact order in the Néron special fibre.  No division field is built.

*Status:* `blocked`.

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.specializedPoint_addOrderOf_eq_atFive`
:::

:::theorem "MT-PRIME-HERBRAND-KUMMER" (parent := "prime_argument") (uses := "MT-PRIME-DIVISION-FIELD, MT-NERON-COMPONENTS") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "medium")
*Exclude additive reduction at five.* In tame characteristic five, the
component group has order at most four, the additive quotient has order five,
and the formal kernel is pro-five.  Such a fibre has no point of prime order
at least eleven.

*Status:* `blocked`.

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.not_additiveReductionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.addOrderOf_ne_prime_ge_eleven_of_componentExponentTwelveAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive`
* `definition` (`contract`):
  `MazurTorsion.EllipticCurve.TameAdditiveReductionDataAtFive.toTameAdditiveFiltrationData`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.minimalCompletionAtFive_reduction_invariants_of_hasAdditiveReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_valuationInput_of_hasAdditiveReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_coefficientObstruction_of_hasAdditiveReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_hasAdditiveReduction_variableChange_of_valuation_u_eq_one`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_translatedCoefficientObstruction_of_hasAdditiveReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.addOrderOf_ne_prime_ge_eleven_of_markedExceptionalCubic_simpleRootAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.minimalCompletionAtFive_tateAlgorithm_exists_markedExceptionalCubic_repeatedRoot_of_primeOrder`

The narrower canonical five-adic handoff needs only `12 • P` in the
nonsingular-reduction subgroup and the exact torsion-free formal kernel.
Finite normalization and enumeration now turn the vanishing reduced `Δ` and
`c₄` into the actual five-element residue additive group. The checked
pointwise quotient-order API derives the exponent from a marked class of
finite order at most four. Residue translation, exact short normalization,
and honest one-factor cusp-chart identities now compile. In the first
coefficient-depth branch every local point has nonsingular reduction, so the
prime-order consumer rules it out and forces `a₆ ∈ 𝔪²` on the same selected
model. The next tangent branch puts `2 • P` in that subgroup and forces
`a₄ ∈ 𝔪²`; the following tangent--secant branch puts `3 • P` there and forces
`a₆ ∈ 𝔪³`. Canonical subgroup membership and marked multiples transport
through the integral unit normalization. The same-model exceptional-cubic
package now proves that a simple marked root puts `2 • P` in the subgroup.
The exact prime-order consumer rules out this branch and returns a repeated
marked root using the original chart uniformizer. A nonzero repeated root
either sends the double into canonical reduction or gives `2P` the simple
root `-2r`; hence `4P` enters the subgroup. The arithmetic consumer forces
`r=0` and derives `x ∈ 𝔪²`, `a₄ ∈ 𝔪³`, `a₆ ∈ 𝔪⁴` on the same model. The
next pointwise tangent--secant calculation puts `3 • P` in the subgroup when
`a₆ ∉ 𝔪⁵`; the actual prime-order consumer therefore forces `a₆ ∈ 𝔪⁵` while
retaining fourth depth on the same model. The later weighted case and final
minimality contradiction remain open, as does genuine identity-component
identification; no full component-cardinality or Kodaira claim is used here.
:::

:::theorem "MT-PRIME-SPLIT-SEQUENCE" (parent := "prime_argument") (uses := "MT-PRIME-HERBRAND-KUMMER") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "small")
*Upgrade potentially good to good reduction.* Potentially good excludes a
multiplicative fibre; the preceding component argument excludes an additive
fibre. The remaining fibre is good.

*Status:* `blocked`.

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.goodReductionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_gt_one_of_hasMultiplicativeReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.not_hasMultiplicativeReduction_of_valuation_j_le_one`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.completionPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.completionPoint_addOrderOf_ne_of_eleven_le_of_componentExponentTwelveAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.minimalCompletionPointAtFive_addOrderOf`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_minimalCompletionAtFive_j`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_eleven_le_of_minimalCompletionInputsAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_componentExponentTwelveAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_tameReductionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_nonsingularReduction`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.completionPoint_primeOrder_ne_of_cuspidalReduction_of_componentExponentTwelveAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_cuspidalReduction_of_componentExponentTwelveAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.minimalCompletionPointAtFive_twelve_nsmul_mem_of_markedComponentOrderAtMostFour`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_cuspidalReduction_of_markedComponentOrderAtMostFourAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_formalImmersionAtFive_of_componentExponentTwelve`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_mappedDegreeOneCotangentAtFive_of_componentExponentTwelve`

The valuation of `j` is now proved strictly greater than one under
multiplicative reduction, so integral `j` excludes that branch. Mathlib's
exhaustive reduction-type trichotomy and the checked tame-additive consumer
then prove good reduction. The completion-level consumer carries that same
marked point through the selected integral model, exact-order reduction, and
the residue-field equivalence to the checked `𝔽₅` contradiction. The rational
point is now base-changed and carried through Mathlib's selected minimal
variable change with unchanged exact order; `j`-invariance and the completion
valuation comparison return the local hypothesis to the rational curve. The
new formal-immersion consumer discharges that rational `j` premise from the
explicit modular/cusp collision inputs and reaches the same `F₅` contradiction.
Its canonical nonsingular-reduction consumer fixes the actual minimal
integral model, coordinate domain/map, and exact formal kernel, accepting no
arbitrary identity subgroup or reduction homomorphism. Lane-specific
completion, rational, formal-immersion, and degree-one cusp-stalk consumers
discharge the cuspidal special-locus classification. The newest rational
consumer replaces the full component-cardinality input by the exact pointwise
statement that the marked quotient class has finite order at most four; the
checked generic bridge derives `12 • P ∈ E₀`. The represented modular/cusp
collision, genuine Néron identity-component identification, and tame
Tate--Kodaira proof of that marked-class bound remain open, so this node
receives no completion credit.
:::

:::theorem "MT-PRIME-SHAFAREVICH" (parent := "prime_argument") (uses := "MT-PRIME-SPLIT-SEQUENCE") (tags := "proof, done, integrated, prime-argument") (priority := "high") (effort := "small")
*The ten-point finite enumeration.* Normalize the good fibre to short
Weierstrass form (valid in characteristic five), enumerate the 25 coefficient
pairs, and verify `#E(𝔽₅) ≤ 10`. This avoids adding a general Hasse
theorem solely for one tiny field and replaces Shafarevich finiteness.

*Status:* `done`.

* `theorem` (`integrated`):
  `MazurTorsion.PrimeOrder.card_reductionAtFive_le_ten`

* `theorem` (`integrated`):
  `MazurTorsion.PrimeOrder.zmod_five_addOrderOf_ne_of_eleven_le`
:::

:::theorem "MT-PRIME-ISOGENY-CHAIN" (parent := "prime_argument") (uses := "MT-PRIME-SHAFAREVICH, MT-X0-EISENSTEIN-QUOTIENT") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "small")
*Exclude order eleven and all primes at least seventeen.* The marked point
injects into a group of at most ten elements.  The Eisenstein quotient is
nontrivial for $`N=11` and prime $`N\ge17`; level thirteen remains the
separate genus-two endpoint.

*Status:* `blocked`.

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_eleven`
* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_prime_ge_seventeen`
:::
