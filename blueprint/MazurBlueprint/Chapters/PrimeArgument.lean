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

:::theorem "MT-PRIME-HERBRAND-KUMMER" (parent := "prime_argument") (uses := "MT-PRIME-DIVISION-FIELD, MT-NERON-COMPONENTS") (tags := "proof, done, integrated, prime-argument") (priority := "high") (effort := "medium")
*Exclude additive reduction at five.* The checked marked Tate-depth argument
on the selected minimal equation forces the terminal weighted coefficient
depths and contradicts minimality. No component-group bound is assumed.

*Status:* `done`.

* `theorem` (`integrated`):
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

Finite normalization, the canonical nonsingular-reduction group, and the
exact formal kernel discharge the intermediate exceptional-depth cases. The
terminal calculation derives `y ∈ 𝔪³`, forces `a₄ ∈ 𝔪⁴`, and obtains
`a₆ ∈ 𝔪⁶` from the point equation. The resulting pure scaling contradicts
minimality. `PrimeOrder.not_additiveReductionAtFive` is consumed by the
stable good-reduction theorem. Genuine identity components and completely
toric modular reduction remain work in the broader Néron infrastructure node,
not premises of this completed pointwise theorem.
:::

:::theorem "MT-PRIME-SPLIT-SEQUENCE" (parent := "prime_argument") (uses := "MT-PRIME-HERBRAND-KUMMER") (tags := "proof, done, integrated, prime-argument") (priority := "high") (effort := "small")
*Upgrade potentially good to good reduction.* Potentially good excludes a
multiplicative fibre; the preceding weighted-depth argument excludes an additive
fibre. The remaining fibre is good.

*Status:* `done`.

* `theorem` (`integrated`): `MazurTorsion.PrimeOrder.goodReductionAtFive`
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

The valuation of `j` is strictly greater than one under multiplicative
reduction, so integral `j` excludes that branch. The checked additive theorem
and Mathlib's exhaustive reduction trichotomy give good reduction. The same
rational point is transported through the selected minimal variable change
with unchanged exact order and then reduced into the exhaustively enumerated
`𝔽₅` group. The resulting local contradiction is consumed by both the
formal-immersion endpoint and the affine Hecke/q-expansion endpoint. The latter
packages an actual affine structural section through the selected fibre point
and derives its coordinate-ring retraction contravariantly. Represented
modular/cusp data remain in their upstream nodes.
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
