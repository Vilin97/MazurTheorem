import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "05 — Mazur's prime-order argument" =>

:::group "prime_argument"
A route-neutral degree-one formal-immersion collision at 5, followed by the checked
minimal-model additive exclusion, prime-to-five specialization, and ten-point
enumeration. Stage weight: 100 points.
:::

:::theorem "MT-PRIME-SEMISTABLE" (parent := "prime_argument") (uses := "MT-X0-MODULI, MT-X0-EISENSTEIN-QUOTIENT, MT-EC-ISOGENY-WEIL") (tags := "proof, blocked, nouns-missing, mazur")
*Attach the modular point and its finite quotient image.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 10 points.

*Summary:* A rational point of prime order N gives a rational cyclic subgroup, an
X\_0(N) point, and therefore a finite-order point in the rank-zero Eisenstein quotient.

*Canonical artifacts:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.xZeroPoint_of_rationalPrimeTorsion`
  Construct the classifying X\_0(N)(Q) point from the generated cyclic subgroup.
* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.eisensteinImage_isTorsion`
  Use finiteness of the quotient's rational points to make the modular image torsion.

:::

:::theorem "MT-PRIME-OUTSIDE-IDENTITY" (parent := "prime_argument") (uses := "MT-PRIME-SEMISTABLE, MT-X0-CUSPS") (tags := "proof, blocked, nouns-missing, mazur")
*Detect cusp reduction at the auxiliary prime five.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 10 points.

*Summary:* If the elliptic curve is potentially multiplicative at 5, its X\_0(N) point
specializes to a cusp; Atkin-Lehner transport reduces the collision to infinity.

*Canonical artifacts:*

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.xZeroPoint_specializesToInfinity_of_potentiallyMultiplicativeAtFive`
  Move the specialized cusp to infinity without changing the quotient argument.

:::

:::theorem "MT-PRIME-EISENSTEIN-SPECIALIZATION" (parent := "prime_argument") (uses := "MT-PRIME-OUTSIDE-IDENTITY, MT-X0-EISENSTEIN-QUOTIENT, MT-NERON-SPECIALIZATION") (tags := "proof, blocked, nouns-missing, mazur")
*Formal immersion forces potentially good reduction at five.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 20 points.

*Summary:* A finite-order quotient point specializing to zero is zero by the unramified
specialization lemma.

*Canonical artifacts:*

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.primeTorsion_potentiallyGoodReductionAtFive`
  Implement Mazur 1978 Corollary 4.3 at the single unramified prime five.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_formalImmersionAtFive`
  Turn the explicit modular/cusp closed-point collision and quotient-section equality
  into the five-adic j-valuation bound using the checked completed-stalk formal
  immersion.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_quotientCotangentCertificateAtFive`
  Derive formal immersion from the quotient-cotangent certificate on the actual
  five-adic cusp stalk and feed it to the rational j collision.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_quotientCotangentAtFive_of_nonsingularReduction`
  Consume the cusp-stalk quotient calculation and canonical nonsingular-reduction inputs
  in the checked prime-order F\_5 contradiction.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_mappedIdealCotangentAtFive`
  Derive the five-adic j bound directly from the extended special-fibre ideal and its
  quotient cotangent calculation.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_mappedCotangentAtFive_of_nonsingularReduction`
  Feed the mapped characteristic-five cotangent calculation directly to the canonical
  prime-order F\_5 contradiction.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_le_one_of_mappedIdealDegreeOneCotangentAtFive`
  Derive the five-adic j bound from the concrete degree-one quotient-fibre outputs
  detected by q-expansion.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_mappedDegreeOneCotangentAtFive_of_nonsingularReduction`
  Consume degree-one special-fibre data and checked canonical reduction additivity in
  the prime-order endpoint.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_properModelSpecializationAtFive`
  Feed an actual proper commutative quotient model, its identified generic fibre,
  section collision, generic-fibre torsion, and a supplied torsion-specialization
  injectivity predicate to the checked formal-immersion prime-order contradiction; no
  full Neron mapping property or specialization theorem is constructed.

:::

:::theorem "MT-PRIME-DIVISION-FIELD" (parent := "prime_argument") (uses := "MT-BASE-INTEGRATED") (tags := "proof, done, integrated, mazur")
*Preserve exact prime-to-five order under good reduction.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 15 points.

*Summary:* The checked good-reduction specialization homomorphism preserves the exact
finite additive order of the marked point at 5.

*Canonical artifacts:*

* `theorem` (`integrated`):
  `MazurTorsion.PrimeOrder.specializedPoint_addOrderOf_eq_atFive_of_goodReduction`
  Preserve the exact additive order of every finite-order point under good reduction at
  5.
* `theorem` (`integrated`):
  `MazurTorsion.PrimeOrder.specializedPointZMod_addOrderOf_eq_atFive_of_goodReduction`
  Transport exact order to the concrete ZMod 5 reduction used by the finite-field
  endpoint.
* `theorem` (`integrated`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_of_eleven_le_of_goodReductionAtFive`
  Consume exact-order specialization and the ten-point enumeration to exclude every
  marked order at least 11 under good reduction.

:::

:::theorem "MT-PRIME-HERBRAND-KUMMER" (parent := "prime_argument") (uses := "MT-BASE-INTEGRATED") (tags := "proof, done, integrated, mazur")
*Exclude additive reduction at five.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 10 points.

*Summary:* The checked marked Tate-depth argument excludes additive reduction at 5 by
forcing a forbidden weighted rescaling of the selected minimal equation.

*Canonical artifacts:*

* `theorem` (`integrated`): `MazurTorsion.PrimeOrder.not_additiveReductionAtFive`
  Exclude additive reduction by the checked marked weighted-depth and minimality
  contradiction; the good-reduction theorem is its compiled consumer.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive`
  Prove the prime-order contradiction from the component, additive-residue, and
  torsion-free formal-kernel filtration.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.addOrderOf_ne_prime_ge_eleven_of_componentExponentTwelveAtFive`
  Exclude a marked prime-order point using only its component exponent, the five-element
  identity-component reduction target, and the torsion-free formal kernel.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive`
  Instantiate the component-exponent contradiction on canonical coordinatewise
  nonsingular reduction and discharge the formal-kernel theorem at five.
* `definition` (`contract`):
  `MazurTorsion.EllipticCurve.TameAdditiveReductionDataAtFive.toTameAdditiveFiltrationData`
  Convert the canonical five-adic handoff to the checked torsion filtration while
  deriving finite component and torsion-free formal-kernel inputs.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.minimalCompletionAtFive_reduction_invariants_of_hasAdditiveReduction`
  Specialize vanishing of the discriminant and c₄ to Mathlib's selected minimal
  five-adic integral model, starting the cuspidal nonsingular-locus classification.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_valuationInput_of_hasAdditiveReduction`
  Package the additive-reduction and integral-j valuation inequalities consumed by the
  tame Tate-algorithm route.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_coefficientObstruction_of_hasAdditiveReduction`
  Apply selected-equation minimality to rule out another pure weighted scaling while
  retaining all translation, blowup, and component steps as open work.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_hasAdditiveReduction_variableChange_of_valuation_u_eq_one`
  Keep the minimal additive branch stable under every integral valuation-unit coordinate
  change used by the residue-translation stage.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.tateAlgorithm_translatedCoefficientObstruction_of_hasAdditiveReduction`
  Rule out simultaneous integrality of all five exactly transformed coefficients after
  arbitrary translations and a scale of valuation below one.

:::

:::theorem "MT-PRIME-SPLIT-SEQUENCE" (parent := "prime_argument") (uses := "MT-PRIME-HERBRAND-KUMMER") (tags := "proof, done, integrated, mazur")
*Upgrade potentially good to good reduction at five.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 10 points.

*Summary:* Integral j excludes multiplicative reduction, while the checked marked
Tate-depth theorem excludes additive reduction; the exhaustive reduction trichotomy
therefore gives good reduction on the selected five-adic minimal equation.

*Canonical artifacts:*

* `theorem` (`integrated`): `MazurTorsion.PrimeOrder.goodReductionAtFive`
  Combine the checked multiplicative and weighted-depth additive exclusions; the
  rational finite-field and formal-immersion endpoints consume this theorem.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.valuation_j_gt_one_of_hasMultiplicativeReduction`
  Calculate that multiplicative reduction forces valuation of the j-invariant strictly
  above one.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.not_hasMultiplicativeReduction_of_valuation_j_le_one`
  Deduce that an integral j-invariant excludes the multiplicative branch.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction`
  Share the reduction trichotomy between residue characteristics five and eleven by
  isolating the additive branch as an exact-order obstruction.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive`
  Consume integral j, an actual tame additive filtration, and a marked large-prime-order
  point in the reduction-type trichotomy to prove good reduction.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive`
  Reduce a torsion point on a minimal completed equation with good reduction, transport
  it to ZMod 5, and consume the checked finite-field order bound.

:::

:::theorem "MT-PRIME-SHAFAREVICH" (parent := "prime_argument") (uses := "MT-BASE-INTEGRATED") (tags := "proof, done, integrated, mixed")
*The ten-point finite enumeration over F\_5.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `proof`; *backend:* `mixed`;
*risk:* `extreme`; *weight:* 15 points.

*Summary:* The checked exhaustive enumeration proves every elliptic curve over F₅ has at
most ten rational points.

*Canonical artifacts:*

* `theorem` (`integrated`): `MazurTorsion.PrimeOrder.card_reductionAtFive_le_ten`
  Normalize in characteristics other than two and three, then verify all 25 short models
  over F\_5.
* `theorem` (`integrated`):
  `MazurTorsion.PrimeOrder.zmod_five_addOrderOf_ne_of_eleven_le`
  Consume the finite enumeration to rule out every point whose exact additive order is
  at least eleven.

:::

:::theorem "MT-PRIME-ISOGENY-CHAIN" (parent := "prime_argument") (uses := "MT-PRIME-EISENSTEIN-SPECIALIZATION, MT-PRIME-DIVISION-FIELD, MT-PRIME-SPLIT-SEQUENCE, MT-PRIME-SHAFAREVICH") (tags := "proof, blocked, nouns-missing, mazur")
*Exclude order 11 and every prime order at least 17.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 10 points.

*Summary:* Join potential-good reduction from formal immersion, the checked additive
exclusion, prime-to-five exact-order specialization, and the ten-point enumeration to
exclude order 11 and every prime order at least 17.

*Canonical artifacts:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_eleven`
  Exclude exact rational order eleven by the formal-immersion-at-five argument.
* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_prime_ge_seventeen`
  Exclude every rational prime order at least seventeen by the same argument.

:::
