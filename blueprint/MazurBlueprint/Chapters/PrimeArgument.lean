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

The local algebraic endpoint already compiles:
`AlgebraicGeometry.IsFormalImmersionAt.spec_ext_of_stalkClosedPointTo`
separates arbitrary maps from a Noetherian local spectrum once their closed
points and restricted local homomorphisms agree. What remains here is to
construct the modular and cusp sections and prove that their quotient images
satisfy those hypotheses.

* `theorem` (`proposed`):
  `MazurTorsion.PrimeOrder.primeTorsion_potentiallyGoodReductionAtFive`
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

The abstract component/additive-residue/formal-kernel filtration now gives
the exact prime-order contradiction. Constructing it from the genuine Néron
special fibre remains open.
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
  `MazurTorsion.PrimeOrder.hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive`
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.completionPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive`

The valuation of `j` is now proved strictly greater than one under
multiplicative reduction, so integral `j` excludes that branch. Mathlib's
exhaustive reduction-type trichotomy and the checked tame-additive consumer
then prove good reduction. The completion-level consumer carries that same
marked point through the selected integral model, exact-order reduction, and
the residue-field equivalence to the checked `𝔽₅` contradiction. The modular
integral-`j` input, genuine Néron filtration, and global-to-local marked-point
and minimal-model transport are still required, so this node receives no
completion credit.
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
