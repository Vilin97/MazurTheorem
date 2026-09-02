import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "02 — Finite-level endpoints" =>

:::group "finite_endpoints"
Close level 13 and orders 18, 25, 35, and 49; obtain order 11 from the uniform
formal-immersion route, reuse the same engine for squarefree level 35, and reduce order
49 directly to the checked X\_0(49) cusp classification. Stage weight: 100 points.
:::

:::theorem "MT-X11-COSET" (parent := "finite_endpoints") (uses := "MT-X11-JOIN") (tags := "proof, paused, compiled, mazur")
*The five-coset bound on X\_1(11).*

*Status:* `paused`; *readiness:* `compiled`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `high`; *weight:* 12 points.

*Summary:* The reverse X\_1(11) model-to-Tate bridge, its discriminant certificate, the
conditional cusp classification, and the conditional five-coset proof with Q=0 are
checked.

*Canonical artifacts:*

* `theorem` (`contract`): `MazurTorsion.Kubert.orderElevenModelOfRaw_inverse`
  The denominator-safe reverse rational functions are a checked inverse to the forward
  X\_1(11) model map on the noncusp locus.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.exists_elliptic_tate_marked_order_eleven_of_model`
  A noncusp model point reconstructs an actual elliptic Tate curve with a rational point
  of exact order eleven; nonzero discriminant follows from the checked degree-five
  resultant certificate.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.model_abscissa_eq_zero_or_one_of_no_order_eleven`
  Real consumer reducing rational X\_1(11) points to the two cusp abscissae from any
  uniform exact-order-eleven exclusion.
* `theorem` (`contract`): `MazurTorsion.XOneEleven.fiveCosetBound_of_no_order_eleven`
  The preferred route consumer enumerates the four affine cusp points plus infinity and
  proves FiveCosetBound with quotient point Q=0.
* `theorem` (`contract`): `MazurTorsion.XOneEleven.veluFiveMap_eq_zero_iff_five_nsmul`
  Fallback five-isogeny infrastructure: the candidate Velu point function has zero fibre
  exactly the points killed by five; no additivity or packaged isogeny is claimed.
* `theorem` (`contract`): `MazurTorsion.XOneEleven.exists_fifthPower_of_emptyFiveSelmer`
  Fallback arithmetic consumer: a rational unit with all finite valuation residues
  trivial modulo five is a fifth power; the local Kummer comparison and ramified factor
  remain open.

:::

:::theorem "MT-X11-JOIN" (parent := "finite_endpoints") (uses := "MT-PRIME-ISOGENY-CHAIN") (tags := "integration, blocked, statement-only, mazur")
*Expose the order-11 endpoint from the prime theorem.*

*Status:* `blocked`; *readiness:* `statement_only`; *kind:* `integration`; *backend:*
`mazur`; *risk:* `low`; *weight:* 2 points.

*Summary:* Adapt the formal-immersion order-11 theorem to the existing PointOrder
callback; the explicit X\_1(11) descent is no longer a logical prerequisite.

*Canonical artifacts:*

* `theorem` (`proposed`): `MazurTorsion.XOneEleven.rationalPoint_addOrderOf_ne_eleven`
  Expose the uniform order-eleven result under the finite-endpoint namespace expected by
  PointOrder.

:::

:::theorem "MT-X13-NONCUSP" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, paused, compiled, mazur")
*Classify the noncuspidal rational points on X\_1(13).*

*Status:* `paused`; *readiness:* `compiled`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 26 points.

*Summary:* Show that the explicit genus-two order-13 model has no rational affine point
with x different from 0 and -1.

*Canonical artifacts:*

* `theorem` (`contract`):
  `MazurTorsion.XOneThirteenDescent.positive_split_rational_curve_point`
  Dehomogenize every positive primitive split datum to an actual rational point on the
  order-thirteen sextic with its canonical positive integral ordinate.
* `theorem` (`contract`): `MazurTorsion.XOneThirteenDescent.homogeneous_pell_identity`
  Check the degree-38 homogeneous Pell identity for the explicit degree-19 and degree-16
  certificates.
* `theorem` (`contract`):
  `MazurTorsion.XOneThirteenDescent.odd_prime_pell_factor_allocation`
  Prove that the two positive Pell factors have no common odd prime and allocate each
  odd prime divisor of b to exactly one factor.
* `definition` (`contract`):
  `MazurTorsion.XOneThirteenDescent.PositivePellAllocatedFactorObstruction`
  Name the remaining global allocated-factor obstruction without claiming the unproved
  divisor-class elimination.
* `theorem` (`contract`):
  `MazurTorsion.XOneThirteenDescent.rationalPoint_addOrderOf_ne_thirteen_of_positivePellAllocatedFactor`
  Carry the honest allocated-factor boundary through the existing descent to the
  exact-order-thirteen consumer.
* `theorem` (`contract`):
  `MazurTorsion.XOneThirteenDescent.positive_pell_half_factors_isCoprime`
  Remove the forced scalar two and prove the resulting positive Pell factors coprime,
  including at the prime two.
* `theorem` (`contract`):
  `MazurTorsion.XOneThirteenDescent.positive_pell_factor_power_split`
  Use integer unique factorization to express the two halves as positive coprime
  thirty-eighth powers whose roots multiply to b.
* `definition` (`contract`):
  `MazurTorsion.XOneThirteenDescent.PositivePellPowerSplitObstruction`
  Name the fixed two-equation power-split cover left by the global Pell factorization.
* `theorem` (`contract`):
  `MazurTorsion.XOneThirteenDescent.rationalPoint_addOrderOf_ne_thirteen_of_positivePellPowerSplit`
  Consume the fixed-cover obstruction in the actual exact-order-thirteen exclusion path.

:::

:::theorem "MT-X18-NONCUSP" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, paused, compiled, mazur")
*Classify the noncuspidal rational points on the order-18 curve.*

*Status:* `paused`; *readiness:* `compiled`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `extreme`; *weight:* 18 points.

*Summary:* Show that the explicit genus-two order-18 model has no rational point with x
different from 0 and 1.

*Canonical artifacts:*

* `theorem` (`contract`):
  `MazurTorsion.XOneEighteenDescent.splitEisensteinThreePrime_not_common`
  Exclude simultaneous divisibility of the two split factors by the ramified prime above
  three using exact depth and the scalar-times-cube identity.
* `definition` (`contract`):
  `MazurTorsion.XOneEighteenDescent.TwoPrimeSupportedEisensteinIntegerFiniteSplitCyclicCubicObstruction`
  Expose the remaining finite Eisenstein obstruction after every common prime has been
  restricted to support above two.
* `theorem` (`contract`):
  `MazurTorsion.XOneEighteenDescent.rationalPoint_addOrderOf_ne_eighteen_of_twoPrimeSupportedEisensteinIntegerObstruction`
  Carry the narrowed support-only-over-two obstruction through the checked descent to
  the exact-order-18 exclusion.
* `theorem` (`contract`):
  `MazurTorsion.XOneEighteenDescent.antiDiagonalExceptionalPolynomial_ne_zero`
  Remove the exceptional denominator of the anti-diagonal quotient by complete
  projective enumeration modulo five.
* `theorem` (`contract`):
  `MazurTorsion.XOneEighteenDescent.antiDiagonalZ_sq_of_fourScalarCorrespondence`
  Map every surviving nondegenerate four-scalar cube correspondence to the explicit
  anti-diagonal genus-two curve.
* `theorem` (`contract`):
  `MazurTorsion.XOneEighteenFiniteField.card_pointCertificateF25`
  Enumerate fourteen affine points and two infinity directions over a checked
  transparent presentation of F\_25.
* `theorem` (`contract`):
  `MazurTorsion.XOneEighteenFiniteField.card_reducedDegreeTwoClassCertificateF5`
  Enumerate the 26 Frobenius-stable effective degree-two labels and collapse the
  six-member hyperelliptic pencil to obtain the expected 21 finite Jacobian classes.
* `theorem` (`contract`):
  `MazurTorsion.XOneEighteenFiniteField.finitePicard_card_eq_twentyOne_of_reducedDegreeTwoEquiv`
  Provide the named downstream consumer turning a future geometric finite-Picard
  equivalence into the sharp cardinality 21.

:::

:::theorem "MT-O25-EXCLUDE" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, paused, compiled, mathlib")
*Exclude exact rational order 25.*

*Status:* `paused`; *readiness:* `compiled`; *kind:* `proof`; *backend:* `mathlib`;
*risk:* `extreme`; *weight:* 16 points.

*Summary:* Prove that no rational point on an elliptic curve over Q has exact additive
order 25.

*Canonical artifacts:*

* `theorem` (`contract`): `MazurTorsion.Kubert.nsmul_origin_eq_successiveCoordinates`
  Compute (n+2)P by a reusable Tate recurrence under exactly the preceding nonzero
  abscissa hypotheses.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.tateSuccessiveX_ne_zero_of_marked_order_twentyFive`
  Deduce every secant denominator needed through 13P from exact order 25.
* `theorem` (`contract`): `MazurTorsion.Kubert.tateClearedCoordinates_spec`
  Represent the rational Tate recurrence by a division-free numerator-denominator
  recurrence with proved nonzero denominators.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.orderTwentyFiveRecurrenceEquation_eq_zero_of_marked_order`
  Derive the explicit rational-function collision x(13P)=x(12P) on Tate normal form.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.orderTwentyFiveClearedEquation_eq_zero_of_marked_order`
  Cross-multiply the 12P/13P collision to the fixed fraction-free X\_1(25) recurrence
  expression.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.exists_tateOrderTwentyFive_recurrence_certificate`
  Normalize an arbitrary exact-order-25 rational point to the recurrence locus while
  retaining all denominators and discriminant scale.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.orderTwentyFive_normalized_collision_factorization`
  Factor the fully normalized 12P/13P collision exactly as minus the cusp factor b-c
  times the explicit degree-40 noncuspidal polynomial.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.orderTwentyFiveNoncuspidalFactor_eq_zero_of_marked_order`
  Use exact marked order 25 and every checked denominator to reach the explicit
  noncuspidal factor with c and b-c nonzero.
* `theorem` (`contract`):
  `MazurTorsion.Kubert.exists_tateOrderTwentyFive_noncuspidal_certificate`
  Send an arbitrary exact-order-25 rational point to the fixed degree-40 model while
  retaining b, c, b-c, and the Tate-normalization discriminant scale.

:::

:::theorem "MT-O35-EXCLUDE" (parent := "finite_endpoints") (uses := "MT-X0-MODULI, MT-X0-CUSPS, MT-X0-EISENSTEIN-ALGEBRA, MT-NERON-SPECIALIZATION") (tags := "proof, paused, compiled, mathlib")
*Exclude exact order 35 with the shared formal-immersion engine.*

*Status:* `paused`; *readiness:* `compiled`; *kind:* `proof`; *backend:* `mathlib`;
*risk:* `extreme`; *weight:* 14 points.

*Summary:* Use the explicit optimal elliptic quotient X\_0(35)/w\_5 and Mazur's
squarefree-level formal-immersion criterion at auxiliary prime 11.

*Canonical artifacts:*

* `definition` (`proposed`): `MazurTorsion.OrderThirtyFive.optimalQuotient`
  Construct the explicit optimal quotient X\_0(35)/w\_5 with model y^2+y=x^3+x^2+9x+1.
* `theorem` (`proposed`):
  `MazurTorsion.OrderThirtyFive.optimalQuotient_mordellWeil_finite`
  Prove the quotient has rank zero and rational torsion Z/3 by a checked descent.
* `theorem` (`proposed`):
  `MazurTorsion.OrderThirtyFive.formalImmersionAtInfinity_modEleven`
  Instantiate the shared optimal-quotient formal immersion in characteristic eleven.
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.card_reductionAtEleven_le_eighteen`
  Normalize to short form and verify the 121 coefficient pairs over F\_11.
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.shortCurveEleven_addOrderOf_le_eighteen`
  Turn the enumerated short-model cardinality bound into a point-order bound.
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.shortCurveEleven_addOrderOf_ne_of_nineteen_le`
  Exclude every exact point order at least nineteen on an elliptic short model over
  F\_11.
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.zmod_eleven_addOrderOf_le_eighteen`
  Consume short-Weierstrass normalization to bound point order on every elliptic curve
  over F\_11.
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.zmod_eleven_addOrderOf_ne_of_nineteen_le`
  Uniformly exclude every exact order at least nineteen after arbitrary-model
  normalization.
* `theorem` (`proposed`): `MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_thirtyFive`
  Feed the local-at-eleven collision and finite-field bound to the published endpoint.

:::

:::theorem "MT-O49-TOWER" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, done, integrated, mazur")
*Exclude exact order 49 on the classified X\_0(49) correspondence.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `proof`; *backend:* `mazur`;
*risk:* `high`; *weight:* 10 points.

*Summary:* Exact order 49 is excluded by a fully checked explicit order-seven isogeny
tower.

*Canonical artifacts:*

* `theorem` (`contract`):
  `MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine_of_variableChangeClassifyingMap`
  Consume a noncuspidal classifying map from presentation-independent rational
  cyclic-subgroup data to the checked two-cusp X\_0(49) model.
* `theorem` (`contract`):
  `MazurTorsion.XZeroFortyNine.rationalDatumOfSplitFiniteFlatSourceOfOrderFortyNineTorsion`
  Construct the represented split finite-flat source from exact order 49 and prove that
  forgetting it recovers the original raw rational Gamma\_0 datum.
* `theorem` (`integrated`):
  `MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence3_checked`
  Check the final quintic/quartic pseudo-division recurrence through exact dense integer
  convolution identities.
* `theorem` (`integrated`):
  `MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.bounded_resultants_ne_zero`
  Use all seven checked recurrences and order-three parameter symmetry to make the three
  bounded resultants nonzero.
* `theorem` (`integrated`):
  `MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine`
  Exclude exact rational point order 49 through the explicit resultant obstruction and
  classified X\_0(49) correspondence.

:::

:::theorem "MT-FINITE-JOIN" (parent := "finite_endpoints") (uses := "MT-X11-JOIN, MT-X13-NONCUSP, MT-X18-NONCUSP, MT-O25-EXCLUDE, MT-O35-EXCLUDE, MT-O49-TOWER") (tags := "integration, blocked, statement-only, mazur")
*Assemble the genuinely exceptional finite levels.*

*Status:* `blocked`; *readiness:* `statement_only`; *kind:* `integration`; *backend:*
`mazur`; *risk:* `low`; *weight:* 2 points.

*Summary:* Remove the level-13 and exact-order 18, 25, 35, and 49 callbacks; order 11 is
already supplied by the uniform formal-immersion theorem.

*Canonical artifacts:*

* `theorem` (`proposed`):
  `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders_of_finite_endpoints`
  Combine order 11 from the prime route with level 13 and the four composite exclusions.

:::
