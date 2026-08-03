import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "02 — Finite-level endpoints" =>

:::group "finite_endpoints"
Close level 13 and orders 18, 25, 35, and 49. Order 11 comes from the
uniform formal-immersion theorem; the inherited five-coset Challenge is then
discharged from the resulting cusp classification. Stage weight: 100 points.
:::

:::theorem "MT-X11-COSET" (parent := "finite_endpoints") (uses := "MT-X11-JOIN") (tags := "proof, open, compiled, mazur") (priority := "high") (effort := "medium")
*The five-coset bound on $`X_1(11)`.* Every rational point on
$`y^2+y=x^3-x^2` differs from one of the five multiples of $`(0,0)` by five
times a rational point.

*Status:* `open`; *scope:* exact compiled challenge contract. The target
declaration is `MazurTorsion.XOneEleven.fiveCosetBound`, with challenge bridge
`MazurTheorem.Challenge.xOneEleven_fiveCosetBound`; the existing consumer is
`MazurTorsion.XOneEleven.five_point_classification_of_cosetBound`.  The
preferred route is now to prove the reverse $`X_1(11)` model bridge, use the
order-11 theorem to classify all rational points as the five cusps, and take
$`Q=0` in the coset statement.  The prepared five-isogeny Selmer computation
remains a valid independent proof.
:::

:::theorem "MT-X11-JOIN" (parent := "finite_endpoints") (uses := "MT-PRIME-ISOGENY-CHAIN") (tags := "integration, blocked, statement-only, mazur") (priority := "high") (effort := "small")
*Expose the order-11 endpoint from the prime theorem.* Adapt the uniform
formal-immersion result to the namespace expected by PointOrder.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.XOneEleven.rationalPoint_addOrderOf_ne_eleven`
  Expose the formal-immersion order-eleven theorem through the existing endpoint API.
:::

:::theorem "MT-X13-NONCUSP" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, research-open, compiled, mazur") (priority := "high") (effort := "large")
*Classify the noncuspidal rational points on $`X_1(13)`.* If rational
$`x,y` satisfy the explicit order-13 sextic equation, then $`x=0` or $`x=-1`.

*Status:* `research_open`; *scope:* exact compiled challenge contract. The
destination is `MazurTorsion.XOneThirteenDescent.no_noncuspidal_point`; the
challenge name is `MazurTheorem.Challenge.xOneThirteen_no_noncuspidal_point`.
The prepared nouns are the Kubert sextic, Pell certificate, and genus-two
descent data in `MazurTorsion.NumberTheory.XOneThirteenDescent`.
:::

:::theorem "MT-X18-NONCUSP" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, research-open, compiled, mazur") (priority := "high") (effort := "large")
*Classify the noncuspidal rational points on the order-18 curve.* If rational
$`x,y` satisfy the explicit order-18 sextic equation, then $`x=0` or $`x=1`.

*Status:* `research_open`; *scope:* exact compiled challenge contract. The
destination is `MazurTorsion.XOneEighteenDescent.no_noncuspidal_point`; the
challenge name is `MazurTheorem.Challenge.xOneEighteen_no_noncuspidal_point`.
The proposed proof finishes the Eisenstein-integer descent already exposed by
the module.
:::

:::theorem "MT-O25-EXCLUDE" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, research-open, compiled, mazur") (priority := "high") (effort := "large")
*Exclude exact rational order 25.* No rational point on an elliptic curve
over $`\mathbb{Q}` has exact additive order 25.

*Status:* `research_open`; *scope:* exact compiled challenge contract. The
destination theorem is
`MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_twentyFive`, bridged by
`MazurTheorem.Challenge.no_rational_point_of_order_twentyFive`.
:::

:::theorem "MT-O35-EXCLUDE" (parent := "finite_endpoints") (uses := "MT-X0-MODULI, MT-X0-CUSPS, MT-X0-EISENSTEIN-ALGEBRA, MT-NERON-COMPONENTS, MT-NERON-SPECIALIZATION") (tags := "proof, research-open, compiled, mazur, formal-immersion") (priority := "high") (effort := "medium")
*Exclude exact order 35 with the shared formal-immersion engine.* Use the
rank-zero optimal quotient $`X_0(35)/w_5` at auxiliary prime eleven.  Tame
specialization and $`\#E(\mathbb F_{11})\le18` then contradict exact order
35.

*Status:* `research_open`; *scope:* exact compiled challenge contract. The
destination theorem is
`MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_thirtyFive`, bridged by
`MazurTheorem.Challenge.no_rational_point_of_order_thirtyFive`.

* `definition` (`proposed`):
  `MazurTorsion.OrderThirtyFive.optimalQuotient`
* `theorem` (`proposed`):
  `MazurTorsion.OrderThirtyFive.optimalQuotient_mordellWeil_finite`
* `theorem` (`proposed`):
  `MazurTorsion.OrderThirtyFive.formalImmersionAtInfinity_modEleven`
* `theorem` (`proposed`):
  `MazurTorsion.OrderThirtyFive.card_reductionAtEleven_le_eighteen`
* `theorem` (`proposed`):
  `MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_thirtyFive`
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.targetCubicFibreRoots_iff_targetThreeCandidateSurjective`
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.targetEisensteinUnitCover_no_nonzero_integer_solution`
* `definition` (`contract`):
  `MazurTorsion.OrderThirtyFive.TargetEisensteinAssociatedCube`
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.optimalQuotientModel_rank_zero_of_associatedCube`
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.targetEisensteinAssociatedCube`
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.optimalQuotientModel_rank_zero`
* `theorem` (`contract`):
  `MazurTorsion.OrderThirtyFive.optimalQuotientModel_finite`

The fixed equation, its rational torsion subgroup, an equation-checked Vélu
point-function candidate and its zero fibre, and trivial torsion on the
candidate target are checked. The opposite point-function candidate is total
on rational points, and its composite with the first candidate is checked to
be multiplication by three. The rational three-cover and visible-coset
translations compile through conditional rank-zero and finiteness consumers.
The source cube-class bound is now checked by a reduced
numerator-denominator and gcd-at-seven calculation. The target cyclic cubic
fibre is proved equivalent to surjectivity. Denominator clearing, the
Eisenstein norm factorization, all six unit classes, both nontrivial
mod-seven infinite descents, and the trivial-unit rational fibre root now
feed a compiled end-to-end rank-zero consumer. The associated-cube boundary is
now the existential normalized integral-data witness actually used by that
consumer, and the nonsplit common-prime ideal-support calculation at `2`, `3`,
and `5` supplies it unconditionally. Thus the fixed explicit curve model has
checked rank zero and a finite rational point group. Its identification with
the actual modular quotient, the classifying map, formal immersion, and the
geometric bad-fibre specialization remain open, so this is not node
completion.
:::

:::theorem "MT-O49-TOWER" (parent := "finite_endpoints") (uses := "MT-X0-MODULI") (tags := "proof, open, compiled, mazur") (priority := "high") (effort := "small")
*Bridge exact order 49 directly to the classified $`X_0(49)` curve.* The
generated cyclic subgroup gives a noncuspidal rational modular point, while
the checked rank-zero model has only its two cusps.

*Status:* `open`; *scope:* exact compiled challenge contract. The
destination is
`MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine`, bridged by
`MazurTheorem.Challenge.no_rational_point_of_order_fortyNine`. The public
$`X_0(49)` two-cusp classification already compiles.  The preferred bridge
uses the generic cyclic-subgroup moduli point and does not require additivity
of the explicit Vélu point function or a nonbacktracking isogeny tower. The
raw datum is now quotiented by checked admissible Weierstrass changes, and the
presentation-independent endpoint
`MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine_of_variableChangeClassifyingMap`
compiles. Constructing the coarse classifying map, its noncuspidality, and the
target identification remains the open Challenge.

* `theorem` (`contract`):
  `MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine_of_variableChangeClassifyingMap`
:::

:::theorem "MT-FINITE-JOIN" (parent := "finite_endpoints") (uses := "MT-X11-JOIN, MT-X13-NONCUSP, MT-X18-NONCUSP, MT-O25-EXCLUDE, MT-O35-EXCLUDE, MT-O49-TOWER") (tags := "integration, blocked, statement-only, mazur") (priority := "high") (effort := "medium")
*Assemble the genuinely exceptional finite levels.* Remove the level-13 and
four composite callbacks; order 11 has already been supplied by the prime
route.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders_of_finite_endpoints`
  Combine order 11 from the prime route with level 13 and the four composite
  exclusions.
:::
