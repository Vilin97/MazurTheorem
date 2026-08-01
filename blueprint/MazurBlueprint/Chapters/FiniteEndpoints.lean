import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "02 — Finite-level endpoints" =>

:::group "finite_endpoints"
Close orders 18, 25, 35, and 49 and the separate prime levels 11 and 13.
Stage weight: 100 points.
:::

:::theorem "MT-X11-COSET" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, open, compiled, mazur") (priority := "high") (effort := "large")
*The five-coset bound on $`X_1(11)`.* Every rational point on
$`y^2+y=x^3-x^2` differs from one of the five multiples of $`(0,0)` by five
times a rational point.

*Status:* `open`; *scope:* exact compiled challenge contract. The target
declaration is `MazurTorsion.XOneEleven.fiveCosetBound`, with challenge bridge
`MazurTheorem.Challenge.xOneEleven_fiveCosetBound`; the existing consumer is
`MazurTorsion.XOneEleven.five_point_classification_of_cosetBound`.
:::

:::theorem "MT-X11-JOIN" (parent := "finite_endpoints") (uses := "MT-X11-COSET") (tags := "integration, blocked, statement-only, mazur") (priority := "high") (effort := "small")
*Exclude exact rational order 11.* Feed the five-coset classification through
the existing $`X_1(11)` reduction.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.XOneEleven.rationalPoint_addOrderOf_ne_eleven`
  Consume the five-coset contract and the existing $`X_1(11)` reduction to exclude
  exact rational order 11.
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

:::theorem "MT-O35-EXCLUDE" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, research-open, compiled, mazur") (priority := "high") (effort := "large")
*Exclude exact rational order 35.* No rational point on an elliptic curve
over $`\mathbb{Q}` has exact additive order 35.

*Status:* `research_open`; *scope:* exact compiled challenge contract. The
destination theorem is
`MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_thirtyFive`, bridged by
`MazurTheorem.Challenge.no_rational_point_of_order_thirtyFive`.
:::

:::theorem "MT-O49-TOWER" (parent := "finite_endpoints") (uses := "MT-BASE-INTEGRATED") (tags := "proof, open, compiled, mazur") (priority := "high") (effort := "large")
*Bridge exact order 49 to the $`X_0(49)` correspondence.* An exact rational
order-49 point produces a noncuspidal point of the already classified
level-seven correspondence, a contradiction.

*Status:* `open`; *scope:* exact compiled challenge contract. The
destination is
`MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine`, bridged by
`MazurTheorem.Challenge.no_rational_point_of_order_fortyNine`. Existing
transfer and rank-zero APIs live under `MazurTorsion.NumberTheory`.
:::

:::theorem "MT-FINITE-JOIN" (parent := "finite_endpoints") (uses := "MT-X11-JOIN, MT-X13-NONCUSP, MT-X18-NONCUSP, MT-O25-EXCLUDE, MT-O35-EXCLUDE, MT-O49-TOWER") (tags := "integration, blocked, statement-only, mazur") (priority := "high") (effort := "medium")
*Assemble all finite-level exclusions.* Remove the four composite callbacks
and the separate 11- and 13-level callbacks from the point-order theorem.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders_of_finite_endpoints`
  Combine the exact order 11, 13, 18, 25, 35, and 49 exclusions into the finite-
  endpoint point-order API.
:::
