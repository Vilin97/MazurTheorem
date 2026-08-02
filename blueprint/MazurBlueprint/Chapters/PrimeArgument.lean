import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "05 — Mazur's prime-order argument" =>

:::group "prime_argument"
The specialization, unramified-extension, splitting, and isogeny-chain
argument for primes at least 17. Stage weight: 100 points.
:::

:::theorem "MT-PRIME-SEMISTABLE" (parent := "prime_argument") (uses := "MT-NERON-SPECIALIZATION, MT-FFGS-OORT-RAYNAUD") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*Prime torsion forces semistability.* For a prime $`p\ge 17`, finite-flat
uniqueness and Néron-model specialization exclude additive reduction of an
elliptic curve carrying a rational point of order $`p`.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.primeTorsion_semistable`
  Prove that a rational point of prime order p at least 17 forces semistable
  reduction.
:::

:::theorem "MT-PRIME-OUTSIDE-IDENTITY" (parent := "prime_argument") (uses := "MT-PRIME-SEMISTABLE") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*Torsion specializes outside identity components.* Hasse bounds and component
groups place the marked point outside the identity component at 2, 3, and all
bad primes.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.primeTorsion_specializesOutsideIdentity`
  Use Hasse bounds and component groups to locate the marked point outside the
  relevant identity components.
:::

:::theorem "MT-PRIME-EISENSTEIN-SPECIALIZATION" (parent := "prime_argument") (uses := "MT-PRIME-OUTSIDE-IDENTITY, MT-X0-EISENSTEIN-QUOTIENT") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*Specialize through the Eisenstein quotient.* Map the integral $`X_0(p)`
point to the Eisenstein quotient and compare its specializations in two
residue characteristics.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.eisenstein_specialization_comparison`
  Compare the two specializations of the integral modular point after mapping to the
  Eisenstein quotient.
:::

:::theorem "MT-PRIME-DIVISION-FIELD" (parent := "prime_argument") (uses := "MT-PRIME-EISENSTEIN-SPECIALIZATION, MT-CYCLOTOMIC-UNRAMIFIED") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*The division-field extension is everywhere unramified.* The comparison
constructs the x-coordinate $`p`-division-field datum attached to the rational
prime-order point and forces its inverse-cyclotomic extension over
$`\mathbb{Q}(\zeta_p)` to be unramified at every finite place.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `MazurTorsion.PrimeOrder.DivisionFieldData`
  Tie the inverse-cyclotomic extension to a rational point of exact order p and
  the splitting field of its x-coordinate p-division polynomial.
* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.divisionField_everywhereUnramified`
  Prove that the p-division field extension over the p-th cyclotomic field is
  everywhere unramified.
:::

:::theorem "MT-PRIME-HERBRAND-KUMMER" (parent := "prime_argument") (uses := "MT-PRIME-DIVISION-FIELD") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*Exclude the inverse-cyclotomic extension.* The Herbrand–Kummer calculation
and $`B_2=1/6` rule out the unramified character extension demanded by the
division field.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.inverseCyclotomic_extension_impossible`
  Apply the Herbrand-Kummer calculation to rule out the required inverse-cyclotomic
  extension.
:::

:::theorem "MT-PRIME-SPLIT-SEQUENCE" (parent := "prime_argument") (uses := "MT-PRIME-HERBRAND-KUMMER, MT-EC-ISOGENY-WEIL") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*Split the $`p`-torsion extension.* Split
$`0\to\mathbb{Z}/p\mathbb{Z}\to E[p]\to\mu_p\to0` after the forbidden
character extension has been excluded.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.primeTorsion_exactSequence_split`
  Split the exact sequence from the rational p-torsion line to its cyclotomic
  quotient.
:::

:::theorem "MT-PRIME-SHAFAREVICH" (parent := "prime_argument") (uses := "MT-TC-E1-JACOBIAN-VARIETY, MT-EC-ISOGENY-WEIL") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*Shafarevich finiteness for the isogeny chain.* Only finitely many rational
elliptic curves up to isomorphism have good reduction outside a prescribed
finite set, in the exact form consumed by quotient iteration.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.Shafarevich.finiteIsomorphismClasses`
  Give the finiteness theorem for elliptic curves with a prescribed finite set of bad
  primes.
:::

:::theorem "MT-PRIME-ISOGENY-CHAIN" (parent := "prime_argument") (uses := "MT-PRIME-SPLIT-SEQUENCE, MT-PRIME-SHAFAREVICH") (tags := "proof, blocked, nouns-missing, prime-argument") (priority := "high") (effort := "large")
*The infinite isogeny-chain contradiction.* Iterate quotient isogenies by
the split rational subgroup; Shafarevich finiteness contradicts the resulting
infinite sequence, excluding rational prime order $`p\ge17`.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.PrimeOrder.rationalPoint_addOrderOf_ne_prime_ge_seventeen`
  Exclude every rational point of prime order p at least 17 by the quotient-isogeny
  chain contradiction.
:::
