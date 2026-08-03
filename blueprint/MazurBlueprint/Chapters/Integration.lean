import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "06 — Integration and hardening" =>

:::group "integration"
Pin convergence, stable APIs, final assembly, kernel audit, and exposition.
Stage weight: 50 points.
:::

:::theorem "MT-PIN-MIGRATION" (parent := "integration") (uses := "MT-BASE-INTEGRATED") (tags := "integration, done, integrated, release") (priority := "high") (effort := "medium")
*Converge on a shared Mathlib and Tau Ceti pin.* The imported baseline and the
Tau Ceti contract workspace use one exact Lean toolchain and complete resolved
package-revision graph. The downstream aggregator builds under the contract-axiom,
Mathlib-linter, style, and repository source-policy gates.

*Status:* `done`.

*Canonical deliverables — these names are authoritative for this node:*

* `integration` (`integrated`): `MazurTheorem.Release.sharedDependencyGraph`
  Embed the exact root and Tau Ceti toolchains and manifests whose complete resolved
  package-revision graphs are checked for equality.
* `integration` (`integrated`): `MazurTheorem.Release.tauCetiConsumerBuild`
  Record the exact Tau Ceti downstream build and audit commands exercised by the
  permanent quality and CI gates.
:::

:::theorem "MT-API-INTEGRATION" (parent := "integration") (uses := "MT-FINITE-JOIN, MT-PRIME-ISOGENY-CHAIN, MT-PIN-MIGRATION") (tags := "integration, blocked, statement-only, mazur") (priority := "high") (effort := "medium")
*Integrate finite and formal-immersion prime APIs.* Expose one unconditional
statement saying that every rational torsion point has one of Mazur's allowed
orders, using the prime-five proof for order 11 and all primes at least 17.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders`
  Combine all finite endpoints and the prime-order theorem into an unconditional
  allowed-order result.
:::

:::theorem "MT-FINAL-ASSEMBLY" (parent := "integration") (uses := "MT-API-INTEGRATION") (tags := "integration, blocked, compiled, mazur") (priority := "high") (effort := "medium")
*Kernel-check Mazur's torsion bound.* Feed the unconditional point-order
theorem to the compiled cardinality reduction and prove that rational torsion
has cardinality at most 16.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `Challenge.Mazur.torsion_ncard_le`
  Prove the exact Lean Pool challenge statement that the rational torsion set has
  ncard at most 16.
:::

:::theorem "MT-EXPOSITION-AUDIT" (parent := "integration") (uses := "MT-FINAL-ASSEMBLY, MT-X11-COSET, MT-CYCLOTOMIC-UNRAMIFIED") (tags := "integration, blocked, statement-only, audit") (priority := "high") (effort := "medium")
*Final Challenge, exposition, provenance, and reproducibility audit.* Verify
every Blueprint arrow, close every retained Challenge (including the two
noncritical contracts named in the dependency metadata), reproduce the clean
build, and publish source and axiom reports.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `audit` (`proposed`): `MazurTheorem.Release.kernelAndProvenanceAudit`
  Record the final axiom report, exact source pins, declaration provenance, and
  reproducible build evidence.
* `integration` (`proposed`): `MazurTheorem.Release.allChallengesClosed`
  Verify that every registered Challenge is a checked bridge with no open contract.
* `integration` (`proposed`): `MazurTheorem.Release.versoBlueprint`
  Publish a Verso blueprint whose labels and mathematical dependency edges exactly
  match the canonical programme.
:::
