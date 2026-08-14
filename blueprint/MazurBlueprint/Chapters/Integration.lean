import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "06 — Integration and hardening" =>

:::group "integration"
Assemble allowed point orders with Mordell–Weil finiteness and finite-abelian shape to
prove the full fifteen-group classification, then derive the ncard challenge and audit
the release. Stage weight: 50 points.
:::

:::theorem "MT-PIN-MIGRATION" (parent := "integration") (uses := "MT-BASE-INTEGRATED") (tags := "integration, done, integrated, mixed")
*Converge on a shared Mathlib and Tau Ceti pin.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `integration`; *backend:* `mixed`;
*risk:* `high`; *weight:* 20 points.

*Summary:* The root and Tau Ceti contract workspaces use one exact Lean toolchain and
complete resolved package-revision graph.

*Canonical artifacts:*

* `integration` (`integrated`): `MazurTheorem.Release.sharedDependencyGraph`
  Embed the exact root and Tau Ceti toolchains and manifests whose complete resolved
  package-revision graphs are checked for equality.
* `integration` (`integrated`): `MazurTheorem.Release.tauCetiConsumerBuild`
  Record the exact Tau Ceti downstream build and audit commands exercised by the
  permanent quality and CI gates.

:::

:::theorem "MT-API-INTEGRATION" (parent := "integration") (uses := "MT-FINITE-JOIN, MT-PRIME-ISOGENY-CHAIN, MT-PIN-MIGRATION") (tags := "integration, blocked, statement-only, mazur")
*Integrate finite and formal-immersion prime APIs.*

*Status:* `blocked`; *readiness:* `statement_only`; *kind:* `integration`; *backend:*
`mazur`; *risk:* `medium`; *weight:* 10 points.

*Summary:* Expose one unconditional theorem that every rational torsion point has an
allowed order, using the formal-immersion theorem for 11 and primes at least 17.

*Canonical artifacts:*

* `theorem` (`proposed`): `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders`
  Combine the exceptional finite endpoints and the formal-immersion prime theorem.

:::

:::theorem "MT-FINAL-ASSEMBLY" (parent := "integration") (uses := "MT-API-INTEGRATION") (tags := "integration, blocked, compiled, mazur")
*Kernel-check Mazur's full torsion classification.*

*Status:* `blocked`; *readiness:* `compiled`; *kind:* `integration`; *backend:* `mazur`;
*risk:* `low`; *weight:* 15 points.

*Summary:* Prove rational torsion finite, obtain its rank-two invariant-factor
presentation, combine that input with the unconditional point-order theorem and the
checked forbidden subgroup results, and conclude the fifteen-group classification.

*Canonical artifacts:*

* `theorem` (`proposed`): `MazurTorsion.rationalTorsion_finite`
  Supply the Mordell–Weil finiteness input deliberately omitted from the literal ncard
  challenge.
* `theorem` (`proposed`): `MazurTorsion.rationalTorsion_hasRankTwoPresentation`
  Put the finite rational torsion group into the two-invariant-factor form used by the
  checked classification theorem.
* `theorem` (`proposed`): `MazurTorsion.rationalTorsion_hasMazurClassification`
  Classify the rational torsion subgroup up to group isomorphism as one of Mazur's
  fifteen groups.
* `theorem` (`proposed`): `Challenge.Mazur.torsion_ncard_le`
  Derive the immutable Lean Pool ncard-at-most-16 statement from the full
  classification.

:::

:::theorem "MT-EXPOSITION-AUDIT" (parent := "integration") (uses := "MT-FINAL-ASSEMBLY, MT-X11-COSET, MT-CYCLOTOMIC-UNRAMIFIED") (tags := "integration, blocked, statement-only, mixed")
*Final challenge, exposition, provenance, and reproducibility audit.*

*Status:* `blocked`; *readiness:* `statement_only`; *kind:* `integration`; *backend:*
`mixed`; *risk:* `low`; *weight:* 5 points.

*Summary:* Verify every blueprint edge, close every retained Challenge including the
now-noncritical X\_1(11) and cyclotomic contracts, reproduce the clean build, and
publish the final axiom and source audit.

*Canonical artifacts:*

* `audit` (`proposed`): `MazurTheorem.Release.kernelAndProvenanceAudit`
  Record the final axiom report, exact source pins, declaration provenance, and
  reproducible build evidence.
* `integration` (`proposed`): `MazurTheorem.Release.allChallengesClosed`
  Verify that every registered Challenge is a checked bridge with no open contract.
* `integration` (`proposed`): `MazurTheorem.Release.versoBlueprint`
  Publish a Verso blueprint exactly matching the formal-immersion dependency graph.

:::
