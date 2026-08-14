import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "01 — Integrated baseline" =>

:::group "integrated_baseline"
The imported sorry-free finite-group reduction, arithmetic foundations, and seven
completed exceptional orders, together with checked rational height-descent foundations.
Stage weight: 50 points.
:::

:::theorem "MT-BASE-INTEGRATED" (parent := "integrated_baseline") (tags := "milestone, done, integrated, mazur")
*Imported sorry-free Mazur baseline.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `milestone`; *backend:* `mazur`;
*risk:* `low`; *weight:* 50 points.

*Summary:* Finite-group classification and cardinality assembly; direct rational-torsion
finiteness; the generic finite-abelian rank-two presentation; full 2-, 3-, 4-, 5-, and
7-torsion obstructions; exceptional products; and unconditional exclusions of orders 14,
15, 16, 20, 21, 24, and 27.

*Canonical artifacts:*

* `definition` (`integrated`): `MazurTorsion.RationalTorsion`
  The rational torsion subgroup on which the point-order and cardinality reductions are
  stated.
* `definition` (`integrated`): `MazurTorsion.cyclicOrders`
  The finite set of cyclic point orders allowed by the target classification.
* `definition` (`integrated`): `MazurTorsion.remainingKubertForbiddenOrders`
  The exact residual composite-order callbacks exposed by the imported baseline.
* `theorem` (`integrated`):
  `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders_of_remaining_obstructions`
  The checked point-order reduction from the remaining prime and composite exclusions.
* `theorem` (`integrated`): `MazurTorsion.torsion_ncard_le_of_explicit_arithmetic`
  The checked cardinality bound once the explicit point-order hypotheses are supplied.
* `theorem` (`integrated`): `WeierstrassCurve.Affine.approx_parallelogram_law`
  The checked naïve-height estimate consumed by Mathlib's direct finite-torsion descent
  theorem.
* `definition` (`integrated`): `MazurTorsion.rationalLogHeightNorthcott`
  Northcott's property for rational logarithmic height, completing the direct
  torsion-finiteness input without finite generation.
* `theorem` (`integrated`): `MazurTorsion.rationalTorsion_finite`
  Apply rational Northcott and the approximate parallelogram law to Mathlib's
  finite-torsion descent theorem, without full Mordell–Weil finite generation.
* `theorem` (`integrated`):
  `MazurTorsion.exists_rankTwoPresentation_of_allowed_orders_and_forbidden`
  Put any finite abelian group satisfying the allowed-order hypothesis and exactly
  c2Cube, c3Square, c5Square, and c7Square into rank-two invariant-factor form;
  c4Square, c2c10, and c2c12 remain classification-only.

:::
