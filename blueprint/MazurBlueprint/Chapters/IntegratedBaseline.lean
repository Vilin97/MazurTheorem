import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "01 — Integrated baseline" =>

:::group "integrated_baseline"
The sorry-free finite-group reduction, arithmetic foundations, and seven completed
exceptional orders imported from Clawristotle. Stage weight: 50 points.
:::

:::theorem "MT-BASE-INTEGRATED" (parent := "integrated_baseline") (tags := "milestone, done, integrated, mazur")
*Imported sorry-free Mazur baseline.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `milestone`; *backend:* `mazur`;
*risk:* `low`; *weight:* 50 points.

*Summary:* Finite-group classification and cardinality assembly; full 2-, 3-, 4-, 5-,
and 7-torsion obstructions; exceptional products; and unconditional exclusions of orders
14, 15, 16, 20, 21, 24, and 27.

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

:::
