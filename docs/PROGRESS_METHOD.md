# Progress and crowdsourcing methodology

## What the headline measures

The project reports two different numbers, both derived from
[`coordination/program.json`](../coordination/program.json):

- **Integrated completion: 17.2%.** This is 172 earned points out of the fixed
  1,000-point programme.
- **Ecosystem readiness: 18%.** This planning estimate also recognizes audited,
  compatible infrastructure outside the repository. It is not proof credit.

The canonical goal is the full group-structure theorem
`MazurTorsion.rationalTorsion_hasMazurClassification`. The immutable Lean Pool
`Challenge.Mazur.torsion_ncard_le` statement is tracked as a sibling corollary.
Finishing the numerical shortcut alone does not complete the classification
endpoint.

## Fixed accounting units

The denominator is 1,000 effort points:

| Stage | Points | Share |
|---|---:|---:|
| Integrated foundation | 50 | 5% |
| Remaining finite endpoints | 100 | 10% |
| Shared algebraic geometry and isogenies | 300 | 30% |
| Prime-level infrastructure | 400 | 40% |
| Mazur's prime-order argument | 100 | 10% |
| Integration and hardening | 50 | 5% |

The 48 top-level node IDs and their weights are permanent accounting
addresses. A reviewed route revision may change scope or dependencies, but it
must retain those IDs, weights, completion flags, and registered contracts;
record the revision; rebuild reciprocal edges; and keep the graph acyclic.

Schema-v4 `work_packages` are nonweighted execution subdivisions. Their
`weight_points` fields partition the owning node's existing weight and must
sum to it. They do not add to the denominator, cannot earn credit separately,
and do not make a parent node complete. Package status communicates execution
order and blockers only.

## Completion credit

Proof nodes receive:

- 0% for prose or a statement alone;
- 70% for an isolated kernel-checked proof;
- 85% after API review; and
- 100% only after the named downstream consumer compiles.

Infrastructure and upstream nodes receive:

- 0% for a proposed interface;
- 40% when the required definitions compile;
- 70% after mathematical and API checks; and
- 100% after a real downstream consumer compiles.

The ledger computes `earned_points` and `percent` from these rules. Line count,
commit count, elapsed time, issue closure, generated proof volume, and package
status are not completion evidence. A challenge declaration whose body remains
`:= sorry` contributes no proof credit.

Readiness is separate from completion. It records whether a node has only a
statement, still lacks foundational nouns, has a compiled boundary, or is
integrated. Claimability is separate again.

## Execution and claims

The `execution` object sets a work-in-progress limit of three packages and
currently selects two active lanes. Each selected lane has exactly one
`current_work_package` and a concrete exit criterion. An unused slot is not a
reason to select work whose prerequisite object does not exist. Other packages
marked `active` may be technically unblocked; they are not additional selected
WIP unless the execution plan names them.

Challenge lifecycle has these meanings:

- `open` with `claimable: true` permits one ordinary lease;
- `research_open` with `claimable: true` permits nonexclusive research
  intentions;
- `paused` requires `claimable: false`; its published contract remains
  immutable and compiled but receives no active maintainer proof volume; and
- `done` retains the contract as a checked bridge with `claimable: false`.

See [claiming guidance](CLAIMING.md) before starting work. Pausing is an
execution decision, not deletion, weakening, or completion of a contract.

## Evidence and audits

Credited work requires all applicable evidence:

- exact dependency pins and recorded provenance;
- a warning-free compiled declaration;
- no placeholders, custom axioms, unsafe escape hatches, or weakened checks;
- a named downstream consumer;
- an allowed-axiom audit;
- reciprocal, acyclic roadmap dependencies; and
- synchronized Blueprint and site projections.

The [code-quality policy](../.github/CODE_QUALITY.md) defines the repository
trust boundary. The [owner queue](../coordination/OWNER_QUEUE.md) is a compact
execution view only; it never overrides the ledger or awards progress.
