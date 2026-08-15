# Claiming work

[`coordination/program.json`](../coordination/program.json) is canonical for
challenge status, claimability, dependencies, work packages, and execution
selection. The site, Blueprint, issue forms, and this page are navigation aids;
they do not create claims or change programme state.

## Before claiming

Check the node's `challenge` object in the ledger:

- `open` with `claimable: true` permits one ordinary claim;
- `research_open` with `claimable: true` permits nonexclusive research
  intentions;
- `paused` is always unclaimable, although its published contract remains
  immutable and compiled; and
- `done` is retained as a checked bridge and is not claimable.

The execution plan separately selects two maintainer work packages under a WIP
limit of three. Each active lane names one `current_work_package`; an unused
slot is not filled with work whose prerequisite object is missing. Another
package may have status `active` because its prerequisites are ready; that does
not reserve it or increase the WIP limit. Work packages divide delivery into
reviewable steps and carry zero independent progress credit.

## Ordinary claims

Open the repository's **Claim a work package** issue form. A normal claim:

- lasts 14 days;
- needs a public progress note at least once every 7 days;
- may be extended when concrete progress is visible; and
- may be released at any time without stigma.

Maintainers may release a silent claim so another contributor is not blocked.
A claim never authorizes changing the contract's mathematical meaning, stable
node ID, weight, or registered destination.

## Research intentions

`research_open` work can have multiple teams. Use the **Register a research
approach** issue form. A research intention reserves no namespace and does not
exclude independent approaches. Share negative results, interface discoveries,
and source references early.

## Foundational interfaces

For a node whose readiness is `nouns_missing`, or whose status is `blocked` or
`planned`, open a design issue before proof-heavy implementation. Include:

- the named consumer motivating the API;
- proposed exact Lean signatures;
- the upstream destination and dependency pin;
- small sanity examples; and
- what the interface deliberately does not promise.

A new interface receives no integration credit until its exact boundary is
recorded and a real named consumer compiles.

## Closing a claim

A claim closes only when the pull request compiles the registered declaration
and consumer, passes source and axiom gates, records provenance, and updates the
ledger lifecycle without weakening the task. Challenge implementations belong
in checked library modules; the immutable challenge then becomes a one-line
checked bridge.

See the compact [owner queue](../coordination/OWNER_QUEUE.md) for current
selection and the [progress method](PROGRESS_METHOD.md) for credit rules.
