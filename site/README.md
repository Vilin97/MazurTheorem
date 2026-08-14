# Mazur Theorem coordination site

The public dashboard is a read-only projection of schema-v4
[`coordination/program.json`](../coordination/program.json). It presents the
fixed programme DAG, challenge boundaries, nonweighted work packages, current
execution lanes, and release endpoints without becoming a second source of
truth.

The canonical release endpoint is the full
`MazurTorsion.rationalTorsion_hasMazurClassification` theorem. The immutable
`Challenge.Mazur.torsion_ncard_le` contract appears as a sibling numerical
corollary, not as the definition of project completion.

## Data and navigation

`generated/program.json` must remain byte-identical to the canonical ledger.
Top-level nodes are the stable 1,000-point accounting units. Nested work
packages subdivide execution and earn no independent credit. The execution
object selects current packages under a WIP limit of three; it currently names
two honest lanes and leaves one slot unused. Other packages marked `active`
are ready rather than selected.

The main roadmap graph is the top-level mathematical DAG. Package and endpoint
views provide operational navigation without inventing new Blueprint nodes or
progress units. Paused challenge cards remain visible because their contracts
are immutable, but the ledger makes them unclaimable.

Related projections are the [Verso Blueprint](../blueprint/README.md), compact
[owner queue](../coordination/OWNER_QUEUE.md), and
[claiming guide](../docs/CLAIMING.md). Any disagreement is resolved in favor
of `coordination/program.json`.

## Local development

Node.js 22.13 or newer is required.

```bash
npm install
npm run dev
```

The production-compatible checks are:

```bash
npm run programme:check
npm run lint
npm test
```

Run `npm run programme:sync` after an authorized ledger change. Repository-wide
roadmap generation is available from the repository root:

```bash
python3 scripts/sync_roadmap_docs.py
python3 scripts/sync_roadmap_docs.py --check
```

The site has no database, authentication, or runtime mutation. Claims and
discussion happen in GitHub issues; accepted state changes are recorded in the
checked ledger.
