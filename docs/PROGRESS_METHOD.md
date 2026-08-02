# Progress and crowdsourcing methodology

## The two headline numbers

The project reports two deliberately different percentages:

- **Integrated completion** is the weighted fraction of the final theorem
  whose named acceptance consumers compile in this repository.
- **Ecosystem readiness** is a planning estimate that also credits compatible
  reusable infrastructure already present in Mathlib, Lean Pool, Tau Ceti,
  FLT, and other audited repositories.

At launch these are **5% integrated** and approximately **12%
ecosystem-ready**. The second number is not a proof-progress claim.

The August 2026 audit of AINTLIB's modular-curve branch identifies roughly
50--75 effort points of plausibly reusable material after pin convergence,
license review, transitive axiom checks, and adapter work. Those points overlap
infrastructure already represented in the 12% ecosystem estimate, so they are
not added a second time. AINTLIB contributes **0 integrated points** until a
named consumer in this repository compiles against an accepted extraction.

## Weighted denominator

The denominator is 1,000 effort points, where one point is 0.1% of the
estimated total effort:

| Stage | Points | Share |
|---|---:|---:|
| Integrated foundation | 50 | 5% |
| Remaining finite endpoints | 100 | 10% |
| Shared algebraic geometry and elliptic-curve infrastructure | 300 | 30% |
| Prime-level infrastructure | 400 | 40% |
| Mazur's prime theorem | 100 | 10% |
| Integration and hardening | 50 | 5% |

The ledger and dependency graph live in
[`coordination/program.json`](../coordination/program.json). Node identifiers
are immutable and all weights must sum to 1,000. Changes to the denominator
need a public design issue and must explain what new scope was discovered.

## Route revisions and immutable ledger addresses

Node identifiers are permanent accounting addresses, not promises that one
particular proof strategy will remain optimal forever. A mathematical route
may be replaced when a documented literature and API audit finds a strictly
smaller checked dependency cone. Such a migration must:

- add a dated top-level `route_revision` record;
- retain every public node ID, weight, completion flag, and registered
  Challenge;
- record the former role and the replacement role in `route_history` on each
  repurposed node;
- rebuild reciprocal dependency edges and prove that the graph remains
  acyclic;
- award no completion credit for prose, rejected work, or a renamed node; and
- identify a concrete downstream consumer for every proposed public API.

A Challenge may cease to be theorem-critical without ceasing to be a release
obligation. In that case it stays in the ledger with its immutable contract,
and the final exposition/audit node depends on it even though the mathematical
theorem path does not. This distinction prevents historical contributor
contracts from forcing a needlessly difficult proof route while ensuring that
none is silently deleted or declared solved.

The `formal-immersion-at-five-v1` revision follows this policy. It changes no
denominator or completion number: all 48 node IDs and all 1,000 points remain,
with the obsolete prime-argument addresses assigned to the successive checked
steps of Mazur's 1978 formal-immersion proof.

This is an engineering estimate, not a theorem. High-risk nodes can vary by a
factor of two or more. The weights are most useful for preventing tiny final
lemmas or large generated files from distorting the picture.

## Completion credit

Proof nodes receive:

- 0% when only prose or a statement exists;
- 70% when an isolated proof is kernel-checked;
- 85% when its public API is accepted;
- 100% when the named downstream consumer compiles.

Infrastructure nodes receive:

- 0% for a prose-only design;
- up to 40% when definitions compile;
- up to 70% when acceptance tests pass;
- 100% after a real downstream consumer uses the API.

The launch ledger uses only 0% or 100% completion to keep the headline
conservative. A challenge declaration containing `sorry` always contributes
0%.

Readiness is tracked separately:

- `nouns_missing`;
- `statement_only`;
- `compiled`;
- `integrated`.

Readiness makes bottlenecks visible without inflating theorem completion.
Claimability is a separate boolean contract: a compiled statement can be open
for a normal lease, open for parallel research, or held back until its
interfaces are reviewed.

## What can be crowdsourced?

There are three distinct questions:

1. **Can a task be stated with today's APIs?** At launch, exact compiled
   contracts expose 11.3% of the weighted work: 3.9% ordinary claimable and
   7.4% research-open.
2. **Can it be parallelized after an interface is reviewed?** Roughly 35–45%
   in total—including the 11.3% above—can become bounded work packages.
3. **Can it be done by independent contributors without continuous
   coordination?** Not for the core prime-level proof. Approximately 45–55%
   remains tightly coupled research and integration.

So “most of the theorem cannot be crowdsourced” is accurate if
“crowdsourced” means unrelated proof bounties posted today. It is too
pessimistic if it includes coordinated teams working against reviewed
interfaces and upstream libraries.

Poincaré-style roadmapping is valuable because it exposes prerequisites,
ownership, and interfaces. It does not by itself make missing mathematical
nouns exist. This project therefore publishes exact claimable declarations
only when they compile, while keeping later nodes as research work packages.

## Evidence and audits

Completion requires all of:

- an exact dependency pin;
- a warning-free compiled declaration;
- no custom axioms;
- no placeholders or unsafe escape hatches;
- a named consumer;
- provenance and source recorded;
- generated roadmap and documentation checks passing.

Line count, elapsed time, number of commits, AI generation, and visual graph
coverage are not completion evidence.
