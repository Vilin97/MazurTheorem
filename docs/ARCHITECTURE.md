# Architecture

The repository separates checked mathematics, immutable contracts, programme
coordination, and public projections.

```text
Mathlib / Tau Ceti / attributed exact-pin ports
                         |
                         v
               MazurTorsion checked library
                         |
              named consumer declarations
                         |
          +--------------+---------------+
          v                              v
HasMazurClassification             Lean Pool ncard
canonical release theorem          challenge corollary

Challenge/                 immutable published contracts
coordination/program.json  canonical weighted and execution DAG
blueprint/                 generated mathematical projection
site/                      generated public coordination projection
upstream/tauceti/          same pins, separate upstream contracts
```

The canonical release theorem is
`MazurTorsion.rationalTorsion_hasMazurClassification`: the rational torsion
group is isomorphic to one of Mazur's fifteen groups. The immutable
`Challenge.Mazur.torsion_ncard_le` statement is a sibling release endpoint and
a numerical corollary. Its finite/infinite `Set.ncard` shortcut is useful, but
it is not the project definition of Mazur's theorem.

## Canonical objects

[`coordination/program.json`](../coordination/program.json) is the sole source
of truth for stable node IDs, weights, dependencies, completion, challenge
lifecycle, work packages, the three active execution lanes, and release
endpoints. Top-level nodes are the permanent 1,000-point accounting units.
Nested work packages divide delivery into reviewable steps but earn no
independent progress credit.

Checked implementation never imports `Challenge`. A challenge imports only
what is needed to state its contract. When solved, its permanent implementation
lives in `MazurTorsion/` and the challenge becomes a one-line checked bridge.
Published contract identity and meaning remain immutable even when a contract
is paused and made unclaimable.

## Canonical and provisional mathematical objects

Object maturity is part of the proof boundary:

1. A **canonical constructed object** is the actual scheme, morphism, group
   object, or theorem, with its laws proved.
2. A **canonical interface over a supplied object** proves generic consequences
   from the axioms of a genuine supplied object. It does not construct that
   object.
3. A **point-level adapter** is an honest theorem about rational points or
   abstract groups. It may be a consumer, but it cannot discharge a
   representability node.
4. A **conditional shadow** packages a desired conclusion or substitutes an
   arbitrary equivalence for a missing construction. Existing compatibility
   boundaries may remain stable, but new theorem paths and completion credit
   must not grow through them.

Thus point-level cyclic-subgroup data are not a represented modular curve, an
abstract Picard group is not a Jacobian scheme, a supplied group object is not
a construction of the Weierstrass group law, and a Néron mapping-property API
does not prove that a Néron model exists. Foundational credit requires the
canonical maturity level named by the ledger and a real downstream consumer.

## Projections and navigation

The following are views of the canonical ledger, not competing databases:

- the [Verso Blueprint](../blueprint/README.md) renders the stable top-level
  mathematical DAG;
- the [coordination site](../site/README.md) renders public programme and
  challenge data;
- the compact [owner queue](../coordination/OWNER_QUEUE.md) shows only current
  execution lanes;
- [implementation status](IMPLEMENTATION_STATUS.md) summarizes the checked
  boundary;
- [progress methodology](PROGRESS_METHOD.md) defines credit;
- [claiming guidance](CLAIMING.md) defines contributor leases; and
- [route audit](ROUTE_AUDIT.md) records why the formal-immersion proof was
  selected.

Generated Blueprint chapters and `site/generated/program.json` must be
regenerated from the ledger. Narrative documents may explain the current
programme, but any disagreement is resolved in favor of the ledger.
