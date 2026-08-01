# Upstream and dependency strategy

Mazur's theorem sits across several formalization ecosystems. This repository
uses them as upstreams, not as untracked code mines.

## Core pin

The checked `MazurTorsion` package uses Lean `v4.33.0-rc1` and Mathlib commit
`79d0395a1825a6264ad5d269e35e60537518955e`, matching the current Lean Pool
challenge and the Tau Ceti contract workspace. Future pin migrations remain
their own weighted roadmap node and pull request.

## Mathlib

General-purpose results belong in Mathlib when their API and scope fit.
Downstream adapters should be thin and pinned. No local theorem is counted
complete merely because a similar theorem exists on a newer Mathlib revision.

## Lean Pool

Lean Pool provides the immutable target, comparator model, quality policy, and
many reusable completed projects. A final solution must be replayable against
the target statement without importing its open challenge.

## Tau Ceti

Tau Ceti is the preferred upstream for large algebraic-geometry interfaces
such as divisors, Picard functors, abelian varieties, and the Jacobian
roadmap. It now shares this repository's exact Lean/Mathlib pin, while its work
still lives in [`upstream/tauceti/`](../upstream/tauceti/) as a separately
resolved Lake package. Direct integration remains blocked until the explicit
migration node connects those dependency graphs and adds consumer tests.

## FLT repositories

The Imperial FLT and related repositories contain relevant interfaces and
experimental proof cones. A declaration stated as an axiom or depending on
unfinished work is design prior art, not a proof dependency. Any port must
retain its license, author headers, exact source commit, and a declaration
audit.

## Poincaré Conjecture project

The
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
repository was refreshed at commit
[`68475da55dca31369fe2b274b3e554d4f18aaec1`](https://github.com/frenzymath/Poincare-Conjecture/commit/68475da55dca31369fe2b274b3e554d4f18aaec1).
It separates a primary dependency-driven proof, source-faithful book and
article formalizations, shared infrastructure, and a public site that
distinguishes verified declarations from work in progress.

That is the right coordination pattern for a theorem whose prerequisites are
larger than its final statement. This repository adopts the dependency-first
blueprint, visible verification status, and source-project separation. It adds
an exact weighted ledger and compiler-checked claim contracts because Mazur's
current frontier spans separately resolved dependency graphs and several
unbuilt interfaces. The visual roadmap is coordination evidence, not proof
evidence.

## Dependency updates

Each dependency is pinned to an immutable commit in the roadmap. Updates must
be isolated PRs that:

- explain why the update is needed;
- rebuild affected consumers;
- report API changes and axiom results;
- update provenance and generated artifacts;
- do not change roadmap weights.
