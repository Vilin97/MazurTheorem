# Upstream and dependency strategy

Mazur's theorem sits across several formalization ecosystems. This repository
uses them as upstreams, not as untracked code mines.

## Core pin

The checked `MazurTorsion` package remains on Lean `v4.32.0-rc1` and Mathlib
commit `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, matching the original Lean
Pool challenge. A pin migration is its own weighted roadmap node and its own
pull request.

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
roadmap. Current Tau Ceti uses a different Lean/Mathlib pin, so its work lives
in [`upstream/tauceti/`](../upstream/tauceti/) as a separate Lake package.
Cross-pin integration is blocked until the explicit migration node lands.

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
current frontier spans two incompatible dependency pins. The visual roadmap
is coordination evidence, not proof evidence.

## Dependency updates

Each dependency is pinned to an immutable commit in the roadmap. Updates must
be isolated PRs that:

- explain why the update is needed;
- rebuild affected consumers;
- report API changes and axiom results;
- update provenance and generated artifacts;
- do not change roadmap weights.
