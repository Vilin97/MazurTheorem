# Tau Ceti interface challenges

This is a separate Lake package for open work that belongs against
[Tau Ceti](https://github.com/TauCetiProject/TauCeti). The core
`MazurTorsion` package now depends directly on the same immutable Tau Ceti
commit; this package remains separate only so open upstream contracts cannot
enter the checked implementation graph.

| Dependency | Exact pin |
|---|---|
| Lean | `v4.33.0-rc1` |
| Tau Ceti | `a3913fd9111b851af857f720b4ce6721e6634183` |
| Mathlib (through Tau Ceti) | `79d0395a1825a6264ad5d269e35e60537518955e` |

The files state small, compiler-checked API gaps against nouns that already
exist in Tau Ceti:

- finite support of the order of a rational function at codimension-one
  points, needed to package scheme principal divisors;
- additivity of abelian-variety dimension under products, a basic acceptance
  result for the future Jacobian API.

These are upstream-facing contracts, not completed Mazur proof. They carry
zero theorem-completion credit until proved, reviewed upstream, and consumed
by a Mazur node. Prefer opening the implementation in Tau Ceti and then
updating both the root dependency and this package to the same merged commit.

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build MazurTauCetiChallenge
```

Expected `declaration uses 'sorry'` notices are allowed only for currently
open registered contracts. CI derives the exact count from the canonical
ledger, so solving a contract removes one expected notice.
