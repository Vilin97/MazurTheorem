# Mazur's torsion bound

This Lean 4 package targets LeanPool's `Challenge.Mazur.torsion_ncard_le`:
the torsion subgroup of the rational points of an elliptic curve over `ℚ`
has at most sixteen elements.

The package is pinned to Lean `v4.32.0-rc1` and the matching Mathlib release
used by the LeanPool challenge. Development is kept buildable and
placeholder-free: incomplete mathematical layers are tracked in
`BLUEPRINT.md`, not introduced as axioms or admitted Lean declarations.

Current machine-checked results include:

* the exact finite/infinite `Set.ncard` reduction;
* the cardinality consequence of Mazur's fifteen-group classification;
* a presentation-independent forbidden-embedding API and a complete
  finite-abelian theorem proving `Nat.card G ≤ 16` from allowed element
  orders and seven forbidden subgroups, without a rank-two hypothesis;
* an exact conditional bridge from the point-order theorem and four
  remaining arithmetic subgroup exclusions to the LeanPool cardinality
  target;
* `#E[2](F) ≤ 4`, `#E[4](F) ≤ 16`, and `#E[3](ℚ) ≤ 9`;
* non-embedding of `(ℤ/2ℤ)^3`, `(ℤ/3ℤ)^2`, and `(ℤ/4ℤ)^2` into the
  relevant rational point groups;
* every nonzero-order rational root of unity is `1` or `-1`, and hence a
  primitive rational root of unity has order at most two;
* the scalar-multiplication-to-division-polynomial root criteria at `5` and
  `7`, proved from the affine group law and low-level `Φ`/`ΨSq`
  identities;
* the complete split-polynomial/square-discriminant argument for excluding
  full rational `5`- and `7`-torsion, now conditional only on the two
  classical fixed-level discriminant identities;
* the explicit point-group additive equivalence induced by a Weierstrass
  variable change, ported from Michael Stoll's Apache-2.0 project;
* torsion-subgroup transport along additive equivalences, the cyclic
  extension lemma needed for the `20`/`24` isogeny kernels, and rational
  Northcott finiteness for logarithmic height.

The deep point-order theorem and modular-curve exclusions are not yet
complete. Their exact dependency frontier is documented rather than hidden.

Project documentation:

* [`INFORMAL_PROOF.md`](INFORMAL_PROOF.md) gives the detailed mathematical
  proof and Mazur's prime-level argument;
* [`PRIOR_ART.md`](PRIOR_ART.md) records the pinned repository and
  declaration audit;
* [`BLUEPRINT.md`](BLUEPRINT.md) gives the declaration-level module plan,
  milestones, risks, and verification policy.

For a memory-conservative build:

```sh
LEAN_NUM_THREADS=1 lake build MazurTorsion
```

`TwoTorsion.lean`, `ThreeTorsion.lean`, and `FullFourTorsion.lean` were
written by Victor Aguiar for the Apache-2.0 LeanPool foundation branch at
commit `60bec16`; their copyright, license, and authorship headers are
retained. They were verified unchanged against this package's older exact
challenge pin before being ported to the local namespace. The generic
two-torsion file additionally exposes `[DecidableEq F]` as a public
parameter instead of baking a private classical decider into theorem types;
this preserves instance coherence at the rational specialization without
changing the proofs.

`EllipticCurve/VariableChange.lean` is ported from Michael Stoll's
Apache-2.0
[`EllipticCurves`](https://github.com/MichaelStollBayreuth/EllipticCurves)
repository at commit `3f8c39c`; its copyright, license, and authorship
header is retained. The file compiles unchanged in substance at the exact
LeanPool pin with narrower imports.
