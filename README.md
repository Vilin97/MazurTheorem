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
* an exact bridge from the point-order theorem alone to the LeanPool
  cardinality target, with all seven forbidden subgroup embeddings
  discharged internally;
* `#E[2](F) ≤ 4`, `#E[4](F) ≤ 16`, and `#E[3](ℚ) ≤ 9`;
* non-embedding of `(ℤ/2ℤ)^3`, `(ℤ/3ℤ)^2`, and `(ℤ/4ℤ)^2` into the
  relevant rational point groups;
* every nonzero-order rational root of unity is `1` or `-1`, and hence a
  primitive rational root of unity has order at most two;
* the scalar-multiplication-to-division-polynomial root criteria at `5` and
  `7`, proved from the affine group law and low-level `Φ`/`ΨSq`
  identities;
* the complete split-polynomial/square-discriminant reduction for excluding
  full rational `5`- and `7`-torsion from their fixed discriminant
  identities;
* unconditional universal fifth- and seventh-division discriminant
  identities, and hence unconditional non-embedding of full rational
  `5`- and `7`-torsion;
* compact sparse-resultant certificates for both identities, reducing the
  degree-24 seventh-level case to one cubic resultant and
  elliptic-divisibility syzygies;
* the complete direct reduction of `C₂ × C₁₀` to
  `e² = X⁴ - 11X²Y² - Y⁴`, including Tate normalization, square
  discriminant, denominator clearing, coprimality, and sign cases;
* a fully checked elementary infinite descent for that quartic, and hence
  unconditional non-embedding of `C₂ × C₁₀` in rational points and
  rational torsion;
* the complete direct reduction of `C₂ × C₁₂` to
  `w² = (t² - 1)(9t² - 1)` and then to the explicit cubic
  `Y² = (X - 10)(X - 6)(X + 6)`, with all degenerate cases excluded;
* an explicit two-descent on that cubic: four doubling cosets, finite
  generation from naïve height, exact rational two-torsion cardinality
  four, Mordell--Weil rank zero, and finiteness of its rational point group;
* an exact-pin port of good-reduction infrastructure, an injective
  reduction map at `5`, and a checked count of eight reduced points,
  closing the exceptional cubic and hence unconditionally excluding
  `C₂ × C₁₂`;
* the finitely generated abelian-group identity
  `[G : nG] = n ^ rank(G) * #G[n]`, narrowly ported from Michael Stoll's
  Apache-2.0 project and checked at the challenge pin;
* a reusable Tate normal form with a scaling equivalence, checked formulas
  through explicit `5P`, and a checked addition recurrence used for `6P`;
* an exact order-fifteen certificate reducing a marked point of order
  fifteen to a concrete Tate-normal-form polynomial and discriminant
  identity;
* a complete specialized two-isogeny descent on the standard
  `X₁(15)` Weierstrass model, including every local squareclass
  obstruction, two doubling cosets, finite generation, rank zero, and
  finiteness;
* the shared exact order-nine Tate polynomial certificate needed by the
  order-eighteen and order-twenty-seven branches;
* the complete exact-order-eleven reduction to the non-cuspidal locus of
  `X₁(11): v²+v=u³-u²`, together with its five visible rational points
  and sharp good-reduction count at `3`;
* an explicit equation-checked degree-five Vélu candidate from `X₁(11)`
  to `y²+y=x³-x²-10x-20`, an exact enumeration of rational five-torsion,
  a five-fold naïve-height descent, and a proved
  `FiveCosetBound → rank zero → finiteness → cusp classification` chain;
  the named `FiveCosetBound` proposition is the remaining honest
  five-isogeny Selmer computation;
* the exact order-thirteen reduction to a non-cusp point on its standard
  genus-two sextic, its order-six symmetry and conic quotient, the complete
  primitive split-`19` norm data, and an independently derived
  degree-`(19,16)` polynomial Pell certificate for the difference of the
  two infinity branches;
* the order-eighteen reduction from its simultaneous order-nine and
  two-division equations through a rational parameterization to the
  explicit genus-two `X₁(18)` sextic, with every denominator retained;
* an exact order-fourteen certificate, with checked formulas through `7P`,
  every recurrence denominator proved nonzero, and an explicit
  Tate-parameter equation for the genus-one `X₁(14)` boundary;
* a complete specialized two-isogeny descent on
  `X₁(14): V²=U(U²-11U+32)`: two doubling cosets, finite generation,
  exact rational two-torsion, rank zero, finiteness, and six distinct
  visible rational points;
* the explicit inverse Tate-to-`X₁(14)` map, injective good reduction at
  `3`, an exact count of six reduced points, and hence the unconditional
  exclusion of rational points of order fourteen;
* the nondegenerate quartic-difference theorem
  `x⁴ - y⁴ ≠ z²` for nonzero integers, proved by primitive-Pythagorean
  infinite descent;
* an unconditional exclusion of rational points of exact order sixteen,
  reducing a normalized duplication chain to the `X₁(16)` sextic and
  closing its two parity branches with the quartic-difference theorem and
  Fermat's exponent-four theorem;
* a reusable normalization of any rational point of order two to
  `y²=x(x²+ax+b)`, explicit two-isogeny and dual point functions with both
  composites equal to doubling, and powers-of-two compatibility;
* unconditional exclusions of exact rational orders twenty and
  twenty-four: fixed-multiple image calculations construct forbidden
  `C₂×C₁₀` and `C₂×C₁₂` subgroups on the isogenous curves, without
  assuming that the raw point functions preserve arbitrary addition;
* the explicit `X₀(21)` curve `y²+xy=x³-4x-1`, its split
  full-two-torsion model, complete denominator squareclass reduction,
  mod-`16` local obstructions, and a conditional eight-point
  classification whose only arithmetic inputs are two named primitive
  quartic descents;
* an exact divisor-closure reduction of the point-order theorem to prime
  orders at least eleven and the eleven minimal composite orders
  `14,15,16,18,20,21,24,25,27,35,49`;
* an incremental rational point-order interface which applies the
  unconditional order-`14`, `15`, `16`, `20`, and `24` theorems
  internally, leaving callbacks only for the large-prime layer and the six
  composite orders `18,21,25,27,35,49`;
* an exact conditional cardinality endpoint whose only input is the
  point-order theorem;
* the explicit point-group additive equivalence induced by a Weierstrass
  variable change, ported from Michael Stoll's Apache-2.0 project;
* torsion-subgroup transport along additive equivalences, the cyclic
  extension lemma needed for the `20`/`24` isogeny kernels, and rational
  Northcott finiteness for logarithmic height.

The deep point-order theorem remains incomplete.  Its exact dependency
frontier is documented rather than hidden.

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

`EllipticCurve/VariableChange.lean`,
`Foundations/NaiveHeightDescent.lean`, and
`GroupTheory/IndexNSmulFG.lean` are narrow ports from Michael Stoll's
Apache-2.0
[`EllipticCurves`](https://github.com/MichaelStollBayreuth/EllipticCurves)
repository at commit `3f8c39c`; its copyright, license, and authorship
headers are retained. The files compile unchanged in substance at the exact
LeanPool pin with narrower imports.
