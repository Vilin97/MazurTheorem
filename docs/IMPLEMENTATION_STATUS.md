# Detailed implementation status

This Lean 4 package targets Lean Pool's `Challenge.Mazur.torsion_ncard_le`:
the torsion subgroup of the rational points of an elliptic curve over `ℚ`
has at most sixteen elements.

The package is pinned to Lean `v4.33.0-rc1` and the matching Mathlib release
used by the LeanPool challenge. Development is kept buildable and
placeholder-free: incomplete mathematical layers are tracked in the
[technical blueprint](TECHNICAL_BLUEPRINT.md) and
[canonical programme ledger](../coordination/program.json), not introduced
as axioms or admitted Lean declarations.

The audited prime-order route is Mazur's 1978 degree-one formal-immersion
argument at auxiliary prime five, not the older global
semistability--cyclotomic--Shafarevich chain. The same engine is reused at
eleven for exact order 35, while order 49 now maps directly to the checked
two-cusp classification of `X₀(49)`. See
[`ROUTE_AUDIT.md`](ROUTE_AUDIT.md) for the literature comparison, exact
dependency migration, and fallback policy. This refactor awards no
completion credit and leaves every registered Challenge in force.

Current machine-checked results include:

* the exact finite/infinite `Set.ncard` reduction;
* the cardinality consequence of Mazur's fifteen-group classification;
* a presentation-independent forbidden-embedding API and a complete
  finite-abelian theorem proving `Nat.card G ≤ 16` from allowed element
  orders and seven forbidden subgroups, without a rank-two hypothesis;
* an exact bridge from the point-order theorem alone to the LeanPool
  cardinality target, with all seven forbidden subgroup embeddings
  discharged internally;
* a checked normalization of every elliptic Weierstrass equation over
  `F₅` to one of 25 short models, exhaustive proof that its point group has
  at most ten elements, and a separate compiled consumer excluding point
  orders at least eleven;
* a checked raw rational cyclic-subgroup datum, exact-order generator
  construction, and a direct conditional order-49 consumer of the two-cusp
  `X₀(49)(ℚ)` classification; the actual coarse classifying map and
  explicit-model identification remain open;
* a second checked finite normalization/enumeration over `F₁₁`, proving
  `#E(F₁₁) ≤ 18` for every elliptic Weierstrass equation and supplying
  the exact-order-35 reduction-fibre contradiction;
* the fixed model expected for the order-35 quotient,
  `y²+y=x³+x²+9x+1`, its explicit
  order-three normalization, and an unconditional equivalence of its rational
  torsion subgroup with `ZMod 3`; the equation-checked Vélu point-function
  candidate has exactly the visible three-element zero fibre, and its
  candidate target has trivial rational torsion by division-polynomial
  factorization and reduction at three. A total opposite candidate now has a
  checked composite equal to multiplication by three on every rational source
  point. The rational three-cover and visible `1`, `7`, and `49` translations
  feed a checked reduced numerator-denominator argument proving the exact
  source cube-class bound. Target-candidate surjectivity then assembles the
  three cosets, with compiled downstream consumers proving finite generation,
  rank zero, and finiteness. Target-curve finiteness and the modular
  identification remain open, so unconditional rank zero is not yet claimed;
* exact unramified formal-kernel torsion and collision theorems at the integer
  primes `5` and `11`, plus concrete residue-field identifications and
  exact-order preservation under good reduction; the compiled consumers
  `rationalPoint_addOrderOf_ne_of_eleven_le_of_goodReductionAtFive` and
  `rationalPoint_addOrderOf_ne_thirtyFive_of_goodReductionAtEleven` join these
  maps to the exhaustive `F₅` and `F₁₁` bounds. At five, a second checked
  consumer starts from Mathlib's minimal completed equation, derives an
  elliptic integral model from good reduction, preserves point order through
  `adicRed`, and transports the result to `ZMod 5`; the local integral-`j` and
  supplied-filtration trichotomy feeds that endpoint directly. The
  global-to-local marked-point/minimal-model bridge and the Néron special-fibre
  and component-group maps needed before good reduction remain open;
* an explicit algebraic tame-additive filtration contract, recording a
  component group of cardinality at most four, the additive residue quotient,
  exact identification of its kernel with the formal kernel, and
  torsion-freeness there. Separate consumers now rule out prime orders at
  least eleven when the residue group has cardinality five and order 35 when
  it has cardinality eleven. This does not construct the geometric Néron
  filtration and earns no Néron node credit;
* the canonical `ℤ`-linear map between stalk cotangent spaces for a scheme
  morphism, its representative formula, surjectivity under a surjective
  stalk map, and an identity-morphism normalization consumer. A separate
  canonical semilinear map records the actual induced residue-field
  homomorphism. The degree-one certificate requires dimension one over the
  source residue field and turns a detected vector into the canonical
  surjectivity criterion. The maximal-ideal-adic completion map now also
  compiles for arbitrary local homomorphisms, is functorial, and defines
  `AlgebraicGeometry.IsFormalImmersionAt` by actual completed-local-ring
  surjectivity; identity and composition are checked consumers. Under finite
  generation of the target maximal ideal, a checked Nakayama theorem shows
  that cotangent surjectivity generates that maximal ideal. Residue and
  cotangent surjectivity also give a surjection modulo its square, with the
  modular degree-one certificate as a downstream consumer. Mathlib's
  precomplete/Hausdorff criterion then proves surjectivity on completions; a
  convenient corollary assumes both maximal ideals finite. Mathlib's
  Noetherian-stalk theorem discharges these assumptions on locally Noetherian
  schemes, so the modular degree-one theorem now concludes the actual
  formal-immersion predicate under the natural geometric hypothesis.
  The integral cusp model, q-expansion calculation, and formal-immersion
  collision remain open, so no roadmap node is credited;
* the weighted point and divisor Abel--Jacobi classes from Tau Ceti transported
  through a divisor-class/Picard equivalence into the actual degree-zero
  subgroup of `Scheme.Pic`. The checked formulas cover the base point,
  collision by linear equivalence, equal-weight point differences, point
  divisors, and principal divisors. An exact divisor dictionary additionally
  produces the chosen Abel--Jacobi line bundle and detects its isomorphism
  class. This is an absolute group-valued precursor, not the relative Picard
  functor, Jacobian variety, or Abel--Jacobi scheme morphism, so no D1, E1, or
  F1 credit is claimed;
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
  mod-`16` local obstructions, unconditional eight-point classification,
  checked Hauptmodul transfer, exceptional-`j` certificates, and the resulting
  exclusion of exact rational order twenty-one;
* an exact divisor-closure reduction of the point-order theorem to prime
  orders at least eleven and the eleven minimal composite orders
  `14,15,16,18,20,21,24,25,27,35,49`;
* an incremental rational point-order interface which applies the
  unconditional order-`14`, `15`, `16`, `20`, `21`, `24`, and `27` theorems
  internally, leaving callbacks only for the large-prime layer and the four
  composite orders `18,25,35,49`;
* an exact conditional cardinality endpoint whose only input is the
  point-order theorem;
* the explicit point-group additive equivalence induced by a Weierstrass
  variable change, ported from Michael Stoll's Apache-2.0 project;
* torsion-subgroup transport along additive equivalences, the cyclic
  extension lemma needed for the `20`/`24` isogeny kernels, and rational
  Northcott finiteness for logarithmic height;
* the exact shared Lean/Mathlib/Tau Ceti dependency graph, with a compiled
  downstream Tau Ceti contract build and permanent pin/provenance audit;
* Tau Ceti's finite-support theorem for codimension-one orders and its
  compiled scheme `OrderSystem` consumer;
* Tau Ceti's smooth-proper-curve product formula: a non-global rational
  function extends to a finite flat map to `P¹`, whose zero and infinity
  fibre degrees cancel. The checked Challenge transports the theorem to any
  order system with the same geometric orders, while the divisor quotient
  and `DivisorPicard.Dictionary.properCurveDegreeZero` provide real
  downstream consumers;
* Tau Ceti's product-dimension theorem for abelian varieties, proved through
  faithful integral-extension invariance of Krull dimension, Noether
  normalization for tensor products, and matching affine-chart bounds for
  nonempty finite-type scheme products, with a compiled self-product
  consumer;
* a checked finite-flat commutative group-scheme substrate with honest
  kernels, affine constant-rank point exponent, constant and diagonalizable
  examples, a genuine `μₙ` multiplication kernel, and constant-group
  quotients; morphism-level base-change naturality for the named constant
  families; and one exact fppf admissible-filtration step whose constant/μₚ
  factors force a `p²` point-exponent bound before and after
  kernel-compatible scalar extension. Generic kernel/quotient base change,
  fppf cohomology, Raynaud uniqueness, and the Eisenstein rank-zero consumer
  remain open; and
* explicit total Vélu and dual point maps for `X₁(11)` whose composition is
  multiplication by five; this is retained as a release-obligation fallback,
  not a prerequisite of the uniform order-eleven theorem.

The deep point-order theorem remains incomplete.  Its exact dependency
frontier is documented rather than hidden.

Project documentation:

* [`INFORMAL_PROOF.md`](INFORMAL_PROOF.md) gives the detailed mathematical
  proof and Mazur's formal-immersion prime-level argument;
* [`ROUTE_AUDIT.md`](ROUTE_AUDIT.md) records the primary-literature and
  pinned-API comparison behind the route selection;
* [`PRIOR_ART.md`](PRIOR_ART.md) records the pinned repository and
  declaration audit;
* [`TECHNICAL_BLUEPRINT.md`](TECHNICAL_BLUEPRINT.md) gives the original
  declaration-level module plan,
  milestones, risks, and verification policy.

The canonical current weighted roadmap is
[`../coordination/program.json`](../coordination/program.json); this inventory
is a detailed snapshot and does not define completion percentages.

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
