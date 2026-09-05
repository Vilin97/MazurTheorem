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
lifecycle, work packages, bounded execution selection, and release endpoints.
The limit is three packages, with two honest lanes currently selected.
Top-level nodes are the permanent 1,000-point accounting units.
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

The coherent-cohomology lane now has a canonical cover-independent action of
global functions in every degree and canonical structure-map field-linear
functoriality in `H¹`. That action is distinct from the older `hZeroModule` and
affine-cover/finite-map actions, which were transported across chosen
equivalences. The 11-point Čech comparison package is integrated because its
additive comparison is consumed by genuine-`H¹` finite-generation transfer;
the parent node receives no credit. Canonical `H⁰` compatibility, linear
connecting maps, and pointed proper-curve canonical-action `H¹` finiteness are
checked. Properness reduces canonical `H⁰` finiteness to finite global
sections over the source ring, and finite free sheaves are certified as
ordered low-degree-good targets. Supplied open-local, support-controlled
comparisons to those targets now assemble into the exact coherent
support-comodel consumed by induction. Constructing such comparison data for
every coherent sheaf and proving proper base change keep the final package
open. The first genuine Riemann--Roch consumer belongs to B2, downstream of
this foundation.

The Picard lane likewise separates an honest absolute construction from the
missing represented object. For one smooth proper integral curve over a field
and a supplied divisor-class/Picard equivalence, the checked residue-degree
map now gives an actual Picard degree homomorphism, its exact degree-zero
kernel, a splitting from a rational section, and a kernel-valued Abel--Jacobi
consumer. The map into the associated fppf sheafification is evaluated only
at the identity test object. None of these facts supplies an arbitrary-base
relative degree, relative `Pic⁰`, a representing Jacobian, or an Abel--Jacobi
scheme morphism.

The represented-modular lane proceeds through three explicit packages: the
canonical commutative group scheme on the concrete Weierstrass cubic, the
finite-flat cyclic subgroup generated by an exact-torsion point, and the
quotient with its kernel and base-change laws. Checked over-base addition
morphisms now exist on the actual product opens `D(x₁ - x₂)` and `D(B₁₂)`;
their affine and projective restrictions agree on the exact intersection, and
the second chart restricts to tangent doubling along the diagonal. Two actual
infinity-output morphisms agree with their affine counterparts on exact
intersections and with each other on their exact common principal open, and
the four principal opens cover the affine-pair presentation by elliptic
nonsingularity. All six pairwise restrictions agree on their actual pullbacks,
and the checked cover is glued to an actual affine-pair addition morphism.
The full projective product is now covered by the four products of the actual
`Y ≠ 0` and `Z ≠ 0` cubic charts, and its standard-by-standard member is
identified with the affine-pair presentation and consumes that morphism. This
is still not a global group scheme. The package remains active until addition
is constructed on the other three members, the overlaps and global gluing are
proved, and the group axioms and coordinate-point comparison are proved. The represented
`Γ₀`-moduli package waits on the subgroup package. Each step removes the
corresponding supplied group-object, compatibility, or arbitrary-interface
input from its named order-49 consumer.

The finite-translation quotient geometry is a separate reusable layer. Given
an actual commutative source group scheme with affine diagonal, a finite
section action, an invariant affine atlas, and scheme-theoretic freeness, it
constructs the actual quotient. Geometric integrality descends from a
geometrically integral source. Over an affine noetherian base, properness
descends from a proper source, while smoothness follows separately from a
flat, locally finite-type, geometrically reduced source. Its field
abelian-variety wrapper is a named consumer. It does not instantiate the
canonical Weierstrass source, the exact-torsion subgroup, the arithmetic
cyclic quotient, or its arbitrary base-change law.

Likewise, the polynomial cusp chart constructs genuine sections and proves a
closed-point collision used by the formal-immersion valuation consumer. It is
only a represented local chart: it is not represented `X₀`, a generalized-
elliptic compactification, or a finite-flat `Γ₀` classifier. The X₀ moduli and
integral nodes remain blocked. Separately, the supplied Néron mapping-property
interface and generic admissible-filtration API are integrated, while
construction of the actual source and quotient Néron models remains open. The
generic finite-translation quotient substrate proves neither an Eisenstein
generic-fibre identification nor the Néron mapping property. No Eisenstein
instantiation is selected before those objects exist.

Rational-torsion finiteness is not a missing full Mordell--Weil theorem. The
integrated `MazurTorsion.rationalTorsion_finite` proof feeds the checked
rational Northcott instance and approximate parallelogram law to Mathlib's
direct finite-torsion descent theorem. A separate integrated base-only package
proves the generic finite-abelian rank-two normal form from allowed orders and
exactly `c2Cube`, `c3Square`, `c5Square`, and `c7Square`. Its cross-module
rational adapter compiles conditionally, but the two-point WP remains blocked
on point-order, `h55`, and `h77` API inputs. `c4Square`, `c2c10`, and `c2c12`
remain classification-only before the immutable ncard bridge.

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
