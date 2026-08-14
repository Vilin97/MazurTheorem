# Technical blueprint

This document is the compact architectural contract for the Lean
formalization. The exact node weights, statuses, work packages, artifacts, and
dependency edges live in [`coordination/program.json`](../coordination/program.json).
The generated Verso chapters are the exhaustive node-by-node view.

## 1. Release boundaries

The canonical endpoint is the full group classification:

```lean
theorem MazurTorsion.rationalTorsion_hasMazurClassification
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    MazurTorsion.HasMazurClassification E
```

`HasMazurClassification E` is already defined and means

```lean
(∃ n ∈ cyclicOrders,
    Nonempty (RationalTorsion E ≃+ ZMod n)) ∨
  ∃ m ∈ bicyclicParameters,
    Nonempty (RationalTorsion E ≃+ (ZMod 2 × ZMod (2 * m)))
```

The second release endpoint is the immutable challenge
`Challenge.Mazur.torsion_ncard_le`. It can be obtained directly from the
allowed-point-order theorem by the existing finite/infinite split, or as a
corollary of the full classification. It is not interchangeable with the full
classification.

Three additional final inputs are explicit:

```lean
-- proposed
theorem MazurTorsion.rationalTorsion_finite ...

-- proposed
theorem MazurTorsion.rationalTorsion_hasRankTwoPresentation ...

-- existing assembly theorem
theorem MazurTorsion.hasMazurClassification_of_rankTwo ...
```

This makes the previously omitted Mordell–Weil finiteness boundary visible.

## 2. Proof spine

```text
finite exceptional endpoints ───────┐
                                    ├─ allowed point orders
represented X₀(N) point             │
        │                           │
private Eisenstein witness          │
        │                           │
formal collision at 5               │
        │                           │
good reduction + #E(F₅) ≤ 10 ──────┘
                                    │
Mordell–Weil finiteness + rank two ─┤
forbidden subgroup results ─────────┤
                                    ▼
                    full fifteen-group classification
                                    │
                                    ▼
                         ncard-at-most-16 challenge
```

The prime-order public API must not expose the construction details of the
Eisenstein quotient. Its proposed seam is:

```lean
-- proposed; exact fields require interface review before implementation
structure MazurTorsion.PrimeOrder.DegreeOneFormalImmersionWitness where
  -- represented integral modular and cusp sections
  -- a cusp-normalized map to a supplied abelian/Néron target
  -- formal immersion at infinity in residue characteristic five
  -- torsion of the particular modular image
  -- specialization compatibility used by the collision
```

The private constructor is proposed as
`ModularCurve.EisensteinQuotient.toDegreeOneFormalImmersionWitness`.

## 3. Object maturity levels

Every public object belongs to one of four maturity levels.

1. **Canonical constructed object** — the actual scheme, morphism, group
   object, or theorem has been constructed and its laws proved.
2. **Canonical interface over a supplied object** — a genuine mathematical
   object is supplied, and the file proves generic consequences of its actual
   axioms. `AlgebraicGeometry.NeronModel` and its generic specialization API
   belong here.
3. **Point-level adapter** — an honest statement about rational points or
   abstract groups, explicitly not a represented moduli object. Such adapters
   may be consumers, but cannot discharge representability nodes.
4. **Conditional shadow** — a record containing the theorem one ultimately
   wants as a field, or an arbitrary equivalence standing in for a missing
   construction. Existing compatibility wrappers may remain stable, but new
   theorem paths must not grow through them.

The roadmap credits a foundational node only when the appropriate canonical
level is reached and a named downstream theorem consumes it.

## 4. Finite-group and arithmetic assembly

### Existing canonical API

- `MazurTorsion.RationalTorsion`
- `MazurTorsion.cyclicOrders`
- `MazurTorsion.bicyclicParameters`
- `MazurTorsion.HasMazurClassification`
- `MazurTorsion.HasMazurClassificationIfFinite`
- `MazurTorsion.hasMazurClassification_of_rankTwo`
- `MazurTorsion.torsion_ncard_le_of_classification`
- the checked forbidden-embedding package in
  `MazurTorsion.GroupTheory.FiniteClassification`
- the checked point-order reduction in
  `MazurTorsion.Arithmetic.PointOrder`

### Remaining integration

`MazurTorsion.rationalTorsion_orders_mem_cyclicOrders` must join the prime
theorem and finite endpoints. The full classification additionally needs an
honest proof that rational torsion is finite and an invariant-factor
presentation of rank at most two. The numerical challenge deliberately did
not force those facts, so they must not be treated as already integrated.

## 5. Curve cohomology, Picard, and Jacobian

### Coherent cohomology

`MT-TC-B1-COHERENT-COHOMOLOGY` is independent of the global
divisor/line-bundle dictionary. Its active work package supplies only the
proper-curve finite-cohomology core consumed by Riemann–Roch and Picard
representability. General cohomology machinery outside that consumer is not
on the critical path.

### Divisors and line bundles

The existing absolute divisor-class/Picard adapters are useful point-level
normalizations. The remaining A3 theorem is the global tensor-compatible
dictionary: exact principal kernel, essential surjectivity, and descent of
the actual line bundle. Local affine comparisons do not by themselves prove
this global result.

### Relative Picard

D1 owns only:

- the rigidified relative Picard functor modulo pullbacks from the base;
- its degree-zero subfunctor;
- the exact fppf descent/sheafification statement used downstream.

D2 owns:

- representability of `Pic⁰`;
- the normalized universal Poincaré bundle;
- properness and geometric connectedness of the representing group scheme.

The universal bundle no longer appears in D1.

### Jacobian and Abel–Jacobi

The Jacobian is the represented degree-zero Picard group scheme of a smooth,
proper, geometrically connected curve. The existing `PicardDegreeZero` and
`PicardAbelJacobi` modules construct valuable abstract Picard classes, but
they are not a Jacobian scheme.

The canonical completion must construct:

```lean
-- proposed
TauCeti.AlgebraicGeometry.Jacobian
TauCeti.AlgebraicGeometry.Jacobian.abelJacobi
TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_baseChange
```

Only the universal property and base-change facts consumed by modular curves
are required initially. General polarization theory is outside the critical
path.

## 6. Elliptic curves and finite-flat cyclic subgroups

The project has checked point-level `RationalCyclicSubgroup`, divisor
subgroups, constant finite-flat carriers, quotient formulas, projective cubic
geometry, and rational-point comparisons. These are not yet a construction of
the global Weierstrass group scheme: multiplication on the projective cubic
has not been constructed and proved compatible with the affine point law.

Therefore:

- `RationalCyclicSubgroup` remains explicitly point-level;
- `SplitGammaZeroDatum` remains split-constant finite-flat data;
- supplied `WeierstrassGroupSchemeInterface`-style records are compatibility
  wrappers, not canonical endpoints;
- no new adapter may claim a canonical group scheme merely by assuming a
  `GrpObj` instance or an arbitrary point equivalence.

The active vertical slice constructs the missing compatibility needed to send
an exact-order-49 point through an honest finite-flat subgroup to a represented
`X₀(49)` point. Its named endpoint is
`MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine`.

## 7. Represented `X₀(N)`

`X₀(N)` is not defined by the existing rational-data record. The canonical
object must address the moduli problem of generalized elliptic curves with a
finite locally free cyclic subgroup, its coarse/represented form in the exact
range used here, compactification, cusps, and prime-to-level base change.

The first implementation may specialize aggressively:

- prime levels `N = 11` and `N ≥ 17` at residue characteristic `5`;
- level `35` at residue characteristic `11`;
- level `49` for the explicit vertical slice.

It need not first solve arbitrary level or residue-characteristic-dividing-level
geometry.

Required outputs are:

```lean
-- proposed
ModularCurve.XZeroModuli
ModularCurve.XZeroModuli.pointOfRationalCyclicSubgroup
ModularCurve.IntegralXZero
ModularCurve.XZero.infinityCusp
ModularCurve.XZero.atkinLehner
```

The point constructor must consume an actual finite-flat subgroup scheme and
prove noncuspidality; a supplied equivalence of point sets is not sufficient.

## 8. Formal immersion

The local algebra layer is already canonical:

- maps on stalks and cotangent spaces;
- the surjectivity definition of formal immersion;
- quotient-cotangent and Nakayama criteria;
- completed-DVR collision consequences;
- degree-one q-expansion certificates.

What remains is not another abstract criterion. It is the genuine modular
input: the represented cusp chart, the actual quotient map, and the Hecke
q-expansion theorem proving the criterion at that cusp.

## 9. Néron models and specialization

`AlgebraicGeometry.NeronModel` is a genuine interface over an actual smooth
separated model with the Néron mapping property. Generic consequences belong
under `MazurTorsion.AlgebraicGeometry.NeronModel`, not under a modular-curve
namespace.

The specialization layer owns:

- the residue-field point map induced by a supplied model;
- restriction and specialization of base sections;
- the generic equal-image/formal-collision lemma;
- prime-to-residue torsion specialization once its hypotheses are proved.

The existing prime-five theorem is the named consumer. Separate work packages
must still construct Néron models for the source elliptic curve and for the
modular quotient; a generic theorem over a supplied model is not an existence
proof.

General component-group classification is unnecessary for the checked local
additive-reduction contradiction. The remaining component work is only the
represented identity component and toric modular fibre used by the private
Eisenstein rank-zero constructor.

## 10. Eisenstein rank zero

The private witness constructor needs a narrow chain:

1. the modular Jacobian and Hecke-stable optimal quotient;
2. nontriviality at prime `N = 11` or `N ≥ 17`;
3. the multiplication-kernel finite-flat presentation actually used;
4. a two-factor constant/multiplicative filtration;
5. the required represented fppf `H¹` bounds;
6. the bad-level comparison and Raynaud uniqueness in this specialized case;
7. finite generation and the Kummer cardinality argument forcing rank zero;
8. finite rational points, hence torsion of the particular modular image.

The repository already contains much of the generic Kummer-cardinality and
represented fppf-cohomology consumer side. It does not yet identify the
actual modular quotient kernel with that data. Conditional kernel packages do
not complete the node.

## 11. Finite endpoints

The finite point-order callbacks are `13`, `18`, `25`, `35`, and `49`; order
`11` is supplied by the prime theorem. The order-specific code remains
checked, but current maintainer work is limited to order `49` as a consumer of
the represented modular-curve lane. The other unsolved contracts are paused
until the shared geometry they require is available.

## 12. Module and dependency policy

- Generic algebraic geometry belongs under `MazurTorsion/AlgebraicGeometry/`.
- Modular constructions belong under `MazurTorsion/ModularCurve/` only after
  they consume represented modular objects.
- Arithmetic specializations belong under `MazurTorsion/PrimeOrder/` or
  `MazurTorsion/NumberTheory/` and must import the generic layer, never the
  reverse.
- Compatibility modules may re-export moved declarations, but new consumers
  should import the canonical owner.
- Every new interface needs a design review and a named downstream consumer.
- A work package is a planning partition; only its parent node earns progress
  credit.

## 13. Acceptance discipline

A foundation is complete only when all four statements are true:

1. the mathematical object is constructed at the claimed maturity level;
2. its laws are kernel-checked without prohibited assumptions;
3. the public API is reviewed and placed in the correct dependency layer;
4. the ledger's named downstream consumer compiles using that API.

Large generated certificates, conditional shadows, line counts, and isolated
helper proofs are evidence, not completion.
