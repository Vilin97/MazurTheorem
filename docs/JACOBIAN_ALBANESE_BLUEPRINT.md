# Jacobian and Albanese blueprint

This document is the implementation plan for the algebraic-geometric
Jacobian challenge in `lean-eval`.  It deliberately separates checked input
from the mathematical theorems that still have to be formalized.  In
particular, an abstract Picard group, a supplied group scheme, or a theorem
whose hypotheses already contain the desired Jacobian is not counted as a
construction.

The target is the following statement.  Let `k` be an arbitrary field and
let `C → Spec k` be proper, smooth of relative dimension one, and
geometrically irreducible.  There is a smooth proper geometrically
irreducible group scheme `J → Spec k` of dimension

```text
g = dim_k H¹(C, O_C)
```

which exists without a `k`-rational point.  Given a rational point `P`, the
map

```text
a_P : C → J,        x ↦ O_C(x - P)
```

sends `P` to the identity and is initial among pointed maps from `C` to an
abelian variety.

## 1. Existing checked foundations

The implementation should reuse the following code rather than introduce a
parallel abstraction.

| Requirement | Existing checked API | Status |
| --- | --- | --- |
| Ground-field action on genuine sheaf `H¹` | `SchemeModuleCohomology.hOneCanonicalFieldModule` | available over every field |
| Finite-dimensional `H¹(O_C)` under the challenge hypotheses | `Jacobian.structureHOne_finiteDimensional` | checked, with no rational-point input |
| Finite-dimensional `H¹` for a coherent module | `genuineSheafHOneCanonical_finiteDimensional_of_codimensionOnePoint` | available after supplying a codimension-one point |
| Vanishing above the dimension of a curve | `CurveCohomologyGrothendieckVanishing` | available |
| Finite map to `P¹` from a non-global rational function | `rationalFunctionMorphismAt_isFinite` | available |
| Finite map to `P¹` under the exact challenge hypotheses | `FiniteMapToProjectiveLine.hom` and `overHom` | checked, with no rational-point input |
| Permutation action on a relative power | `PermutationPower.action` and `action_equivariant` | checked |
| Projectivity of nonempty finite powers of `P¹` | `ProjectiveFiniteOrbit.projectiveLinePower_isProjectiveFactorization` | checked via the scheme-level Segre embedding |
| Affine neighbourhoods of finite projective orbits | `ProjectiveFiniteOrbit.hasAffineOrbit_of_isProjectiveFactorization` | checked over every field |
| Finite-group quotient from affine orbit neighbourhoods | `FiniteGroupQuotient.quotient` | checked, with categorical universal property |
| Symmetric powers of challenge curves in positive degree | `SymmetricPower.curveSchemeSucc` and `curveProjectionSucc` | quotient checked; projection finite/surjective; target geometrically irreducible and universally closed |
| Ordered universal incidence family on `C × C^d` | `UniversalEffectiveDivisor.orderedIncidence` | checked as the scheme-theoretic union of the coordinate graphs, with its ideal invariant under coordinate permutations; quotient descent remains |
| Absolute Picard group | AINTLIB `Scheme.Pic` port | available, group-valued only |
| Relative Picard presheaf definitions | AINTLIB `RelativePic` port | available, not represented |
| Pullback/tensor and section base-change identities | `PicardSectionBaseChange` and upstream adapters | available |
| Divisor and point-difference Abel--Jacobi classes | `PicardAbelJacobi`, `PicardRationalSectionAbelJacobi` | available on classes, not a scheme morphism |
| Group objects in schemes over a base | Mathlib `GrpObj (Over S)` | available |
| Morphism-property descent | Mathlib fpqc/fppf descent APIs | available for the properties already registered there |
| Abstract abelian-variety wrappers and products | Tau Ceti | useful vocabulary, not a Jacobian construction |

The finite-cohomology repository integrated under
`MazurTorsion.Upstream.CoherentCohomologyFinite` is useful for comparison and
for characteristic-zero consumers.  The genus definition below uses the
canonical arbitrary-field action instead, because the challenge quantifies
over every field and must not depend on rationalizing an abelian group.

The repository audit found no checked representability theorem for the
relative Picard functor, no constructed `Pic⁰`, and no checked Albanese
universal property in Mathlib, LeanPool, Tau Ceti, or the other inspected
Lean developments.  Consequently those results are implementation work, not
imports to be discovered later.

## 2. Mathematical construction

### 2.1 Integral and cohomological preliminaries

Geometric irreducibility plus smoothness implies geometric reducedness, hence
geometric integrality.  In particular `C` is nonempty and integral.  The
checked construction chooses a standard-smooth affine chart of relative
dimension one and then a nonzero maximal ideal in its coordinate ring.  The
maximal ideal cannot be zero: otherwise the coordinate ring would be a field
finite over the ground field, while standard smoothness supplies an injective
étale map from a one-variable polynomial ring, contradicting its infinite
dimension.  The corresponding scheme point has codimension one.  At such a
point the local ring is a discrete valuation ring.  A uniformizer, viewed in
the function field and inverted, has order `-1`; it cannot be a global regular
function.  The associated rational-function morphism `C → P¹_k` is finite.

For a coherent module `M`, finite pushforward along this map and the checked
two-affine calculation on `P¹` show that genuine sheaf `H¹(C, M)` is a finite
dimensional `k`-vector space.  The scalar action is the canonical action
obtained by restricting the global-section action along `C → Spec k`; it is
independent of the chosen point and finite map.

For `M = O_C`, define

```text
genus(C) := finrank k H¹(C, O_C).
```

The choice of a codimension-one point occurs only inside the checked proof of
finiteness, not in this definition or its hypotheses.

### 2.2 The relative Picard fppf sheaf

For a `k`-scheme `T`, put `C_T = C ×_k T` and define the rigidified relative
Picard prestack by line bundles on `C_T`, with arrows the line-bundle
isomorphisms.  Passing to isomorphism classes and quotienting by pullbacks of
line bundles from `T` gives the usual presheaf

```text
T ↦ Pic(C_T) / Pic(T).
```

The quotient formulation is essential when `C(k)` is empty.  If a point is
available, rigidification along that section is equivalent to the quotient,
but the Jacobian itself may not depend on this extra datum.

Sheafify for the fppf topology.  Prove the following in this order:

1. pullback is functorial before quotienting;
2. tensor product and dual descend to the quotient;
3. line bundles and their isomorphisms satisfy fpqc descent;
4. the quotient presheaf maps to an fppf sheaf of abelian groups;
5. formation of this sheaf commutes with arbitrary field extension.

The degree map is defined fiberwise by Euler characteristic,

```text
deg(L) = χ(L) - χ(O_C),
```

and is fppf local on the base.  This avoids choosing a rational divisor.
Its kernel is the degree-zero relative Picard sheaf `Pic⁰_{C/k}`.  One must
also prove that this kernel agrees with the connected component of the
identity after geometric base change.

### 2.3 Representability

Representability is the main new theorem.  A suitable proof route is the
classical symmetric-power construction, which is concrete enough to expose
all Lean dependencies.

1. Construct `Sym^d(C)` as the quotient of `C^d` by the finite permutation
   action and identify it with effective relative Cartier divisors of degree
   `d` on `C`.
2. Construct the universal effective divisor on
   `C × Sym^d(C)` and its line bundle.
3. Define the Abel map `Sym^d(C) → Pic^d_{C/k}`.
4. Prove relative Riemann--Roch and cohomology-and-base-change for line
   bundles on `C`.
5. For `d ≥ 2g - 1`, prove that the Abel map is an fppf-locally nonempty
   projective-space bundle.  Its fibers are complete linear systems.
6. Use the equivalence relation induced by the two projections from
   `Sym^d(C) ×_{Pic^d} Sym^d(C)` and effective descent to construct the
   representing scheme.
7. Transport tensor product, dual, and the trivial bundle through Yoneda to
   obtain the group object.

The construction must first represent all degree components locally and then
select the identity component.  Defining the Jacobian from a point-normalized
Picard functor would incorrectly require `C(k)` to be inhabited.

The first quotient step is now factored into checked code.  Relative powers,
their permutation actions, componentwise equivariance, stable-affine
refinement, quotient gluing, and descent of the structure map are all
formalized.  For every positive degree, the affine-orbit hypothesis is also
checked over an arbitrary field.  A nonempty finite product of projective
lines is projective by iterating the checked scheme-level Segre embedding.
For a finite family of points in projective space, retain the inclusion-
maximal homogeneous point ideals.  For each ordered pair of distinct maximal
ideals `I,J`, choose a homogeneous element in `J \ I`; multiplying these
pairwise separators gives an element vanishing at every maximal point other
than `I` and nonvanishing at `I`.  Multiplication by a coordinate nonzero at
`I` raises all such elements to one common positive degree.  Their sum is
nonzero modulo every maximal point ideal and hence modulo every original
point ideal.  Its homogeneous basic open is affine and contains the entire
finite orbit.  Pullback along a projective closed embedding proves the claim
for projective schemes.  Finally, the selected finite map `C → P¹` induces a
finite componentwise map `C^d → (P¹)^d`; affine-orbit neighbourhoods transfer
back along this affine map.

Thus `Sym^d(C)` is available for every `d > 0` under exactly the challenge
hypotheses.  Degree zero is the terminal relative power and can be treated
separately when its quotient interface is needed.  The ordered power is
proper, geometrically irreducible, and universally open.  Geometric
irreducibility descends to the symmetric quotient through the universally
surjective projection, and universal closedness descends from the proper
ordered power.  The quotient projection is finite: on each stable affine
chart, base sections land in the invariant ring, finite generation passes
from the base to the invariants, and finite-group integrality makes the chart
ring module-finite over its invariants.  The descended structure map is
locally of finite type on the same charts: Artin--Tate makes the base-to-
invariants map finite type, and epimorphicity of the invariant-spectrum map
identifies the chart restriction with its `Spec` morphism.

The quotient is also separated.  More generally, if `X → Y` is finite and
surjective and `X → S` is proper, then `Y → S` is separated.  After
base-changing the diagonal of `Y/S` along
`X ×_S X → Y ×_S Y`, its source is `X ×_Y X`; the resulting
morphism into `X ×_S X` is proper.  The product cover is again finite and
surjective, so universal closedness of the pulled-back diagonal descends
without a flatness assumption.  Since every scheme diagonal is an immersion,
a universally closed diagonal is a closed immersion.  Combining
separatedness, universal closedness, and local finite type proves that every
positive symmetric power constructed above is proper over the ground field.

The ordered incidence family needed for the next step is also checked.  In
`C ×_S C^d`, its `i`-th component is the equalizer of the first
projection and the `i`-th coordinate of the second projection.  Since
`C → S` is separated, each graph is a closed immersion.  The product of
their ideal sheaves defines the scheme-theoretic union, including the empty
family in degree zero, and its support is exactly the union of the graph
supports.  Coordinate permutations act by ambient isomorphisms, carry the
graph indexed by `g i` isomorphically to the graph indexed by `i`, and
transport finite products of ideal sheaves multiplicatively.  Consequently
the ordered incidence ideal is invariant with its scheme-theoretic
multiplicities.  It remains to descend this invariant ideal through the
finite symmetric quotient and prove the descended family is a relative
effective Cartier divisor of degree `d`.

Denote the representing object by

```text
J(C) := Pic⁰_{C/k}.
```

Yoneda gives a universal degree-zero line-bundle class on `C × J(C)`.  It is
only defined modulo pullback from `J(C)` in the unrigidified formulation,
which is exactly the correct invariant.

### 2.4 Geometry and dimension of `Pic⁰`

The geometric properties should be proved after base change to an algebraic
closure and descended.

* Finite type follows from the symmetric-power presentation.
* Properness follows from the valuative criterion: a degree-zero line bundle
  on the generic fiber extends across a DVR after twisting by vertical
  components, and the quotient by base line bundles removes the ambiguity.
* Smoothness follows from unobstructed deformation of line bundles on a
  curve.  The obstruction lies in `H²(C, O_C)`, which vanishes by the checked
  dimension-one cohomology theorem.
* The tangent space at the identity is canonically `H¹(C, O_C)`.  Express
  first-order line bundles through the exact sequence

  ```text
  1 → 1 + ε O_C → O^×_{C[ε]} → O_C^× → 1
  ```

  and identify `1 + ε O_C` additively with `O_C`.
* Translation by group elements identifies every tangent space with the
  tangent space at the identity.  Smoothness therefore has constant relative
  dimension `finrank k H¹(C, O_C) = genus(C)`.
* The identity component is geometrically connected by definition; smoothness
  makes it geometrically reduced.  Connected plus reduced for a group scheme
  of finite type over a field gives geometric irreducibility here, or one can
  prove irreducibility directly from the symmetric-power cover.  This step
  must produce Mathlib's exact `GeometricallyIrreducible` morphism property.

Tensor product is symmetric, so the resulting group object is commutative.
The lean-eval target asks only for `GrpObj`; keeping commutativity internally
is nevertheless useful for sums and descent.

### 2.5 Pointed Abel--Jacobi morphism

Let `P : Spec k → C`.  On `C × C`, the diagonal is an effective Cartier
divisor because `C` is smooth of relative dimension one.  The graph of the
constant section `P` is another relative effective Cartier divisor.  The
line bundle

```text
O(Δ - C × P)
```

has degree zero on every fiber.  By the representing property, it determines

```text
a_P : C → Pic⁰_{C/k}.
```

Pulling the family back along `P` yields the trivial class, so
`P ≫ a_P = e`.  This proof should reuse the checked point-difference Picard
class and section base-change lemmas as the pointwise shadow of the family
calculation.

### 2.6 Albanese universal property

Let `A/k` be smooth, proper, geometrically irreducible, and a group object,
and let `f : C → A` satisfy `f(P) = e_A`.

First prove the rigidity lemmas needed by the exact challenge statement.

1. A morphism from a proper geometrically connected scheme to a separated
   group scheme that is constant on one geometric fiber is constant when the
   standard rigidity hypotheses hold.
2. If `h : B → A` is a scheme morphism between abelian varieties and
   `h(e_B) = e_A`, apply rigidity to

   ```text
   (x,y) ↦ h(x+y) - h(x) - h(y)
   ```

   to prove that `h` is a group homomorphism.

This second result matters because the challenge quantifies over ordinary
arrows `J(C) ⟶ A`, not bundled homomorphisms of group objects.

There are two equivalent constructions of the factor map.  The preferred
formal route continues the symmetric-power presentation:

1. On `C^d`, sum the values of `f`.  Commutativity makes this map symmetric,
   so it descends to `s_d : Sym^d(C) → A`.
2. Choose `d ≥ 2g - 1`.  Prove that `s_d` is constant on the complete linear
   systems forming fibers of `Sym^d(C) → Pic^d(C)`.  This is Abel's theorem;
   its proof uses principal divisors and the rigidity lemma.
3. Descend `s_d` through the projective-bundle presentation to
   `Pic^d(C) → A`.
4. Translate degree `d` to degree zero using `dP`, obtaining
   `g : J(C) → A`.
5. Pull back along the degree-one Abel map to prove `f = a_P ≫ g`.
6. If `g₁` and `g₂` have the same pullback along `a_P`, their difference is
   zero on `a_P(C)`.  It is therefore zero on all finite sums, hence on the
   fppf-locally surjective symmetric-power presentation of `J(C)`.  Effective
   epimorphism descent gives `g₁ = g₂`.

The construction commutes with field extension, and all arguments may be
checked fppf locally before descending to `k`.  No rational point is used in
the construction of `J(C)`; `P` is used only to turn the Picard torsor into a
pointed Abel map and to translate `Pic^d` to `Pic⁰`.

## 3. Lean module plan

The proposed files are small dependency layers.  A later file may import
earlier layers, but the cohomology core must not import Picard
representability.

```text
MazurTorsion/AlgebraicGeometry/Jacobian/
  Genus.lean
  RelativePicardFunctor.lean
  RelativePicardDescent.lean
  EulerCharacteristicDegree.lean
  SymmetricPower.lean
  UniversalEffectiveDivisor.lean
  RelativeRiemannRoch.lean
  CohomologyBaseChange.lean
  FiniteMapToProjectiveLine.lean
  FiniteGroupQuotient.lean
  PermutationPower.lean
  ProjectiveFiniteOrbit.lean
  GeometricallyIrreducibleDescent.lean
  PicardRepresentability.lean
  PicardIdentityComponent.lean
  PicardTangentSpace.lean
  PicardGeometry.lean
  AbelJacobi.lean
  AbelianRigidity.lean
  Albanese.lean
  LeanEval.lean
```

`LeanEval.lean` is the named downstream consumer and should expose a narrow
facade whose declarations match the benchmark:

```text
genus
jacobian
jacobianGrpObj
jacobianSmoothOfRelativeDimension
jacobianProper
jacobianGeometricallyIrreducible
abelJacobi
point_comp_abelJacobi
existsUnique_abelJacobi_comp
```

The benchmark submission then imports only Mathlib, so the final checked
facade and every non-Mathlib dependency must be copied into
`Submission/Helpers.lean` with attribution.  The copied code must remain
definitionally compatible with the declarations delegated from
`Submission.lean`.

## 4. Proof obligations by file

Each major definition comes with a concrete consumer and a theorem that
prevents it from becoming inert scaffolding.

* `Genus`: canonical `k`-module on `H¹(O_C)`, finiteness, and the natural
  number `finrank`; consumed by `PicardTangentSpace`.
* `RelativePicardFunctor`: base-change functor and abelian-group structure;
  consumed by descent.
* `RelativePicardDescent`: fppf sheaf condition; consumed by
  representability.
* `EulerCharacteristicDegree`: base-change-stable degree and degree-zero
  subfunctor; consumed by the identity component.
* `SymmetricPower`: quotient, effective divisors, universal family; consumed
  by representability and Albanese descent.
* `PicardRepresentability`: a representing scheme and Yoneda equivalence;
  consumed immediately by `PicardIdentityComponent`.
* `PicardIdentityComponent`: represented `Pic⁰` and group object; consumed by
  geometry and Abel--Jacobi.
* `PicardTangentSpace`: tangent-space equivalence with genuine `H¹`; consumed
  by the relative-dimension proof.
* `PicardGeometry`: smoothness, properness, geometric irreducibility, and
  relative dimension; consumed by the lean-eval facade.
* `AbelianRigidity`: origin-preserving morphisms are homomorphisms; consumed
  by Albanese uniqueness.
* `Albanese`: construction and uniqueness of the factor map; consumed by the
  lean-eval facade.

If an intermediate theorem is not yet proved, it belongs only in a registered
`Challenge/` contract and must not leak as an assumption into the final
facade.  Finishing the benchmark means eliminating every such contract from
the transitive dependency graph of `LeanEval.lean`.

## 5. Verification

For each layer:

1. build the smallest touched module with `LEAN_NUM_THREADS=1`;
2. inspect `#print axioms` for every exported theorem;
3. reject `sorry`, `admit`, custom axioms, `unsafe`, `partial`,
   `native_decide`, and local option changes;
4. run `python3 scripts/quality.py` before handoff;
5. in the generated lean-eval workspace, run its checker and `lake test`;
6. record peak RSS with `/usr/bin/time -v`; keep it below 50 GiB.

The final proof is complete only when both the Mazur facade and the standalone
lean-eval submission compile against their pinned Mathlib versions and the
comparator accepts all nine declarations.
