# Blueprint: Mazur's rational torsion bound

## 1. Exact goal and design decision

For a Weierstrass curve `E` over `ℚ` with `[E.IsElliptic]`, prove

```lean
(AddCommGroup.torsion (E⁄ℚ).Point :
  Set (E⁄ℚ).Point).ncard ≤ 16
```

This is the immutable statement in LeanPool's `Challenge/Mazur.lean`.
The project uses Lean `v4.32.0-rc1` and mathlib commit
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, matching the challenge.

The first architectural decision is to use the semantics of `Set.ncard`
honestly. If the torsion set is infinite, its `ncard` is zero. The deep
classification theorem is therefore needed only under an explicit
`Set.Finite` hypothesis. This removes Mordell--Weil finiteness from the
critical path without weakening or changing the target.

The second decision is to separate three layers:

1. pinned, reusable elliptic-curve and finite-group foundations;
2. the deep arithmetic theorem which rules out forbidden torsion orders and
   structures;
3. a tiny, stable final cardinality wrapper.

No unproved assumption may cross a layer boundary. Conditional lemmas are
allowed as honest implications, but they are not counted as solving a
dependency.

## 2. Current proved state

The package currently has 4,050 integrated lines of Lean under
`MazurTorsion/` and
builds without warnings or unproved declarations.

### 2.1 Cardinality bridge

`GroupTheory/ClassificationCardinality.lean` defines:

```lean
def cyclicOrders : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}

def bicyclicParameters : Finset ℕ :=
  {1, 2, 3, 4}

def HasMazurClassification (E : WeierstrassCurve ℚ) : Prop := ...

def HasMazurClassificationIfFinite
    (E : WeierstrassCurve ℚ) : Prop := ...
```

and proves:

```lean
torsion_ncard_le_of_classification
torsion_ncard_le_of_classification_if_finite
```

The latter performs the exact finite/infinite split for the stronger
classification route. The shorter numerical endpoint is described in
Section 2.3.

### 2.2 Verified arithmetic foundations

The following attributed Apache-2.0 files are integrated and compile on the
exact pin.

* `Foundations/TwoTorsion.lean`

  * finiteness of the points killed by two;
  * `#E[2](F) ≤ 4` in characteristic different from two;
  * `#E[4](F) ≤ 16`;
  * no injection `(ZMod 2)^3 → E(F)`.

* `Foundations/ThreeTorsion.lean`

  * the exact `Ψ₃` torsion dictionary over `ℚ`;
  * `#E[3](ℚ) ≤ 9`;
  * no injection `(ZMod 3)^2 → E(ℚ)`.

* `Foundations/FullFourTorsion.lean`

  * the explicit halving-square identities;
  * no injection `(ZMod 4)^2 → E(ℚ)`.

These theorems are structural inputs. In particular, `#E[4] ≤ 16` is not
mistaken for a bound on all rational torsion.

### 2.3 Compiled finite-group reduction

`GroupTheory/ForbiddenEmbeddings.lean` provides the common negative
embedding predicate and transport through equivalences, subgroups, and
injective maps. `GroupTheory/FiniteClassification.lean` proves:

```lean
factor_count_lt_of_forbidden_pi
factor_count_lt_two_of_forbidden_square
factor_count_lt_three_of_forbidden_cube
hasMazurGroupShape_of_rankTwo
card_le_sixteen_of_rankTwo
card_le_sixteen_of_allowed_orders_and_forbidden
```

The first three declarations connect mathlib's elementary-divisor
decomposition to rank bounds. The next two completely discharge the
finite-group classification once an invariant-factor presentation
`G ≃+ ZMod m × ZMod n` with `m ∣ n` is supplied. The final theorem removes
that hypothesis entirely: it decomposes an arbitrary finite abelian group
into prime-power cyclic factors, bounds their multiplicities using the
forbidden embeddings, handles the two mixed CRT patterns explicitly, and
proves `Nat.card G ≤ 16`.

`Arithmetic/CardinalityReduction.lean` combines the proved `2`, `3`, and
`4` obstructions with the global theorem. Its endpoint

```lean
torsion_ncard_le_of_arithmetic_inputs
```

proves the exact LeanPool inequality from only the point-order theorem, the
`5`- and `7`-square exclusions, and the two exceptional product exclusions.
It performs the finite/infinite `Set.ncard` split internally and needs
neither a rank-two presentation nor Mordell--Weil. The older
`Arithmetic/RankTwoReduction.lean` is retained because it proves the
stronger fifteen-group shape from a natural geometric interface.

### 2.4 Roots of unity and odd-prime discriminants

`NumberTheory/RationalRootsOfUnity.lean` proves that a rational number whose
nonzero natural power is one equals `1` or `-1`, and that a primitive
rational root of unity has order at most two.

`Foundations/OddPrimeFullTorsion.lean` proves from first principles that a
split rational polynomial has square discriminant. It also constructs all
abscissa representatives needed to show that full rational `5`- or
`7`-torsion makes `preΨ' 5` or `preΨ' 7` split.

`Foundations/DivisionPolynomialRootCriterion.lean` now proves the two
previously missing scalar-multiplication implications:

```lean
hasDivisionPolynomialRootCriterion_five
hasDivisionPolynomialRootCriterion_seven
```

The proof derives the abscissas of `2P`, `3P`, and `4P` from the affine
group law, proves the relevant low-level `Φ`/`ΨSq` identities, and applies
the elliptic-divisibility-sequence cross identities at five and seven.

Consequently, `Arithmetic/OddPrimeObstructions.lean` exposes

```lean
forbidsEmbedding_zmod_five_square_of_discr
forbidsEmbedding_zmod_seven_square_of_discr
rationalTorsion_forbids_zmod_five_square_of_discr
rationalTorsion_forbids_zmod_seven_square_of_discr
```

The only remaining inputs in this track are now the two standard fixed-level
discriminant identities

\[
\operatorname{disc}(\mathrm{pre}\Psi'_5)=5^{11}\Delta^{22},
\qquad
\operatorname{disc}(\mathrm{pre}\Psi'_7)=-7^{23}\Delta^{92}.
\]

Neither identity is postulated as a declaration.

### 2.5 Change of Weierstrass model

The attributed Apache-2.0 port
`EllipticCurve/VariableChange.lean` proves the explicit additive
equivalence

```lean
WeierstrassCurve.Affine.Point.equivVariableChange :
  (C • W).toAffine.Point ≃+ W.toAffine.Point
```

and the coordinate formulas behind it. This supplies the transport needed
to replace an arbitrary rational Weierstrass equation by short or
two-torsion normal forms without losing point orders or subgroup
obstructions. `GroupTheory/TorsionEquiv.lean` restricts any additive
equivalence to an equivalence of its torsion subgroups and records
preservation of additive order.

### 2.6 Exceptional-level support

`GroupTheory/CyclicKernelExtension.lean` proves that a finite extension of
an even cyclic group by a two-element kernel is cyclic when every element
killed by two lies in that kernel. This is the pure group-theoretic core of
the cyclic `20`- and `24`-isogeny construction.

`NumberTheory/RatNorthcott.lean` proves directly from
`Rat.logHeight₁_eq_log_max` that rational numbers of bounded logarithmic
height form a finite set, and installs the corresponding `Northcott`
instance. This closes the exact-pin rational Northcott gap in a future
specialized Mordell--Weil/descent certificate.

## 3. Selected proof architecture

The shortest stable dependency graph for the exact challenge is:

```text
mathlib affine points / division polynomials / finite abelian groups
                              │
                              ▼
       low full-level torsion obstructions [partly done]
                              │
                              ▼
       finite-abelian forbidden-embedding classification
                              │
                ┌─────────────┴─────────────┐
                ▼                           ▼
       rational point-order theorem   exceptional product exclusions
                │                    C₂×C₁₀ and C₂×C₁₂
                └─────────────┬─────────────┘
                              ▼
             finite rational torsion classification
                              │
                              ▼
       `torsion_ncard_le_of_classification_if_finite` [done]
                              │
                              ▼
                  `Solution/Mazur.lean`
```

This route is preferable to adding Mordell--Weil merely to prove that
torsion is finite. It is also preferable to Merel's general uniform bound,
which is much less sharp and requires a larger formal apparatus.

## 4. Exact finite-group interface

### 4.1 Common predicate

Create `GroupTheory/ForbiddenEmbeddings.lean` with:

```lean
def ForbidsEmbedding (A G : Type*) [AddCommGroup A] [AddCommGroup G] : Prop :=
  ∀ f : A →+ G, ¬ Function.Injective f
```

Add transport lemmas under additive equivalence, products, subgroups, and
composition. Keep this file entirely independent of elliptic curves.

### 4.2 Finite classification theorem

Create `GroupTheory/FiniteClassification.lean`. Its central theorem should
have the following mathematical interface:

```lean
theorem hasMazurShape_of_forbidden_embeddings
    (G : Type*) [AddCommGroup G] [Finite G]
    (horder : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (h222 : ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) G)
    (h33  : ForbidsEmbedding (ZMod 3 × ZMod 3) G)
    (h44  : ForbidsEmbedding (ZMod 4 × ZMod 4) G)
    (h55  : ForbidsEmbedding (ZMod 5 × ZMod 5) G)
    (h77  : ForbidsEmbedding (ZMod 7 × ZMod 7) G)
    (h210 : ForbidsEmbedding (ZMod 2 × ZMod 10) G)
    (h212 : ForbidsEmbedding (ZMod 2 × ZMod 12) G) :
    MazurGroupShape G
```

`MazurGroupShape` should be generic in `G`; the elliptic-curve-specific
`HasMazurClassification` can then be a specialization.

Why the hypotheses suffice:

1. allowed element orders make the exponent one of
   `{1,…,10,12}`;
2. excluding `(C₂)^3` bounds the two-primary rank by two;
3. excluding `(C₃)^2`, `(C₅)^2`, and `(C₇)^2` makes every odd primary
   component cyclic;
4. excluding `(C₄)^2` restricts the noncyclic two-primary component to the
   shape `C₂ × C_{2^r}` with `r≤3`;
5. coprime primary components recombine, yielding either `C_b` or
   `C₂ × C_b` with even
   `b∈{2,4,6,8,10,12}`;
6. the last two explicit obstructions remove `b=10,12`.

The implementation should use
`AddCommGroup.equiv_directSum_zmod_of_finite` and small helper lemmas about
prime-power factors. It must not reproduce unlicensed source from another
repository.

If a direct shape theorem makes the API unwieldy, an acceptable intermediate
theorem is the strictly weaker conclusion `Nat.card G ≤ 16`; the later
elliptic layer can then bypass the explicit fifteen-group equivalence.

## 5. Full-level torsion foundations

### 5.1 Completed small levels

Keep the existing two-, three-, and four-torsion files separate because
their proofs use different coordinate arguments and are already a natural
size.

### 5.2 Odd prime full torsion

Create `Foundations/OddPrimeFullTorsion.lean` with:

```lean
not_injective_zmod_five_square
not_injective_zmod_seven_square
```

There are two plausible routes.

#### Route A: Weil pairing

Develop a general `EllipticCurve/WeilPairing.lean` and prove that full
rational `p`-torsion produces a primitive rational `p`-th root of unity.
Then a common roots-of-unity lemma excludes every odd prime at once.

This is mathematically clean and ultimately needed by the invariant-factor
proof, but it requires a new pairing construction absent from pinned
mathlib. The rational roots-of-unity endpoint itself is now implemented in
`NumberTheory/RationalRootsOfUnity.lean`; only the elliptic Weil-pairing
layer remains on this route.

#### Route B: fixed division-polynomial discriminants

Full rational `p`-torsion makes the `p`-division polynomial split completely
over `ℚ`. Prove:

* a split separable polynomial has square discriminant;
* the discriminant formula for `ψ_p`;
* for `p=5,7`, that formula is a nonsquare in `ℚ`.

This avoids general group schemes but requires a substantial explicit
polynomial certificate. It is a bounded medium-to-high-risk task and should
be attempted only if its final proof is shorter than a reusable Weil-pairing
layer.

Do not use computation whose correctness is hidden in an evaluator. Any
fixed-prime calculation must leave a kernel-checked algebraic certificate.

## 6. Rational point-order theorem

The public result should live in `Arithmetic/PointOrder.lean`:

```lean
theorem rational_torsion_order_mem_cyclicOrders
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hP : P ∈ AddCommGroup.torsion (E⁄ℚ).Point) :
    addOrderOf P ∈ cyclicOrders
```

The detailed subgraph is:

```text
Kubert/TateNormalForm
        │
        ▼
Kubert/LowLevels
  no orders 14,15,16,18,20,21,24,25,27,35,49
        │
        ├───────────────► MazurTate/OrderThirteen
        │
        ▼
Mazur/PrimeOrder
  no remaining rational prime-order point
        │
        ▼
Mazur/PointOrder
  divisor closure leaves {1,…,10,12}
```

Kubert's Theorem IV.1.2 is the mathematical reduction to a rational
prime-order subgroup of large level. The small-level files should expose
mathematical theorems, not raw computer-algebra transcripts. Rank-zero,
torsion, or cusp computations must be accompanied by checkable descent and
enumeration certificates.

## 7. Prime-level Mazur layer

This is the dominant, multi-year-risk dependency. Pinned mathlib does not
currently provide its main objects.

### 7.1 Required lower-level modules

```text
EllipticCurve/Torsion/WeilPairing.lean
EllipticCurve/Isogeny/Basic.lean
EllipticCurve/Isogeny/Quotient.lean
EllipticCurve/Isogeny/Dual.lean
EllipticCurve/FiniteField/Hasse.lean

EllipticCurve/NeronModel/Basic.lean
EllipticCurve/NeronModel/ComponentGroup.lean
EllipticCurve/NeronModel/TorsionSpecialization.lean

FiniteFlatGroupScheme/Basic.lean
FiniteFlatGroupScheme/ConnectedEtale.lean
FiniteFlatGroupScheme/OortTate.lean
FiniteFlatGroupScheme/Raynaud.lean

ModularCurve/X0/Moduli.lean
ModularCurve/X0/IntegralModel.lean
ModularCurve/X0/Cusps.lean
ModularCurve/X0/Jacobian.lean
ModularCurve/X0/Hecke.lean
ModularCurve/X0/EisensteinIdeal.lean
ModularCurve/X0/EisensteinQuotient.lean

Cyclotomic/UnramifiedCharacterExtension.lean
AbelianVariety/Shafarevich.lean
```

Tau Ceti's future Jacobian work and later mathlib developments should be
monitored before independently building every generic algebraic-geometric
layer.

### 7.2 Stable theorem interfaces

`ModularCurve/X0/EisensteinQuotient.lean` should eventually expose:

```lean
eisensteinQuotient_mordellWeil_finite
cuspDifference_exactOrder
cuspDifference_ne_zero
```

Its internal dependencies include the Hecke algebra quotient
`𝕋/I ≃ ZMod (numerator ((N-1)/12))`, the cusp and Shimura subgroups,
Gorenstein/local-principality results at Eisenstein primes, finite-flat
kernel control, component groups at `N`, and fppf descent.

`Mazur/PrimeOrder.lean` should expose:

```lean
semistable_of_rational_prime_torsion
torsion_specializes_outside_identity_at_two
torsion_specializes_outside_identity_at_three
torsion_specializes_outside_identity_at_bad
divisionField_unramified
divisionSequence_split
no_rational_point_of_prime_order
```

The proof sequence is:

1. use Néron models and Raynaud uniqueness to exclude additive reduction;
2. use Hasse and the multiplicative identity component to show the point is
   outside the identity component at two and three;
3. map the integral `X₀(N)` point to the Eisenstein quotient and use
   specialization in two residue characteristics to prove the same at every
   bad prime;
4. conclude that the `N`-division field over `ℚ(ζ_N)` is everywhere
   unramified;
5. exclude the inverse-cyclotomic unramified extension by
   Herbrand--Kummer and `B₂=1/6`;
6. split `0 → ZMod N → E[N] → μ_N → 0`;
7. iterate quotient isogenies and apply Shafarevich finiteness to get the
   final contradiction.

Do not insert formal-immersion dependencies into this path. Formal immersion
is the later Kamienny--Merel method and is strategically larger for the
degree-one sharp theorem.

## 8. Exceptional product cases

Create:

```text
GroupTheory/CyclicKernelExtension.lean
Foundations/Isogeny/TwoIsogeny.lean
EllipticCurve/Isogeny/CyclicKernel.lean
ModularCurve/X0/Levels20And24.lean
Arithmetic/TwoIsogenyDescent.lean
Arithmetic/ExceptionalProducts.lean
```

The target declarations are:

```lean
cyclic_isogeny_twenty_of_two_ten
cyclic_isogeny_twenty_four_of_two_twelve
x0_20_rational_points_are_cusps
x0_24_rational_points_are_cusps
not_injective_zmod_two_prod_ten
not_injective_zmod_two_prod_twelve
```

For `C₂ × C_{2n}`, quotient by the independent rational `C₂`, compose the
dual degree-two isogeny with the quotient by `C_{2n}`, and prove that the
composite kernel is cyclic of order `4n`. For `n=5,6`, this gives a
noncuspidal rational point of `X₀(20)` or `X₀(24)`.

The pure finite-group core of cyclicity should be isolated first. If
`f : A →+ B` has a two-element kernel, `g.ker` is cyclic of even order, and
every point of order dividing two in `(g.comp f).ker` lies in `f.ker`, then
`(g.comp f).ker` is cyclic. This avoids mixing the elementary lifting
argument with the later quotient-isogeny API.

Use explicit genus-one models:

\[
X_0(20):y^2=x^3+x^2+4x+4,
\qquad
X_0(24):y^2=x^3-x^2-4x+4.
\]

The certificate modules must prove rank zero, compute the rational torsion
groups `C₆` and `C₂×C₄`, and match all six or eight rational points to
cusps. The isomorphism from the modular moduli problem to the explicit model
must also be proved; recognizing only the abstract elliptic curve is not
enough.

### 8.1 Specialized two-isogeny descent certificate

Translate the two models by `u=x+1` and `u=x-1`:

\[
E_{20}: y^2=u(u^2-2u+5),\qquad
E_{24}: y^2=u(u^2+2u-3).
\]

For

\[
E_{a,b}:y^2=x(x^2+ax+b)
\]

define the two-isogenous curve

\[
E'_{a,b}:Y^2=X(X^2-2aX+a^2-4b)
\]

and prove the explicit degree-two isogeny and dual formulas. Define the
descent map to rational square classes by

\[
\alpha_E(O)=1,\quad \alpha_E((0,0))=b,\quad
\alpha_E((x,y))=x.
\]

The main reusable certificate says that a square class in the image has a
squarefree representative `d ∣ b` and coprime integers satisfying

\[
V^2=dU^4+aU^2W^2+(b/d)W^4. \tag{1}
\]

For `E₂₀`, positivity and a two-adic parity argument give

\[
\operatorname{im}\alpha_{E_{20}}=\{1,5\},\qquad
\operatorname{im}\alpha_{E'_{20}}=\{1,-1\}.
\]

For `E₂₄`, explicit points and the same elementary arguments give

\[
\operatorname{im}\alpha_{E_{24}}=\{1,-1,3,-3\},\qquad
\operatorname{im}\alpha_{E'_{24}}=\{1\}.
\]

In both cases the product of image sizes is four. The standard index
identity

\[
|\operatorname{im}\alpha_E|\,|\operatorname{im}\alpha_{E'}|
  =4\cdot 2^{\operatorname{rank}E(\mathbb Q)}
\]

therefore proves rank zero. The rational point sets are then pinned down by
ordinary finite-field reduction:

* `#E₂₀(𝔽₃)=6`, yielding
  `O,(-1,0),(0,±2),(4,±10)` on the original model;
* `#E₂₄(𝔽₅)=8`, yielding
  `O,(-2,0),(0,±2),(1,0),(2,0),(4,±6)`.

The cusp-count formula gives six and eight rational cusps respectively, so
after the model identification cardinality alone proves that every rational
point is a cusp.

Michael Stoll's Apache-2.0 point-variable-change code has been ported as
`EllipticCurve/VariableChange.lean`. His reduction and 2-descent files are
compatible with the exact pin after small API changes, but a narrow
rational specialization is preferable to importing their roughly
22,700-line dependency cone.

### 8.2 Preferred direct formal route

The modular interpretation remains the clean informal proof, but it brings
large missing quotient, dual-isogeny, modular-curve, model-identification,
and cusp layers. For the Lean implementation, first attempt direct
Tate-normal-form descents:

* `C₂ × C₁₀`: impose full rational two-torsion on the order-five Tate
  normal form, make the cubic discriminant a square, and finish by quartic
  infinite descent;
* `C₂ × C₁₂`: combine the compiled halving-square identities with a
  specialized quartic descent.

If successful, these proofs discharge the two forbidden embeddings directly
and leave the general `X₀(20/24)` construction as valuable, non-critical
infrastructure.

## 9. Arithmetic assembly

`Arithmetic/CardinalityReduction.lean` is now the compiled numerical
assembly. It exposes the exact five-input endpoint:

```lean
theorem torsion_ncard_le_of_arithmetic_inputs
    (horders : ∀ x : RationalTorsion E,
      addOrderOf x ∈ cyclicOrders)
    (h55 : ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E))
    (h77 : ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E))
    (h210 : ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E))
    (h212 : ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E)) :
    torsionSet.ncard ≤ 16
```

The remaining arithmetic assembly steps are:

1. invoke the rational point-order theorem for every torsion element;
2. transfer the proved full-level non-embedding results into the torsion
   subtype;
3. invoke the two exceptional-product exclusions;
4. call the compiled five-input endpoint.

No global `Fintype` or Mordell--Weil theorem should leak into the API.

## 10. Final LeanPool file

Only after the dependency cone is clean, add `Solution/Mazur.lean` in a
LeanPool-compatible checkout:

```lean
import MazurTorsion.Arithmetic.CardinalityReduction
import MazurTorsion.Arithmetic.ExceptionalProducts
import MazurTorsion.Arithmetic.PointOrder

namespace Challenge.Mazur

open scoped WeierstrassCurve.Affine

theorem torsion_ncard_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point :
      Set (E⁄ℚ).Point).ncard ≤ 16 :=
  MazurTorsion.torsion_ncard_le_of_arithmetic_inputs E
    (MazurTorsion.rational_torsion_order_mem_cyclicOrders E)
    (MazurTorsion.rationalTorsion_forbids_zmod_five_square E)
    (MazurTorsion.rationalTorsion_forbids_zmod_seven_square E)
    (MazurTorsion.rationalTorsion_forbids_zmod_two_prod_ten E)
    (MazurTorsion.rationalTorsion_forbids_zmod_two_prod_twelve E)

end Challenge.Mazur
```

The exact final syntax may change with namespace choices, but the dependency
shape should remain this small.

## 11. Milestones and risk

| Milestone | Deliverable | Status | Risk |
|---|---|---:|---:|
| M0 | Exact pin, isolated package, green build | done | low |
| M1 | Classification-to-cardinality wrapper and finite/infinite split | done | low |
| M2 | `E[2]`, `E[3]`, `E[4]` bounds/full-level obstructions | done | low |
| M3 | Generic forbidden-embedding finite-group classification | done, including global numerical theorem | low |
| M4 | Full rational `5`- and `7`-torsion obstructions | root criteria done; two fixed discriminant identities remain | medium--high |
| M5 | Exceptional products / `X₀(20),X₀(24)` certificates | explicit descent designed; direct Tate-normal-form route selected | high |
| M6 | Kubert small-level and order-thirteen exclusions | planned | high |
| M7 | Mazur prime-level Eisenstein/Néron/cyclotomic argument | planned | extremely high |
| M8 | Arithmetic assembly and exact `Solution/Mazur.lean` | numerical assembly done; blocked on M4--M7 | low once dependencies exist |

The risk labels describe missing library depth, not permission to weaken a
statement. A milestone becomes done only when its complete dependency cone
passes the axiom audit.

## 12. Build, source, and resource invariants

Every tracked Lean declaration must be proved without:

* unproved placeholders or new axioms;
* unsafe or partial definitions;
* local/global option overrides;
* `native_decide`.

Ordinary kernel-reduced `decide` is permitted for genuinely tiny finite
facts, but explicit algebraic lemmas are preferred when they produce a
better reusable API.

Verification commands:

```sh
LEAN_NUM_THREADS=1 lake build MazurTorsion
rg -n '\b(sorry|admit|axiom|unsafe|partial)\b|set_option|native_decide' \
  MazurTorsion MazurTorsion.lean --glob '*.lean'
git diff --check -- mazur-torsion
```

Builds are serialized. `/usr/bin/time -l` is used on full checks. The largest
observed maximum resident set so far is approximately 2.25 GB, safely below
the 50 GB limit. A broken build is the highest-priority issue and must be
repaired before any new theorem work.

No source file should exceed LeanPool's 10,000-line limit. Long proofs should
be decomposed into named lemmas, normally keeping individual theorem bodies
below 200 lines.

## 13. Checkpoint discipline

The workspace contains unrelated McKay changes. Every checkpoint must stage
only the Mazur subtree:

```sh
git add -- mazur-torsion
git diff --cached --check
git diff --cached --stat
git commit -m "checkpoint: advance Mazur torsion formalization"
git push origin codex/mazur-torsion
```

Before committing, rebuild the package and rerun the source audit. Push at
least once every twelve hours while the goal remains active; earlier
milestone checkpoints are encouraged. Never stage or modify the unrelated
dirty files.
