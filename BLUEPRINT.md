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

The latest integrated package has 24,328 project-specific lines of Lean under
`MazurTorsion/`, plus the attributed 14,040-line exact-pin reduction cone
under `EllipticCurves/`, and builds without warnings or unproved
declarations.

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

proves the exact LeanPool inequality from only the point-order theorem.
The low-level, full rational `5`- and `7`-torsion, `C₂ × C₁₀`, and
`C₂ × C₁₂` exclusions are all discharged internally.
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
forbidsEmbedding_zmod_five_square
forbidsEmbedding_zmod_seven_square_of_discr
forbidsEmbedding_zmod_seven_square
rationalTorsion_forbids_zmod_five_square_of_discr
rationalTorsion_forbids_zmod_five_square
rationalTorsion_forbids_zmod_seven_square_of_discr
rationalTorsion_forbids_zmod_seven_square
```

`Foundations/DivisionPolynomialDiscriminantFive.lean` and
`Foundations/DivisionPolynomialDiscriminantSeven.lean` prove both fixed-level
identities unconditionally:

\[
\operatorname{disc}(\mathrm{pre}\Psi'_5)=5^{11}\Delta^{22},
\qquad
\operatorname{disc}(\mathrm{pre}\Psi'_7)=-7^{23}\Delta^{92}.
\]

Each proof translates to `b₂=0`, checks a sparse chain of
division-polynomial syzygies, computes the resultant from the cubic
discriminant, and transports back using `Polynomial.resultant_taylor`.
The seventh-level proof separately handles the singular short model before
transport, so its universal theorem does not require an ellipticity
hypothesis. Full rational `5`- and `7`-torsion are therefore excluded
without any arithmetic input. No discriminant identity is postulated as a
declaration.

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

`Kubert/TateNormalForm.lean` supplies the reusable Tate normal curve,
the scaling equivalence from an arbitrary rational point with
`3P ≠ 0`, and checked coordinate formulas for `2P`, `3P`, and `4P`.
`Kubert/TateNormalFormMultiples.lean` adds a reusable recurrence for
`Q+(0,0)`, an explicit formula for `5P`, and a recurrence-defined formula
for `6P`, with every denominator hypothesis exposed.
`Arithmetic/ExceptionalTwoTen.lean` imports this common layer rather than
carrying a private duplicate of the normalization.

`Arithmetic/ExceptionalTwoTen.lean` completes the direct geometric and
denominator reduction

\[
C_2\times C_{10}\hookrightarrow E(\mathbb Q)
\Longrightarrow
e^2=X^4-11X^2Y^2-Y^4
\]

for coprime nonzero integers `X,Y`. It proves Tate normalization with the
twelfth-power discriminant scale retained, derives the order-five diagonal
`b=c`, proves that full rational two-torsion makes `E.Δ` a square, and
performs the complete rational-to-integral sign analysis.

`NumberTheory/ExceptionalQuarticDescent.lean` closes the resulting
Diophantine leaf unconditionally. Its elementary descent factors

\[
D_+D_-=125z^4,\qquad D_++D_-=X^2-22z^2,
\]

proves the two positive factors coprime, splits their fourth powers,
parametrizes the resulting primitive Pythagorean triple, and constructs a
new quartic solution with strictly smaller `Int.natAbs` of its second
coordinate. Thus
`ExceptionalTwoTen.noExceptionalQuartic`,
`forbidsEmbedding_zmod_two_prod_ten`, and the rational-torsion restriction
are proved without any remaining hypothesis.

`Arithmetic/ExceptionalTwoTwelve.lean` completes the direct reduction

\[
C_2\times C_{12}\hookrightarrow E(\mathbb Q)
\Longrightarrow
w^2=(t^2-1)(9t^2-1),
\]

with `t,w` nonzero and all three degenerate factors excluded. It also
kernel-checks the map to

\[
Y^2=(X-10)(X-6)(X+6)
\]

and reduces the obstruction to the exact affine `X`-coordinate list
`{-6,2,6,10,18}`. The linear scaling `X=4x+2`, `Y=8y` identifies this
cubic with the selected `X₀(24)` model
`y²=x³-x²-4x+4`; the specialized two-isogeny descent certificate in
Section 8.1 now proves rank zero and finiteness. Its remaining leaf is the
sharp fixed-curve bound of eight rational points.
`Arithmetic/ExceptionalProducts.lean` packages both reductions as
`ForbidsEmbedding` statements on rational torsion. No isogeny or
modular-curve moduli API is needed on this direct path.

`GroupTheory/CyclicKernelExtension.lean` proves that a finite extension of
an even cyclic group by a two-element kernel is cyclic when every element
killed by two lies in that kernel. This is the pure group-theoretic core of
the cyclic `20`- and `24`-isogeny construction.

`NumberTheory/RatNorthcott.lean` proves directly from
`Rat.logHeight₁_eq_log_max` that rational numbers of bounded logarithmic
height form a finite set, and installs the corresponding `Northcott`
instance.

The attributed port `Foundations/NaiveHeightDescent.lean` proves the
approximate parallelogram law for naïve height and exposes

```lean
WeierstrassCurve.Affine.fg_point_of_finiteIndex_two
```

so a curve-specific proof that `2E(ℚ)` has finite index implies finite
generation at the exact pin. `GroupTheory/IndexNSmulFG.lean`, another
narrow attributed port, proves

```lean
AddSubgroup.index_range_nsmul_of_fg
```

or
\([G:nG]=n^{\operatorname{rank}G}\#G[n]\) for every finitely generated
commutative group.

`NumberTheory/ExceptionalCubicDescent.lean` applies these tools to

\[
E_{24}:y^2=u(u^2+2u-3).
\]

It proves that the dual abscissa is always a square, that the abscissa on
`E₂₄` lies in one of the four square classes `1,-1,3,-3`, and that every
rational point belongs to one of

\[
2E(\mathbb Q),\quad D+2E(\mathbb Q),\quad
F+2E(\mathbb Q),\quad T+2E(\mathbb Q).
\]

Thus `[E(ℚ):2E(ℚ)]≤4`. The curve has exactly four rational points killed by
two. Finite generation and the index formula force rank zero; the point
group is therefore finite.  The descent module exports the final
enumeration implication

```lean
exceptionalCubicIsTrivial_of_point_card_le_eight
```

The exact-pin reduction port in `EllipticCurves/` constructs the reduction
homomorphism at the good prime `5`, proves it injective on the now-finite
rational point group, and computes the reduced point count as eight using
the concrete `ZMod 5` model.  The bridge
`NumberTheory/ExceptionalCubicReduction.lean` therefore proves both
`point_card_le_eight` and the unconditional
`ExceptionalCubic.exceptionalCubicIsTrivial`.

`NumberTheory/QuarticDifferenceDescent.lean` proves the precise
nondegenerate form of Fermat's other quartic:

```lean
sq_ne_quartic_sub_quartic
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2
```

The `hz` hypothesis is essential because `x=y=1,z=0` is a degenerate
solution. The proof normalizes a primitive Pythagorean triple, treats both
parities, performs the second parametrization needed in the even branch,
and descends to a strictly smaller hypotenuse.

`Kubert/OrderSixteenReduction.lean` uses that endpoint to close the whole
order-sixteen branch unconditionally.  It first translates
`T=8R` to `(0,0)` and completes the square, giving

\[
Y^2=X^3+aX^2+bX.
\]

For the chain `R,2R,4R,8R`, the checked denominator-free duplication
identity

\[
X(2S)(2Y(S))^2=(X(S)^2-b)^2
\]

shows that the successive nonzero abscissas are squares after scaling.
Eliminating those squares produces a nondegenerate rational point on

\[
V^2=(N^2-1)(N^2+1)(N^2+2N-1),\qquad N\ne0,\quad N^2\ne1.
\]

After writing `N=m/n` in lowest terms, opposite parity makes the three
factors pairwise coprime and produces
`x⁴-y⁴=z²`, contradicting `sq_ne_quartic_sub_quartic`.  If `m,n` are
both odd, the half-sum/half-difference substitution produces
`x⁴+y⁴=z²`, contradicting mathlib's `not_fermat_42`.  The exported final
theorem is

```lean
no_rational_point_of_order_sixteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : E.toAffine.Point) (hR : addOrderOf R = 16) : False
```

There is no remaining rational-point boundary at level sixteen.

## 3. Selected proof architecture

The shortest stable dependency graph for the exact challenge is:

```text
mathlib affine points / division polynomials / finite abelian groups
                              │
                              ▼
       low full-level torsion obstructions [done]
                              │
                              ▼
       finite-abelian forbidden-embedding classification
                              │
                ┌─────────────┴─────────────┐
                ▼                           ▼
       rational point-order theorem   exceptional product exclusions
                │                    C₂×C₁₀ [done],
                │                    C₂×C₁₂ [done]
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

The fixed division-polynomial route is complete.
`Foundations/OddPrimeFullTorsion.lean` and
`Arithmetic/OddPrimeObstructions.lean` expose:

```lean
not_injective_zmod_five_square
not_injective_zmod_seven_square
```

Full rational `p`-torsion makes the `p`-division polynomial split completely
over `ℚ`. The implementation proves:

* a split separable polynomial has square discriminant;
* the scalar-multiplication root criteria for `ψ₅` and `ψ₇`;
* the universal discriminant identities for `ψ₅` and `ψ₇`;
* the rational nonsquare contradictions at five and seven.

The large seventh-level calculation is expressed as sparse polynomial
syzygies and resultants checked by the kernel. A general Weil-pairing
construction remains useful infrastructure, but it is no longer on the
critical path for the two full-level obstructions used by the cardinality
wrapper.

## 6. Rational point-order theorem

The public result should live in `Arithmetic/PointOrder.lean`:

```lean
theorem rational_torsion_order_mem_cyclicOrders
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hP : P ∈ AddCommGroup.torsion (E⁄ℚ).Point) :
    addOrderOf P ∈ cyclicOrders
```

The purely arithmetic divisor reduction is already compiled in
`Arithmetic/PointOrderReduction.lean`. It defines

```lean
kubertForbiddenOrders =
  {14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49}
```

and proves:

```lean
exists_prime_or_kubertForbiddenOrder_dvd
addOrderOf_mem_cyclicOrders_of_order_obstructions
```

For a positive integer outside `cyclicOrders`, choose its least excluded
divisor. If it is prime, it is at least eleven. If it is composite, both
proper factors lie in the allowed list and hence are at most twelve, so the
minimal divisor is below 145; a small kernel-reduced finite classification
gives exactly the displayed eleven values. For a finite-order group
element, multiplication by the complementary quotient extracts an element
of exactly the chosen divisor order. This completes the divisor-closure
step without assuming any of the geometric exclusions.

`Arithmetic/PointOrder.lean` is the incremental rational specialization.
It defines

```lean
remainingKubertForbiddenOrders = {18, 21, 25, 27, 35, 49}
```

and its strongest current public theorem

```lean
rationalTorsion_orders_mem_cyclicOrders_of_remaining_obstructions
```

uses the unconditional level-fourteen, level-fifteen, level-sixteen,
level-twenty, and level-twenty-four obstructions internally.  Consequently,
the current callback boundary consists of prime orders at least eleven and
only the displayed six composite orders; a downstream caller cannot
accidentally reintroduce any completed case as an assumption.  The earlier
incremental interfaces remain available for compatibility.

`Kubert/TateNormalForm.lean` and
`Kubert/TateNormalFormMultiples.lean` are also compiled. They construct the
normal curve and scaling equivalence, verify coordinate formulas through
`5P`, and expose a checked recurrence for `6P` and later multiples. The
shared `Kubert/OrderNineReduction.lean` proves that exact order nine forces

\[
c^5+c^4+(1-b)c^3-3bc^2+3b^2c-b^3=0.
\]

It obtains this by comparing the checked abscissas in `5P=-4P`, with
`b≠0`, `c≠0`, and `b≠c` proved from the exact order rather than assumed.
Its scaled Tate certificate is the common first stage of the order-eighteen
and order-twenty-seven branches.

`Kubert/OrderEighteenReduction.lean` performs the next order-eighteen step.
For a point `Q` of exact order eighteen, `2Q` has exact order nine and
`9Q` has exact order two. After normalizing `2Q`, the module retains both
facts on the same Tate curve:

```lean
orderNinePolynomial b c = 0
tateTwoDivisionPolynomial b c r = 0
```

where

\[
\operatorname{tateTwoDivisionPolynomial}(b,c,r)
=4r^3+((1-c)^2-4b)r^2+2b(c-1)r+b^2.
\]

All order and denominator side conditions, and the twelfth-power
discriminant scale, are checked.

`Kubert/OrderEighteenModel.lean` now performs the elimination.  Rewriting
the order-nine equation as

\[
c^5-(b-c)c^3-(b-c)^3=0
\]

and setting `d=c²/(b-c)` gives

\[
c=d^2(d-1),\qquad b=c(d^2-d+1).
\]

For a root `r` of the two-division cubic, put

\[
s=\frac{(1-c)r-b}{2rc}.
\]

Then

\[
(2s+1)\bigl(d^2(d-1)s^2-(d^2-d+1)\bigr)-s^2=0. \tag{*}
\]

The module proves `d≠0,1`, `r≠0`, and `1+ds≠0`, and verifies the rational
change

\[
X=\frac{d-s+2ds}{1+ds},\qquad
Y=2Xd-(X^3-2X^2+3X-1).
\]

It produces the explicit genus-two point

\[
Y^2=X^6-4X^5+10X^4-10X^3+5X^2-2X+1
\]

with `X≠0,1`.  Thus only the rational-point classification of this
genus-two model remains; the full algebraic path from a point of exact
order eighteen is compiled.

`NumberTheory/XOneEighteenFiniteField.lean` adds two independent checked
boundaries.  Modulo five, the sextic is
`X⁶+X⁵+3X+1`; an explicit Bézout identity with its derivative
`X⁵+3` proves separability and squarefreeness.  Complete ordinary
enumeration gives four affine points, all over `X=0,1`, and the monic
even-degree infinity chart has two smooth directions.  The resulting
six-element type is deliberately only a finite-field certificate: no
projective equivalence, Jacobian reduction, or injection of rational points
is inferred from it.

Over the rationals the same file checks the order-three automorphism

\[
(X,Y)\longmapsto
\left(\frac1{1-X},-\frac{Y}{(1-X)^3}\right).
\]

On `X≠0,1`, its third iterate is the identity.  The invariant functions

\[
u=\frac{X^3-3X+1}{X(X-1)},\qquad
v=\frac{Y}{X(X-1)}
\]

are fixed by the action and satisfy `v²=u²-4u+12`.  These identities expose
the cyclic cubic cover used by the classical Eisenstein-integer descent,
but do not themselves prove that the Jacobian has rank zero.

`NumberTheory/XOneEighteenDescent.lean` now carries the elementary quotient
arithmetic substantially further.  It parameterizes the conic away from
the exceptional fiber `u=1`, and rules out that fiber by a monic
rational-root argument reduced modulo two.  The three abscissas in an
automorphism orbit are the roots of

\[
z^3-uz^2+(u-3)z+1,
\]

whose discriminant is `(u²-3u+9)²`.  Writing the conic parameter as the
canonical coprime fraction `t=m/n` produces a homogeneous cubic with
discriminant

\[
(m^2+3n^2)^2(7m^2+6mn+3n^2)^2.
\]

Both quadratic factors are checked Eisenstein norms.  In coordinates
`a+bω`, with `ω²+ω+1=0`, the file defines multiplication, conjugation and
norm, proves `7=(3+ω)(2-ω)`, and proves the exact lattice criterion

\[
(3+\omega)\mid(a+b\omega)\quad\Longleftrightarrow\quad
7\mid 2a+b.
\]

For primitive `m,n`, the two norm factors cannot both be divisible by
seven.  The capstone theorem packages these coprime integer parameters,
the homogeneous cubic root, the quotient coordinates, and the local
seven-adic exclusion from any noncuspidal rational point.

This is the full elementary/local input to the classical `π=3+ω` descent,
not its global Jacobian conclusion.  Completion still requires the
order-three automorphism on `J₁(18)`, the induced `ℤ[ω]` action and
`π`-endomorphism, Kubert's global `π`-surjectivity on rational Jacobian
points, the rational torsion computation (classically `C₂₁`), and the
intersection of the Abel--Jacobi image with that torsion.  None of those
claims is inferred from the compiled norm identities.

`Kubert/OrderFourteenReduction.lean` now carries the even genus-one case
through `7P`.  Put

\[
\begin{aligned}
A&=c^2+c-b,\\
B&=b^2-bc-c^3,\\
C&=2b^2-bc^2-3bc+c^2,\\
D&=b^3-3b^2c+bc^3+3bc^2-c^5-c^4-c^3.
\end{aligned}
\]

The checked recurrence gives

\[
x(7P)=-\frac{bcAC}{B^2},\qquad
y(7P)=\frac{b^2A^2D}{B^3}.
\]

Exact order fourteen proves `b`, `c`, `b-c`, `A`, `B`, and `C` nonzero.
Since `7P` has exact order two, substituting the two coordinates into
`2y+(1-c)x-b=0` gives the denominator-safe equation

\[
2bA^2D-(1-c)cACB-B^3=0.
\]

The exported certificate retains this equation and the twelfth-power
discriminant scale.  After the sign change `q=-b`, this is Rabarison's
plane Tate model for `X₁(14)`, birational to

\[
s^2+st+s=t^3-t.
\]

The preferred inverse map avoids formalizing the much larger forward
birational formulas.  Directly on the Tate certificate it is

\[
t=\frac{D}{(b-c)C},\qquad
U=\frac{4(D+(b-c)C)}{(b-c)C},\qquad
V=\frac{4(b-2c^2-c)B}{bA^2}.
\]

Its denominators are precisely among the nonzero factors already exported
by `OrderFourteenReduction`.  After clearing denominators, the target
Weierstrass equation is the order-fourteen polynomial times an explicit
multiplier.  The identities

\[
D-(b-c)C=AB,\quad
\operatorname{Res}_b(P_{14},D)=-c^{33},\quad
\operatorname{Res}_b(P_{14},D+(b-c)C)=4c^{31}
\]

show respectively that the resulting abscissa is not `8`, `4`, or `0`.
`Kubert/OrderFourteenModel.lean` proves the two resultant consequences
through their much smaller explicit Bézout identities after setting
`r=b/c`; no general resultant API is needed.

The rational-point side now has a compiled specialized proof.  Completing
the square and putting

\[
U=4(t+1),\qquad V=4(2s+t+1)
\]

gives `V²=U(U²-11U+32)`, whose two-isogenous curve is
`W²=Z(Z²+22Z-7)`.  The two descent images are respectively `{1,2}` and
`{1,-7}`: positivity removes the negative classes on the first curve,
while the two missing dual classes reduce to `7 mod 8` when the primitive
numerator and denominator have opposite parity and to `12 mod 16` when
both are odd.  `NumberTheory/XOneFourteenDescent.lean` turns these
squareclass calculations into two explicit doubling cosets, proves finite
generation, computes the rational two-torsion cardinality as two, and uses
the finitely generated group index formula to prove rank zero and
finiteness.  It also constructs six distinct visible points generated by
`(8,8)`, of exact order six.  `NumberTheory/XOneFourteenReduction.lean`
proves good reduction at three, counts six reduced points, and injects the
finite rational point group into them.  The visible points therefore
exhaust the curve and every affine abscissa is `0`, `4`, or `8`.
`Kubert/OrderFourteen.lean` combines this fact with the inverse map, whose
image avoids all three values, and unconditionally excludes exact rational
order fourteen.

The new `Kubert/OrderFifteenReduction.lean` uses the exact-order hypothesis to
show that `5P` has exact order three, applies the checked three-torsion
criterion, and eliminates the Tate multiples. It produces parameters
`b,c,u` with every exceptional denominator nonzero, an explicit equation
`orderFifteenPolynomial b c = 0`, and the identity
`u^12 * E.Δ = tateNormalDiscriminant b c`. This is a complete,
denominator-safe reduction to the genus-one rational-point problem.

Independently, `NumberTheory/XOneFifteenDescent.lean` proves the specialized
two-isogeny descent for

\[
V^2=U(U^2-7U+16).
\]

It eliminates every non-visible original and dual squareclass by primitive
quartics modulo sixteen, constructs the two doubling cosets represented by
the identity and `(4,4)`, proves finite generation, computes exact rational
two-torsion cardinality two, and concludes rank zero and finiteness.

`Kubert/OrderFifteenModel.lean` now completes the denominator-safe
birational bridge.  For

\[
r=b/c,\qquad q=c^2/(b-c),
\]

it first checks the raw equation and proves that `q-1` and
`qr-2r+1` do not vanish.  It then uses

\[
\begin{aligned}
t&=-\frac{q^2r+q^2-3qr+r}{(q-1)(qr-2r+1)},\\
s&=-\frac{q^2-qr^2-qr+3r^2-3r+1}{(qr-2r+1)^2}
\end{aligned}
\]

to obtain `s²+st+s=t³+t²`, and sets

\[
U=4(t+1),\qquad V=4(2s+t+1).
\]

The resulting point lies on `V²=U(U²-7U+16)`.  Two explicit factor
identities on the raw equation prove `U≠0,4`; no denominator or exceptional
factor is silently cancelled.

`NumberTheory/XOneFifteenReduction.lean` supplies the sharp enumeration.
Good reduction at seven gives at most eight rational points.  The visible
point `(4,4)` has exact order four.  If a point of order eight existed,
successive denominator-free duplication identities would make its
abscissa a rational root of

\[
x^4-16x^3+80x^2-256x+256.
\]

Monicity makes such a root integral, while direct reduction modulo seventeen
shows that the polynomial has no root.  Thus the group has no element of
order eight.  Since its two-torsion has cardinality two, a finite group of
cardinality eight would have doubling image of cardinality four contained in
a two-element kernel, a contradiction.  Hence the group has exactly four
points, namely `O`, `(0,0)`, `(4,4)`, and `(4,-4)`.  Every affine abscissa is
therefore `0` or `4`, contradicting the model image.  The compiled
`Kubert/OrderFifteen.lean` unconditionally excludes exact rational order
fifteen.

The remaining low-level work must turn the six still-open composite order
cases `18,21,25,27,35,49` into explicit rational-point
classifications; cyclic orders divisible by five or seven are not
consequences of the already-proved *full* `C₅²` and `C₇²` obstructions.

The detailed subgraph is:

```text
Kubert/TateNormalForm
        │ [compiled through explicit 5P and recurrent 6P]
        ▼
Kubert/LowLevels
  no orders 14,15,16,20,24 [compiled]
  callbacks 18,21,25,27,35,49
        │
        ├───────────────► MazurTate/OrderThirteen
        │
        ▼
Mazur/PrimeOrder
  no remaining rational prime-order point
        │
        ▼
Mazur/PointOrder
  divisor closure leaves {1,…,10,12} [compiled]
```

Kubert's Theorem IV.1.2 is the mathematical reduction to a rational
prime-order subgroup of large level. The small-level files should expose
mathematical theorems, not raw computer-algebra transcripts. Rank-zero,
torsion, or cusp computations must be accompanied by checkable descent and
enumeration certificates.

### 6.1 Cyclic orders twenty and twenty-four

The completed exceptional-product theorems give a short route to the
*cyclic* orders twenty and twenty-four.  If `Q` has order `2m`, for
`m=10` or `12`, put `T=mQ`.  Then `T` is a rational point of order two.  After an
admissible variable change sends `T` to `(0,0)`, the source has equation

\[
E_{a,b}:y^2=x(x^2+ax+b).
\]

This normalization is now reusable rather than embedded in the
order-sixteen proof.  `EllipticCurve/TwoTorsionNormalization.lean` packages
the change, coefficients, transformed-curve equality, normalized origin,
and induced additive equivalence in `TwoTorsionNormalization.Data`.
`exists_data_of_order_two` constructs the package from exact order two;
the pullback API preserves additive order and transports any relation
`nP=T` to the normalized origin.

`EllipticCurve/TwoIsogeny.lean` now constructs the quotient formulas to

\[
E'_{a,b}:Y^2=X(X^2-2aX+a^2-4b):
\]

\[
X=\frac{y^2}{x^2}=x+a+\frac bx,\qquad
Y=\frac{y(b-x^2)}{x^2}.
\]

The point functions branch explicitly at infinity and `(0,0)`.  The files
prove that both kernels are exactly the corresponding infinity/origin
pairs, that translation by the source origin fixes the quotient map, and
that the displayed dual satisfies both composite identities

\[
\widehat\phi(\phi(P))=2P,\qquad
\phi(\widehat\phi(P'))=2P'
\]

for every rational point, including all exceptional branches.  Applying
the opposite composite to the first identity proves, without a global
additivity theorem,

\[
\phi(2P)=2\phi(P),\qquad
\widehat\phi(2P')=2\widehat\phi(P'),
\]

and hence compatibility with every power-of-two multiple.  This
fixed-multiple route is compiled in
`EllipticCurve/TwoIsogenyMultiples.lean`.

For order twenty, let `Q` be the normalized source point and put

\[
S=\phi(5Q),\qquad A=\phi(4Q).
\]

Doubling compatibility and the exact kernel show that `S` is a nonzero
point killed by two.  It is different from the target origin `T'`,
because applying the dual to an equality `S=T'` would make `10Q=0`.
Powers-of-two compatibility gives `16A=A`, hence `15A=0`.  If `3A=0`,
then `4A=A`; applying the dual would give `32Q=8Q`, so `24Q=0`,
contradicting exact order twenty.  Thus `R=3A` has exact order five.
The point

\[
C=S+R
\]

has exact order ten and `5C=S`.  Since the unique nonzero order-two
element in `⟨C⟩` is `S`, the distinct point `T'` is not in `⟨C⟩`.

For order twenty-four, instead put

\[
S=\phi(6Q),\qquad B=\phi(3Q),\qquad A=\phi(8Q).
\]

Again `S` is nonzero of order two and differs from `T'`.  The identity
`2B=S` makes `B` have exact order four.  Powers-of-two compatibility gives
`4A=A`, while the kernel and exact order of `Q` show `A≠0`; hence `A`
has exact order three.  Therefore

\[
C=B+A
\]

has exact order twelve and `6C=S`, so once again
`T'∉⟨C⟩`.

`GroupTheory/IndependentCyclicGenerators.lean` constructs the two `ZMod`
generator maps and proves that exact-order points `P,C` yield an injective
`ZMod 2 × ZMod n` map whenever `P∉⟨C⟩`.  Applied above, this produces
`C₂×C₁₀` and `C₂×C₁₂` inside the respective target point groups,
contradicting the already compiled unconditional exceptional-product
obstructions.  Thus the proof needs no unproved assertion that the raw
rational point function preserves arbitrary addition; the two composite
identities and their doubling consequences suffice.

`Arithmetic/OrderTwentyTwentyFour.lean` performs the final join for an
arbitrary elliptic curve: it proves the midpoint has exact order two,
normalizes it, pulls back the original point with exact order preserved,
builds the independent target generators, and applies the two forbidden
embedding theorems.  Its public endpoints unconditionally exclude exact
rational orders twenty and twenty-four.

### 6.2 Order-eleven boundary

The exact order-eleven branch now reaches the standard genus-one modular
curve without any cancelled exceptional factors:

```text
Kubert/OrderElevenReduction.lean
Kubert/OrderElevenModel.lean
NumberTheory/XOneElevenReduction.lean
NumberTheory/XOneElevenDescent.lean
```

For a marked point `P=(0,0)` on Tate normal form, exact order eleven gives
`6P=-5P`.  Comparing the already checked abscissas and writing

\[
A=c^2+c-b,\qquad B=b^2-bc-c^3,\qquad d=b-c
\]

produces the denominator-safe equation

\[
d^3B-bcA^3=0. \tag{X11}
\]

The proof derives `b,c,d,A,B≠0` from exact order.  Set

\[
r=b/c,\qquad q=c^2/(b-c).
\]

Then (X11) implies

\[
r^2-rq^3+3rq^2-4rq+q=0.
\]

With `N=rq-2r+1` and `K=q²-q-r+1`, the independently derived and
kernel-checked rational map

\[
U=\frac K N,\qquad
V=\frac{(q-r)K}{N^2}-1
\]

lands on

\[
V^2+V=U^3-U^2.
\]

The raw equation proves `N`, `K`, and `q-r` nonzero, and the exact-order
certificate proves `U≠0,1`.  Thus exact rational order eleven produces a
non-cusp affine point on `X₁(11)`.

`NumberTheory/XOneElevenReduction.lean` proves good reduction at three
and computes the reduced point group to have cardinality five.  Under the
explicit typeclass hypothesis
`[Finite XOneEleven.curve.toAffine.Point]`, reduction is injective, while
the five visible rational points force equality and show that every affine
rational point has `U=0` or `1`.

`NumberTheory/XOneElevenDescent.lean` now makes the missing global
calculation much narrower.  It first checks directly that `P₀=(0,0)` has
exact order five.  It defines the five-isogenous curve

\[
E': y^2+y=x^3-x^2-10x-20
\]

and, away from the four nonzero kernel points, verifies the Vélu
coordinate identity

\[
\begin{aligned}
x'&=x+\frac1{x^2}+\frac{2x-1}{(x-1)^2},\\
y'&=y-\frac{2y+1}{x^3}
       -\frac{x(2y+1)}{(x-1)^3}.
\end{aligned}
\]

The denominator-safe total point function sends infinity and the affine
points with `x=0` or `x=1` to infinity; Lean proves that this is its exact
affine zero fibre.  This file does not assert, without proof, that the raw
point function is additive.  The Miller/Kummer rational function

\[
f(x,y)=\frac{y^2(y+x)}{(x-1)^2}
\]

is recorded as the explicit input for the remaining isogeny descent.

The rational subgroup killed by five is also completely determined.
Reduction modulo three is injective on it, the reduced curve has five
points, and the five multiples of `P₀` are distinct.  Hence
`#E(ℚ)[5]=5`.  The one remaining arithmetic proposition is named
`FiveCosetBound`:

\[
\forall P\in E(\mathbb Q)\quad
 \exists\,0\le i<5,\ Q\in E(\mathbb Q),\qquad
 P=iP_0+5Q. \tag{X11-Sel}
\]

Everything after (X11-Sel) is compiled.  The five representatives make
`E(ℚ)/5E(ℚ)` finite of cardinality at most five.  An explicit
five-fold naïve-height descent turns this finite index into finite
generation: the checked growth inequality has leading term `25h(P)`,
while the translation inequality has coefficient two.  For a finitely
generated group the already compiled index formula gives

\[
[E(\mathbb Q):5E(\mathbb Q)]
  =5^{\operatorname{rank}E(\mathbb Q)}\,\#E(\mathbb Q)[5].
\]

The left side is at most five and the torsion factor is exactly five, so
the rank is zero.  Finite generation plus torsion then gives finiteness,
and the reduction theorem classifies all five points as cusps.  Thus the
only unconditional input still missing at level eleven is exactly
(X11-Sel), the finite local squareclass/Selmer computation for the
five-isogeny; no broader Mordell--Weil hypothesis remains hidden in the
interface, and order eleven is not yet claimed excluded.

### 6.3 Order-thirteen boundary

The strongest reusable research boundary for the first forbidden prime is
an independent, option-free reduction to `X₁(13)`.  Its file split is:

```text
Kubert/OrderThirteenReduction.lean
Kubert/OrderThirteenModel.lean
NumberTheory/XOneThirteenFiniteField.lean
NumberTheory/XOneThirteenDescent.lean
```

The first two files are compiled.  Exact order thirteen gives
`7P=-6P`; the checked coordinates yield the denominator-safe equation

\[
(b-c)B^3+bcA^3C=0,
\]

where `A=c²+c-b`, `B=b²-bc-c³`, and
`C=2b²-bc²-3bc+c²`.  The proof derives the nonvanishing of
`b,c,b-c,A,B,C` from exact order.  With

\[
r=b/c,\qquad s=c^2/(b-c),
\]

the denominator-cleared target is

\[
\begin{aligned}
G_{13}(r,s)={}&r^3+
(-s^4+5s^3-9s^2+4s-2)r^2\\
&+(-s^3+6s^2-3s+1)r-s^3=0.
\end{aligned}
\]

After substitution the Tate equation factors as
`s⁷(r-1)¹¹G₁₃(r,s)`.  The proof also retains
`r,s≠0`, `r,s≠1`, `r≠s`, and `rs-2r+1≠0`.

`OrderThirteenModel` checks the explicit rational map to

\[
y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1
\]

and proves that its image has `x≠0,-1`, the two rational affine cusp
abscissae relevant to the forward map.  This gives an unconditional
end-to-end reduction from exact order thirteen to a non-cusp point on the
sextic, but not yet its rational-point classification.

`XOneThirteenFiniteField` is also compiled.  Over `𝔽₃` it checks an
explicit Bézout identity between the sextic and its derivative, proving
separability and squarefreeness.  Ordinary finite enumeration gives the
four affine solutions at `x=0,-1`, and the monic even-degree infinity chart
has two smooth normalized directions.  The file deliberately packages this
as a six-element finite-field certificate rather than pretending that a
projective hyperelliptic API or rational reduction injection already
exists.

`XOneThirteenDescent` exposes much more of the classical `19`-isogeny
calculation without pretending that the missing Jacobian exists at this
pin.  The sextic has the checked order-six symmetry

\[
\sigma(x,y)=\left(-\frac1{x+1},\frac{y}{(x+1)^3}\right),
\qquad \sigma^3(x,y)=(x,-y).
\]

On `x≠0,-1`, the invariants

\[
u=\frac{x^3-3x-1}{x(x+1)},\qquad
v=\frac{y}{x(x+1)}
\]

lie on `v²=u²+2u+5`.  The file parameterizes this conic by

\[
u=\frac{t^2+4t-1}{1-t^2},\qquad
v=\frac{2(1+t^2)}{1-t^2}.
\]

The exceptional value `u=-1` is impossible because its monic cubic has no
root modulo two.  The three abscissas above a quotient point are the roots
of

\[
z^3-uz^2-(u+3)z-1,
\]

whose discriminant is `(u²+3u+9)²`.  For the canonical primitive fraction
`t=m/n`, denominator clearing gives a homogeneous cyclic cubic with
discriminant

\[
\left(7m^4-4m^3n+2m^2n^2+4mn^3+7n^4\right)^2. \tag{X13-disc}
\]

In coordinates `a+bρ`, with `ρ²-ρ+1=0`, the norm is
`a²+ab+b²` and

\[
19=(3+2\rho)(5-2\rho).
\]

The exact parameter coordinates

\[
a=m^2+4mn-n^2,\qquad b=3(n^2-m^2)
\]

have norm equal to the factor in (X13-disc).  Lean proves the two
index-19 lattice criteria

\[
\begin{aligned}
(3+2\rho)\mid(a+b\rho)&\iff19\mid(5a+2b),\\
(5-2\rho)\mid(a+b\rho)&\iff19\mid(3a-2b),
\end{aligned}
\]

the converse split-norm theorem, and a modulo-19 certificate showing that
primitive `(m,n)` cannot lie in both branches.

The same file also contains a polynomial Pell certificate.  Independently
computed polynomials `H` and `K` of degrees `19` and `16`, respectively,
satisfy

\[
H(x)^2-f_{13}(x)K(x)^2=-4. \tag{X13-Pell}
\]

The reciprocal-chart identity has right side `-4z³⁸`, and its boundary
values distinguish the two points at infinity.  These are the exact
function-field identities underlying

\[
\operatorname{div}(H+yK)=
 19(\infty_- - \infty_+).
\]

The coefficients were produced locally by a standard-library-only
polynomial continued-fraction computation and are independently
kernel-checked by Lean's `ring`; no external coefficient table or
unlicensed source was copied.

These calculations still do not classify the rational points.  Pinned
mathlib has no genus-two hyperelliptic divisor/Picard/Jacobian
implementation, so the first missing bridge is to interpret (X13-Pell) as
the displayed principal-divisor identity and construct the Abel--Jacobi
class.  The classical global leaves are then the Mazur--Tate
`π=3+2γ₂` surjectivity theorem on `J₁(13)(ℚ)`, the computation
`J₁(13)(ℚ)_tors ≃ Z/19`, and Ogg's theorem that the Abel--Jacobi image
meets that torsion subgroup only at the six cusps.  No public
order-thirteen exclusion is claimed before those leaves are formalized.

### 6.4 Order-twenty-one boundary

`NumberTheory/XZeroTwentyOneDescent.lean` independently formalizes the
elementary arithmetic of the standard conductor-21 model

\[
E_{21}:y^2+xy=x^3-4x-1.
\]

The integral affine change

\[
V=4x+1,\qquad W=8y+4x
\]

is proved in both directions and gives

\[
W^2=V(V-9)(V+7). \tag{X21}
\]

The classical fibre-product equation obtained by equating the
`X₀(3)` and `X₀(7)` Hauptmodul formulas is also recorded:

\[
(t_3+27)(t_3+3)^3t_7^7
=t_3(t_7^2+13t_7+49)
  (t_7^2+245t_7+2401)^3.
\]

Four visible rational pairs and their four `j`-values are kernel-checked.
The file deliberately does not assert a modular interpretation or a
birational map from this plane model to `E₂₁`; that bridge must be proved
before using the arithmetic classification to exclude an exact
order-twenty-one point.

For a rational point on (X21) with `V≠0`, write `V=m/n` in lowest terms.
After denominator clearing, the square equation factors as

\[
(Wn^2)^2=(mn)(m^2-2mn-63n^2).
\]

The gcd of the two factors divides `63`.  Removing their gcd and using
coprimality proves that the squareclass of `V` is one of

\[
\pm1,\ \pm3,\ \pm7,\ \pm21.
\]

If `V=d r²`, write the canonical primitive fraction `r=m/n`.  The
associated homogeneous space is

\[
c^2=d(dm^2-9n^2)(dm^2+7n^2). \tag{X21-d}
\]

An exhaustive `ZMod 16` certificate eliminates `d=-1` and `d=3`.
Translation by the rational two-torsion point `(0,0)` is checked directly:

\[
(V,W)\longmapsto
\left(-\frac{63}{V},\frac{63W}{V^2}\right).
\]

It pairs the remaining squareclasses and reduces the global calculation
to exactly two propositions:

\[
\begin{aligned}
c^2&=m^4-2m^2n^2-63n^4,\\
c^2&=-3m^4-2m^2n^2+21n^4.
\end{aligned} \tag{X21-quartics}
\]

They are named `PrincipalQuarticClassified` and
`NegativeThreeQuarticClassified`.  Visible primitive solutions
`(m,n,c)=(3,1,0)` and `(1,1,4)` show that neither leaf can be dismissed by
a simple local obstruction; genuine infinite descent is required.

Assuming exactly these two leaves, Lean proves that

\[
V\in\{0,9,-7,-3,21\}
\]

and enumerates the seven affine solutions of (X21), hence eight rational
points after adding infinity.  Thus the order-21 branch now has two
separate honest boundaries: the two explicit quartic descents, and the
modular/Tate bridge sending an exact order-21 point to a noncuspidal point
of this concrete curve.

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

This layer is complete.  Its implementation is split as:

```text
Arithmetic/ExceptionalTwoTen.lean
Arithmetic/ExceptionalTwoTwelve.lean
NumberTheory/ExceptionalQuarticDescent.lean
NumberTheory/ExceptionalCubicDescent.lean
NumberTheory/ExceptionalCubicReduction.lean
Arithmetic/ExceptionalProducts.lean
```

The public endpoints are:

```lean
forbidsEmbedding_zmod_two_prod_ten
forbidsEmbedding_zmod_two_prod_twelve
rationalTorsion_forbids_zmod_two_prod_ten
rationalTorsion_forbids_zmod_two_prod_twelve
```

The direct implementation starts from independent rational two-torsion and
an order-five or order-six point, normalizes the curve, and derives the
explicit quartic/cubic Diophantine boundaries.  This avoids making an
unformalized identification with a modular `X₀(N)` model.  The completed
product obstructions are then reused by the cyclic order-twenty and
order-twenty-four proof in Section 6.1.

Use explicit genus-one models:

\[
X_0(20):y^2=x^3+x^2+4x+4,
\qquad
X_0(24):y^2=x^3-x^2-4x+4.
\]

The explicit models below remain useful mathematical orientation.  The
compiled direct obstruction does not require a claim that these equations
represent the modular curves, so no moduli identification is silently
assumed.

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
`EllipticCurve/VariableChange.lean`.  The selected 31-file reduction cone
is now ported under `EllipticCurves/` with exact source-commit provenance
and small documented pin adaptations.  Its `ReductionAtPrime` theorem and
the concrete modulo-five harness are sufficient for the exceptional cubic;
the substantially broader Selmer and general Mordell--Weil cones remain
unnecessary.

For `E₂₄`, the rank part of this plan is now compiled in a smaller direct
form. Clearing rational denominators proves the four possible abscissa
square classes. A constructive reverse-duplication calculation gives four
explicit cosets modulo `2E(ℚ)`. The local naïve-height theorem turns finite
index into finite generation, and
`AddSubgroup.index_range_nsmul_of_fg` turns that index together with exact
`#E[2]=4` into rank zero. What remains from the displayed finite-field
paragraph is only torsion injection and the cardinality step at `p=5`;
rank zero must not be conflated with that final bound.

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

Both reductions are machine-checked through their final explicit
Diophantine leaves. The first leaf is now closed by the elementary
`D_+D_-=125z⁴` infinite descent in
`NumberTheory/ExceptionalQuarticDescent.lean`. The second curve's
two-descent, rank-zero theorem, and finiteness are checked in
`NumberTheory/ExceptionalCubicDescent.lean`; good reduction at five then
proves the sharp bound `Nat.card E(ℚ) ≤ 8` and closes the second leaf.
The general `X₀(20/24)` construction is therefore valuable, non-critical
infrastructure rather than a dependency of the direct cardinality path.

## 9. Arithmetic assembly

`Arithmetic/CardinalityReduction.lean` is now the compiled numerical
assembly. It exposes the exact one-input endpoint:

```lean
theorem torsion_ncard_le_of_arithmetic_inputs
    [E.IsElliptic]
    (horders : ∀ x : RationalTorsion E,
      addOrderOf x ∈ cyclicOrders) :
    torsionSet.ncard ≤ 16
```

It also exposes the equivalent explicitly named endpoint

```lean
theorem torsion_ncard_le_of_explicit_arithmetic
    [E.IsElliptic]
    (horders : ∀ x : RationalTorsion E,
      addOrderOf x ∈ cyclicOrders) :
    torsionSet.ncard ≤ 16
```

All low-level and odd-prime subgroup exclusions, the completed
`C₂ × C₁₀` quartic descent, the `C₂ × C₁₂` cubic descent and reduction,
subgroup extraction, restriction to torsion, and cardinality assembly are
discharged behind this interface.

The remaining arithmetic assembly step is:

1. invoke the rational point-order theorem for every torsion element;
2. call the compiled one-input endpoint.

No global `Fintype` or Mordell--Weil theorem should leak into the API.

## 10. Final LeanPool file

Only after the dependency cone is clean, add `Solution/Mazur.lean` in a
LeanPool-compatible checkout:

```lean
import MazurTorsion.Arithmetic.CardinalityReduction
import MazurTorsion.Arithmetic.PointOrder

namespace Challenge.Mazur

open scoped WeierstrassCurve.Affine

theorem torsion_ncard_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point :
      Set (E⁄ℚ).Point).ncard ≤ 16 :=
  MazurTorsion.torsion_ncard_le_of_arithmetic_inputs E
    (MazurTorsion.rational_torsion_order_mem_cyclicOrders E)

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
| M4 | Full rational `5`- and `7`-torsion obstructions | done, including both universal discriminant identities | low |
| M5 | Exceptional products / `X₀(20),X₀(24)` certificates | done: both `C₂×C₁₀` and `C₂×C₁₂` are excluded unconditionally | low |
| M6 | Kubert small-level and order-thirteen exclusions | Tate normal form and exact divisor reduction done; orders 14, 15, 16, 20, and 24 excluded unconditionally, leaving only six composite callbacks; level 11 reaches a single explicit five-isogeny Selmer coset proposition; level 13 has the symmetry quotient, split-19 descent data, and Pell divisor precursor; order 18 reaches its local Eisenstein descent boundary; the `X₀(21)` arithmetic is reduced to two explicit quartic descents plus its modular bridge | high |
| M7 | Mazur prime-level Eisenstein/Néron/cyclotomic argument | planned | extremely high |
| M8 | Arithmetic assembly and exact `Solution/Mazur.lean` | one-input numerical assembly done; blocked only on the remaining point-order work in M6--M7 | low once dependencies exist |

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
observed maximum resident set so far is approximately 3.68 GB, safely below
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
