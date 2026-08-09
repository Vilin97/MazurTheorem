# `X₁(13)` Jacobian route audit

This note records the checked finite calculations, the failed local-cover
shortcut, and the exact global boundary for the rational-point theorem on

\[
C:\quad y^2=f(x),\qquad
f(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1.
\]

It is an audit, not a claim that the open rational-point classification has
been proved.

## Primary route and provenance

The primary source is B. Mazur and J. Tate, *Points of Order 13 on Elliptic
Curves*, Inventiones Mathematicae **22** (1973), 41--49,
[doi:10.1007/BF01425572](https://doi.org/10.1007/BF01425572).  The PDF audited
for this note has SHA-256
`a451c978b1557e7f1f95e34bf62f51f8ee98d5e29b100a5e46345a69653e49c1`.
Their proof has two genuinely global outputs:

1. a `19`-isogeny descent on `J₁(13)` proving `#J₁(13)(ℚ)=19`; and
2. Ogg's determination that the intersection of the curve with this
   nineteen-element subgroup consists exactly of the six rational cusps.

The descent uses the twisted-dihedral action on `J[19]`, finite flat group
schemes over `Spec ℤ[1/13]`, local surjectivity at `13`, and an fppf/CFT
vanishing over the cyclotomic field.  These ingredients cannot be replaced
by the affine polynomial identities alone.

S. Kamienny and B. Newman, *Points of Order 13 on Elliptic Curves*,
[arXiv:1608.08672](https://arxiv.org/abs/1608.08672), was also audited.  The
PDF has SHA-256
`5d7d5412bf1bcdf2162eb0b1320af1d159eca62c1f9f6e0e8fb36789820ee22d`.
Its bielliptic computation over `ℚ(ζ₁₃)⁺` is useful corroboration, but
does not shorten the rational `ℚ` proof at the currently pinned Lean
dependencies.

## Why the elementary `19`-cover does not give a local obstruction

`XOneThirteenDescent` checks polynomials `H = pellH` and `K = pellK` with

\[
H(x)^2-f(x)K(x)^2=-4.
\]

The integral split suggests the affine cover

\[
 z^{19}=\frac{H(x)+yK(x)}2.
\]

At the rational cusp `(x,y,z)=(0,1,1)` the exact values are

\[
 f(0)=1,\quad f'(0)=4,\quad
 H(0)=0,\quad H'(0)=4,\quad K(0)=2,\quad K'(0)=-4.
\]

For

\[
 F=y^2-f(x),\qquad G=H(x)+yK(x)-2z^{19},
\]

the `(x,y)` minor of the Jacobian at this cusp is

\[
 \begin{pmatrix}-4&2\\0&2\end{pmatrix},
 \qquad \det=-8.
\]

Consequently the cover has an odd-adic analytic branch through the cusp;
searching for a congruence obstruction there cannot terminate.  More
explicitly:

* for `p=3,5`, take `x=p`, choose the Hensel lift `y²=f(p)` with
  `y≡1 (mod p)`, and put `w=(H+yK)/2`.  Then `w∈1+pℤ_p`, while the
  nineteenth-power map is an automorphism of `1+pℤ_p`;
* for `p=19`, take `x=19²`.  Then `w∈1+19²ℤ₁₉`, which is the image
  under the nineteenth-power map of `1+19ℤ₁₉`;
* for `p=2`, take `x=2`.  Here `f(2)=193≡1 (mod 8)`, so it is a
  `ℚ₂`-square.  The resulting `w` is odd, and raising to the odd power
  `19` is an automorphism of `ℤ₂×`.

Thus neither the two-case integral split nor its affine `19`-cover supplies
a finite local contradiction.  The remaining work must use a global
Jacobian/Picard argument (or a comparably strong global Diophantine
argument).

## Checked two-prime finite data

`MazurTorsion.NumberTheory.XOneThirteenFiniteField` checks all of the
following by kernel-reduced finite enumeration and explicit Bézout
identities:

| field | `#C` point certificate | affine points | infinity directions |
|---|---:|---:|---:|
| `𝔽₃` | 6 | 4 | 2 |
| `𝔽₉` | 8 | 6 | 2 |
| `𝔽₅` | 6 | 4 | 2 |
| `𝔽₂₅` | 12 | 10 | 2 |

The quadratic fields use transparent pair presentations with `ω²=2`.
Lean checks that `2` is nonsquare in each base field, that every nonzero
pair has a multiplicative inverse, and that Frobenius is pair conjugation.
The non-base points form one conjugate fiber over `𝔽₃` and three over
`𝔽₅`.

The base-field rows are now also geometric statements about the actual
two-chart scheme.  The checked internal chart decomposition proves that
every morphism from the spectrum of a field to the glued curve factors
either through the ordinary chart or through the reciprocal boundary.  The
checked overlap identity says that this boundary is exactly `z = 0`, whose
equation reduces to `w² = 1`.  Consequently
`pointCertificateEquivSchemePointF3` and
`pointCertificateEquivSchemePointF5` identify the old six-element
certificates with literal points of the glued projective scheme.  In
particular, `card_schemePoint_F3` and `card_schemePoint_F5` prove actual
scheme-point counts of six.  The `𝔽₉` and `𝔽₂₅` rows remain transparent
quadratic-pair certificates; they have not yet been identified with points
of a field-valued base change of the glued scheme.

The degree-two enumeration is therefore

\[
 \#\operatorname{Sym}^2 C(𝔽_q)
   =\frac{N_1^2+N_2}{2},
\]

giving `22` at `q=3` and `24` at `q=5`.  In both cases the twenty-one
unordered pairs of rational points contain three hyperelliptic pairs.  The
extension contributes one further hyperelliptic fiber at `3` and three at
`5`.  Collapsing the `q+1` members of the hyperelliptic pencil to one label
leaves

\[
22-3=19,\qquad 24-5=19.
\]

Lean packages these as
`ReducedDegreeTwoClassCertificateF3` and
`ReducedDegreeTwoClassCertificateF5`, and proves that each has cardinality
`19`.  These are deliberately combinatorial types, not definitions of a
Picard group or Jacobian.

There is also an explicit perfect coordinate set in `ZMod 19`:

\[
\{1,-1,7,-7,8,-8\}.
\]

The three opposite pairs are exactly the rational hyperelliptic pairs; the
other eighteen unordered pair sums give every nonzero residue exactly once.
Quadratic hyperelliptic fibers receive coordinate zero.  Lean checks that
this coordinate is a bijection from either reduced certificate to
`ZMod 19`, and transports the cyclic group law along it.  The resulting
`reducedDegreeTwoClassAddEquivZModF3` and
`reducedDegreeTwoClassAddEquivZModF5` are group structures on the
*combinatorial certificates*.  They still do not identify those groups with
geometric Picard groups.

For a smooth projective genus-two curve, Riemann--Roch identifies this
calculation with the familiar formula

\[
 \#J(𝔽_q)=\frac{N_1^2+N_2}{2}-q.
\]

That geometric identification is not yet available in the pinned
libraries.  The named consumer
`finitePicard_cards_eq_nineteen_of_reducedDegreeTwoEquiv` requires actual
additive equivalences from finite Picard/Jacobian point groups to the
certificate groups.  It does not assume them silently.  The two
`finitePicard_addEquiv_zmodNineteen_of_*Certificate` consumers then produce
the corresponding genuine cyclic presentations of those Picard groups.

## Exact remaining boundary

The checked theorem
`rationalJacobian_card_eq_nineteen_of_two_reduction_bounds` isolates the
arithmetic endpoint.  If a finite rational Jacobian `JQ` satisfies

\[
\#JQ\mid 19\,3^a,\qquad
\#JQ\mid 19\,5^b,\qquad
19\mid\#JQ,
\]

then `#JQ=19`.  The first two hypotheses are exactly what good reduction
with possible residue-characteristic primary kernels should supply; the
last should come from the nonzero order-`19` infinity-divisor class encoded
by the Pell identity.

The stronger named consumer
`rationalJacobian_card_eq_nineteen_of_reduction_homs` takes the expected
reduction homomorphisms themselves.  If their kernel cardinalities are
`3ᵃ` and `5ᵇ`, Lagrange's theorem derives the two divisibility bounds from
the additive finite-Picard certificate equivalences, and the same conclusion
follows.  This leaves no hidden injectivity assumption: proving those
primary-kernel statements is precisely the outstanding good-reduction
theorem.

The glued curve itself is no longer only a chartwise candidate for a proper
model.  The chart computations
`ordinaryChartToProjectiveLine_structureMap` and
`reciprocalChartToProjectiveLine_structureMap` give the checked identity

`curveToBase = hyperellipticMap ≫ ProjectiveLine.structureMap`.

Since the hyperelliptic map is finite and projective line is proper, Lean
now supplies `curveToBase_isProper`.  The same finite map gives local
Noetherianity and properness gives compactness, yielding the actual
`curveScheme_isNoetherian` instance.  This discharges the properness and
Noetherianity portions of the geometric setup; it does not assert
smoothness, integrality, genus, or Picard representability.

The dependency-critical missing steps are:

1. prove that the now-proper glued curve is integral, smooth of relative
   dimension one, and genus two, and construct its good integral models at
   `3` and `5`;
2. identify the quadratic-extension point certificates with actual
   `𝔽₉`- and `𝔽₂₅`-points, construct the degree-zero Picard
   group/Jacobian, and identify the two finite reductions with the checked
   reduced degree-two certificates;
3. prove the good-reduction kernel bounds on rational torsion;
4. prove `J(ℚ)` has rank zero (or formalize the Mazur--Tate
   `19`-isogeny-surjectivity descent that implies finiteness);
5. turn the Pell identity into a nonzero divisor class of exact order `19`;
6. prove Abel--Jacobi injectivity for the curve and identify the six
   rational cusp classes, yielding the rational-point classification.

The existing group-valued Picard/Abel--Jacobi files provide divisor-class
normalizations and linear-system fibers, but they do not construct the
representable Jacobian, its integral reduction, or the required
Mordell--Weil theorem.  Those are genuine formalization tasks, not blockers
or assumptions supplied by the finite enumeration.
