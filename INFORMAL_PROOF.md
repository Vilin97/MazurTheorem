# Informal proof of the LeanPool Mazur challenge

## 1. Statement and the `Set.ncard` subtlety

Let `E` be an elliptic Weierstrass curve over `ℚ`, and put

\[
T=E(\mathbb Q)_{\mathrm{tors}}.
\]

LeanPool asks for

\[
\operatorname{ncard}(T)\leq 16.
\]

In Lean, `Set.ncard` is the ordinary cardinality when the set is finite and
is defined to be zero when the set is infinite. Thus the literal theorem can
be proved by splitting into two cases.

* If `T` is infinite, then `Set.Infinite.ncard` gives
  `Set.ncard T = 0`, and the result is immediate.
* If `T` is finite, prove Mazur's classification for this finite subgroup and
  count the fifteen possible groups.

This observation is useful formally: the challenge does not have to depend
on Mordell--Weil or on a separate proof that rational torsion is finite.
Mathematically, of course, rational torsion is finite.

## 2. The elementary last step

Mazur's classification says that `T` is isomorphic to exactly one group in
the following list:

\[
\mathbb Z/n\mathbb Z\quad
(1\leq n\leq 10\text{ or }n=12),
\]

or

\[
\mathbb Z/2\mathbb Z\times\mathbb Z/(2m)\mathbb Z
\quad(1\leq m\leq 4).
\]

There are eleven cyclic groups and four bicyclic groups. Their cardinalities
are, respectively, `n ≤ 12` and

\[
2(2m)=4m\leq 16.
\]

The maximum is attained by
`ℤ/2ℤ × ℤ/8ℤ`. This counting argument is already formalized as
`MazurTorsion.torsion_ncard_le_of_classification`. The exact finite/infinite
split is formalized as
`MazurTorsion.torsion_ncard_le_of_classification_if_finite`.

## 3. Why the classification has this shape

This section isolates the relatively standard structural reduction from the
deep modular-curve theorem.

### 3.1 Two invariant factors

Assume `T` is finite. Let `N` be its exponent. Base change embeds `T` into
the geometric `N`-torsion:

\[
T\hookrightarrow E[N](\overline{\mathbb Q}).
\]

In characteristic zero,

\[
E[N](\overline{\mathbb Q})
\simeq(\mathbb Z/N\mathbb Z)^2.
\]

The structure theorem for finite abelian groups therefore gives integers
`a,b > 0`, with `a ∣ b`, and an isomorphism

\[
T\simeq\mathbb Z/a\mathbb Z\times\mathbb Z/b\mathbb Z.
\]

Equivalently, every finite subgroup of a geometric elliptic curve has at
most two invariant factors.

### 3.2 The first invariant factor is at most two

The subgroup of the displayed product killed by `a` has `a²` elements.
It lies in `E[a]`, which also has `a²` geometric points. Consequently all of
`E[a]` is rational over `ℚ`.

Choose a rational basis `P,Q` of `E[a]`. The Weil pairing

\[
e_a:E[a]\times E[a]\longrightarrow\mu_a
\]

is alternating, nondegenerate, and Galois equivariant. Therefore
`e_a(P,Q)` is a primitive `a`-th root of unity fixed by
`Gal(\overline{\mathbb Q}/\mathbb Q)`, hence it lies in `ℚ`.
The only roots of unity in `ℚ` are `1` and `-1`; therefore `a ≤ 2`.

This argument is the conceptual generalization of the explicit low-torsion
obstructions already proved in this project. In particular, the current Lean
files prove directly that full rational `3`-torsion and full rational
`4`-torsion are impossible, without yet constructing the Weil pairing.

There is also a fixed-level division-polynomial proof at `5` and `7`.
Write

\[
P=(x,y),\quad T=2y+a_1x+a_3,\quad
q=\Psi_3(x),\quad r=\operatorname{pre}\Psi_4(x).
\]

If `2P=(x₂,y₂)`, the tangent formula and the curve equation give

\[
T^2=\PsiSq_2(x),\qquad q=-T^2(x_2-x),
\]

and hence

\[
\Phi_2(x)=x_2\PsiSq_2(x).
\]

Writing `T₂=2y₂+a₁x₂+a₃`, the doubled ordinate formula and a
low-degree identity for `preΨ₄` give

\[
r=T^3T_2.
\]

Now let `3P=(x₃,y₃)`. The secant identities for
`P+2P=3P` and `P-2P=-P` imply

\[
(x_2-x)^2(x-x_3)=TT_2.
\]

Substitution in
`\Phi_3=x\Psi_3^2-\operatorname{pre}\Psi_4\Psi_2^2`
then yields

\[
\Phi_3(x)=x_3\PsiSq_3(x).
\]

For `4P=(x₄,y₄)`, put `A=Φ₂(x)` and `D=ΨSq₂(x)`.
The two polynomial identities

\[
\Phi_4=A^4-b_4A^2D^2-2b_6AD^3-b_8D^4
\]

and

\[
\PsiSq_4=4A^3D+b_2A^2D^2+2b_4AD^3+b_6D^4
\]

reduce, using `A=x₂D`, to the doubling formula applied at `2P`.
Consequently

\[
\Phi_4(x)=x_4\PsiSq_4(x).
\]

If `5P=0`, then `4P=-P`, so `x₄=x`. The elliptic-divisibility
identity

\[
\Phi_4=x\PsiSq_4-\Psi_3\operatorname{pre}\Psi_5
\]

therefore says
`q·preΨ₅(x)=0`. Here `q≠0`, since `q=0` would give
`3P=0`, and together with `5P=0` would force `P=0`.
Thus `preΨ₅(x)=0`.

If `7P=0`, then `4P=-3P`, so `x₄=x₃`. The cross identity

\[
\Phi_4\PsiSq_3-\Phi_3\PsiSq_4
  =-\operatorname{pre}\Psi_7
\]

immediately gives `preΨ₇(x)=0`. These two root criteria are fully
machine-checked in the project.

An injection `(ℤ/pℤ)² → E(ℚ)` supplies all
`(p²-1)/2` nonzero abscissas modulo sign, so the degree
`(p²-1)/2` polynomial `preΨₚ` splits over `ℚ`. A split rational
polynomial has square discriminant. The classical identities are

\[
\operatorname{disc}(\operatorname{pre}\Psi_5)
 =5^{11}\Delta^{22},
\qquad
\operatorname{disc}(\operatorname{pre}\Psi_7)
 =-7^{23}\Delta^{92}.
\]

The first has square class `5`, and the second square class `-7`;
neither is a rational square when `Δ≠0`. Hence full rational
`5`-torsion and full rational `7`-torsion are impossible. In Lean,
the root, splitting, square-discriminant, and nonsquare parts are complete;
only these two universal fixed-level discriminant calculations remain to be
certified.

### 3.3 Possible point orders

The element `(0,1)` in the invariant-factor presentation has order `b`.
Mazur's point-order theorem says that a rational torsion point has order

\[
b\in\{1,2,3,4,5,6,7,8,9,10,12\}.
\]

If `a=1`, the group is cyclic and has at most twelve elements.

If `a=2`, divisibility `a ∣ b` makes `b` even, so

\[
b\in\{2,4,6,8,10,12\}.
\]

The groups with `b=2,4,6,8` have sizes `4,8,12,16`. Two apparent cases
remain:

\[
\mathbb Z/2\mathbb Z\times\mathbb Z/10\mathbb Z,\qquad
\mathbb Z/2\mathbb Z\times\mathbb Z/12\mathbb Z.
\]

It is important not to claim that the point-order theorem alone excludes
these groups: every element in them still has an allowed order.

### 3.4 Excluding the two remaining product cases

There is a standard cyclic-isogeny reduction. Suppose `P` is the independent
rational point of order two and `Q` generates the factor of order `2n`,
where `n=5` or `6`. Let

\[
f:E\longrightarrow E/\langle P\rangle,\qquad
g:E\longrightarrow E/\langle Q\rangle
\]

be the rational quotient isogenies. Independence of `P` and `Q` shows that

\[
g\circ f^\vee:E/\langle P\rangle
\longrightarrow E/\langle Q\rangle
\]

has cyclic kernel and degree `4n`. Thus the two cases would produce a
rational cyclic isogeny of degree `20` or `24`, equivalently a noncuspidal
rational point on `X₀(20)` or `X₀(24)`.

Both genus-one modular curves have rank zero and their rational points are
cusps. One convenient pair of models is

\[
X_0(20):y^2=x^3+x^2+4x+4,
\qquad
X_0(24):y^2=x^3-x^2-4x+4.
\]

Their rational Mordell--Weil groups have orders six and eight, respectively,
and enumeration identifies every rational point with a cusp. Hence neither
noncuspidal point exists, eliminating both product cases.

Here is a certificate-level proof of the two rank computations. For

\[
E_{a,b}:y^2=x(x^2+ax+b),
\]

the two-isogenous curve is

\[
E'_{a,b}:Y^2=X(X^2-2aX+a^2-4b).
\]

The degree-two isogeny and its dual are given away from their kernels by

\[
\phi(x,y)=
\left(\frac{y^2}{x^2},\frac{y(b-x^2)}{x^2}\right),
\]

\[
\widehat\phi(X,Y)=
\left(\frac{Y^2}{4X^2},
\frac{Y(a^2-4b-X^2)}{8X^2}\right).
\]

Direct substitution in the chord-and-tangent formulas verifies
`φ̂ ∘ φ=[2]` and `φ ∘ φ̂=[2]`.

Define

\[
\alpha_E(O)=1,\qquad
\alpha_E((0,0))=b,\qquad
\alpha_E((x,y))=x
\quad\text{in }\mathbb Q^\times/\mathbb Q^{\times2}.
\]

Its kernel is `φ̂(E'(ℚ))`. If `x=A/C²`, `y=B/C³` in lowest
terms and `d` is the squarefree part of `A`, clearing denominators shows
that `d` divides `b` and gives coprime integers satisfying

\[
V^2=dU^4+aU^2W^2+(b/d)W^4. \tag{1}
\]

Conversely, such a quartic solution reconstructs a point in square class
`d`. Thus (1) is a finite, kernel-checkable certificate for the image of
the descent map.

For `X₀(20)`, put `u=x+1`. The curve and its dual become

\[
E_{20}:y^2=u(u^2-2u+5),\qquad
E'_{20}:Y^2=X(X^2+4X-16).
\]

For `E₂₀`, the candidate classes are `±1,±5`. In (1), the
right-hand sides for `d=-1` and `d=-5` are strictly negative, while
`1` and `5` occur. Hence

\[
\operatorname{im}\alpha_{E_{20}}=\{1,5\}.
\]

For the dual, the candidates are `±1,±2`. The classes `1` and `-1`
occur. For `d=±2`, if `U` is odd the right side has 2-adic
valuation one; if `U` is even, coprimality makes `W` odd and the
valuation is three. A square has even valuation, so these cases are
impossible. Therefore

\[
\operatorname{im}\alpha_{E'_{20}}=\{1,-1\}.
\]

For `X₀(24)`, put `u=x-1`. This gives

\[
E_{24}:y^2=u(u^2+2u-3),\qquad
E'_{24}:Y^2=X(X^2-4X+16).
\]

The points with `u=-3,-1,0,1,3` show that every candidate class
`1,-1,3,-3` occurs for `E₂₄`. On the dual, negative candidates
are excluded by positivity and the class `2` by the same 2-adic
valuation argument. Hence

\[
\operatorname{im}\alpha_{E_{24}}=\{1,-1,3,-3\},\qquad
\operatorname{im}\alpha_{E'_{24}}=\{1\}.
\]

For a finitely generated Mordell--Weil group of rank `r`, the two descent
maps satisfy the index formula

\[
|\operatorname{im}\alpha_E|\,
|\operatorname{im}\alpha_{E'}|=4\cdot2^r.
\]

Both products above equal four, so both ranks are zero. Good reduction
then bounds the torsion exactly: `#E₂₀(𝔽₃)=6` and
`#E₂₄(𝔽₅)=8`. Explicit points attain these bounds, giving

\[
X_0(20)(\mathbb Q)=
\{O,(-1,0),(0,\pm2),(4,\pm10)\}
\]

and

\[
X_0(24)(\mathbb Q)=
\{O,(-2,0),(0,\pm2),(1,0),(2,0),(4,\pm6)\}.
\]

Finally,

\[
\#\operatorname{Cusps}(X_0(N))
=\sum_{d\mid N}\varphi(\gcd(d,N/d)).
\]

This gives six cusps at level 20 and eight at level 24. Every relevant
gcd is at most two, so all those cusps are rational. Once the displayed
models are proved to represent the modular curves, equality of cardinalities
shows that every rational point is a cusp; a coordinate-by-coordinate cusp
table is unnecessary.

Combining Sections 3.1--3.4 proves the exact fifteen-group classification
once the point-order theorem and the two modular-curve computations are
available.

## 4. The deep point-order theorem

The point-order theorem is the genuine bottleneck. A complete formal proof
cannot treat it as a finite arithmetic calculation: Mazur's proof uses
integral modular curves, Jacobians, Hecke operators, the Eisenstein ideal,
Néron models, finite-flat group schemes, and cyclotomic arithmetic.

The following is a proof-level roadmap of the original large-prime argument.

### 4.1 Convert a torsion point into a modular point

A rational point `P` of exact order `N` gives a rational noncuspidal point
of `Y₁(N)`, and its cyclic subgroup gives a rational noncuspidal point

\[
x=(E,\langle P\rangle)\in Y_0(N)(\mathbb Q).
\]

After compactification this is a point of `X₀(N)` distinct from the cusps.
Tate normal form and Kubert's explicit calculations dispose of the small
levels and reduce the remaining obstruction to prime level (with the
classical order-thirteen case handled separately by Mazur--Tate).

### 4.2 The Eisenstein quotient

Let `J₀(N)` be the Jacobian of `X₀(N)`. Embed the modular curve by an
Abel--Jacobi map based at the cusp `∞`, and project to the Eisenstein
quotient `Jₑ`.

The Hecke algebra acts on `J₀(N)`. The Eisenstein ideal is generated by the
relations

\[
T_\ell-(1+\ell)\quad(\ell\nmid N)
\]

together with the appropriate level operator relation. Mazur proves the
needed structure of the completed Hecke algebra, that the Eisenstein
quotient has finite rational points, and that the rational cuspidal divisor
`[0]-[∞]` survives with the expected nonzero order
`numerator((N-1)/12)`.

More precisely, if `𝕋` is the Hecke algebra and

\[
I=(1+\ell-T_\ell,\;1+w_N),
\]

then Mazur proves `𝕋/I ≃ ℤ/nℤ` for
`n = numerator((N-1)/12)`. The cusp class
`c=[0]-[∞]` has exact order `n`, is killed by `I`, and has nonzero image in
the optimal Eisenstein quotient. The deep descent theorem gives

\[
J_e(\mathbb Q)=\langle c\rangle\simeq\mathbb Z/n\mathbb Z.
\]

For the torsion theorem, the stable interface needed from this long
construction is only that `Jₑ(ℚ)` is finite and that the two cusps remain
separated.

### 4.3 Semistability and local component analysis

Assume now that `N` is a prime in the remaining range and that
`P∈E(ℚ)` has order `N`.
The closure of `⟨P⟩` in a Néron model is studied prime by prime.
At an additive prime, the component group has order divisible only by two
and three, so the `N`-torsion section enters the additive identity
component. The only possible residue characteristic is then `N`. After a
ramified extension of degree at most six the curve becomes semistable, but
the map from an additive special fiber to a semiabelian special fiber is
zero. Raynaud uniqueness for finite-flat order-`N` models, with ramification
index less than `N-1`, contradicts the nonzero constant generic fiber.
Therefore `E` is semistable.

At `2` and `3`, good reduction is impossible for large `N`: the Hasse bound
would force the reduction group to have fewer than `N` points while the
prime-to-characteristic torsion point would inject. Hence reduction is
multiplicative. After an extension of residue degree at most two, the
identity component is `𝔾ₘ`, with only `2²-1=3` or `3²-1=8` points.
Consequently `P` specializes **outside** the identity component at both
small primes.

Now suppose that at some bad prime `q`, the specialization of `P` lay in the
identity component. The integral modular point
`x=(E,⟨P⟩)` would reduce to the cusp `0` at `q` and to the opposite cusp
`∞` in characteristics two and three. Map `X₀(N)` to `Jₑ`, normalized by
`∞ ↦ 0`. Since the rational image of `x` is torsion, specialization at both
two and three forces its order to be both a power of two and a power of
three; hence its image is zero. Specializing at `q` would then kill the
nonzero cusp class `[0]-[∞]`, contradicting the prime-to-characteristic
torsion-specialization theorem. It follows that `P` is outside the identity
component at every bad prime.

### 4.4 The mod-`N` representation and unramified extension

The rational cyclic subgroup gives an exact sequence of Galois modules

\[
0\longrightarrow\mathbb Z/N\mathbb Z
\longrightarrow E[N]
\longrightarrow\mu_N\longrightarrow0.
\]

Let `K=ℚ(ζ_N)` and `L=ℚ(E[N])`. Then `Gal(L/K)` is either trivial or cyclic
of order `N`, and `Gal(K/ℚ)` acts on it through the inverse cyclotomic
character.

The preceding component assertion proves that `L/K` is unramified
everywhere. At good primes away from `N`, the `N`-torsion is étale. At a
good prime over `N`, use the connected--étale decomposition. At bad primes,
the quotient model is multiplicative; Raynaud identifies the order-`N`
piece with `μ_N` at residue characteristic `N`, while it is étale
elsewhere.

Herbrand/Kummer theory rules out the required nontrivial unramified
`χ⁻¹`-extension of the cyclotomic field; in the relevant eigenspace the
Bernoulli number `B₂=1/6` is an `N`-adic unit. Hence `L=K`, so the extension
splits.

### 4.5 Finish the large-prime contradiction

After splitting, both the constant subgroup and the multiplicative
`μ_N` subgroup are available. Quotienting successively by the latter while
transporting the former constructs an unbounded chain of rational
`N`-isogenies with controlled reduction. Shafarevich finiteness, or the
corresponding modular-curve finiteness argument, forces two curves in the
chain to repeat. The resulting non-scalar rational endomorphism is
incompatible with this isogeny chain; the CM cases are handled separately.
This contradiction excludes the large prime order.

Mazur organizes this as three reductions and four final steps. A formal proof
should follow those interfaces rather than flattening the argument into one
monolithic theorem.

Mazur's Chapter III, §5 argument should not be mislabeled as a formal
immersion proof. Formal immersion at a cusp is the later
Kamienny--Merel symmetric-power method. It is indispensable for torsion over
number fields of higher degree, but for the sharp degree-one theorem it
would add Hecke-independence machinery that Mazur's two-characteristic
specialization argument does not need.

## 5. Sources

The primary source is Barry Mazur,
[“Modular curves and the Eisenstein ideal”](https://www.numdam.org/item/PMIHES_1977__47__33_0/),
*Publications Mathématiques de l'IHÉS* **47** (1977), 33--186,
DOI `10.1007/BF02684339`. The introduction states the point-order result;
Theorems 7′ and 8 on p. 35 state the point-order and group results.
Chapter II develops the Hecke and Eisenstein machinery; in particular,
`𝕋/I ≃ ℤ/nℤ` is II (9.7), the cusp order is II (11.1), and the local
Eisenstein structure is in §§14--18. Chapter III (3.1), pp. 148--151,
computes `Jₑ(ℚ)`, while III (5.1), pp. 156--160, gives the final
classification and prime-order argument.

Mazur's shorter exposition,
[“Rational points on modular curves”](https://math.mit.edu/~drew/vantage/MazurRationalPointsOnModularCurves.pdf),
Lecture Notes in Mathematics **601** (1977), 107--148, states the fifteen
groups as Theorem 1 on pp. 108--109 and packages the proof into the three
axioms/Main Lemma in §§2--3, pp. 122--134. The Weil-pairing sequence is on
pp. 125--127, semistability and small-prime analysis on pp. 127--130, the
global cusp argument on pp. 130--132, and unramifiedness on pp. 132--133.

Daniel Kubert,
[“Universal bounds on the torsion of elliptic curves”](https://doi.org/10.1112/plms/s3-33.2.193),
*Proceedings of the London Mathematical Society* (3) **33** (1976),
193--237, gives Tate-normal-form equations and the small-level case
reduction; see Theorem IV.1.2 and Table 3.

The exceptional order-thirteen calculation is Barry Mazur and John Tate,
[“Points of order 13 on elliptic curves”](https://pub.math.leidenuniv.nl/~vonkjb/other/mazur/MazurTate.pdf),
*Inventiones Mathematicae* **22** (1973), 41--49,
DOI `10.1007/BF01425572`.

For comparison rather than as the chosen route, Sheldon Kamienny,
[“Torsion points on elliptic curves and q-coefficients of modular forms”](https://eudml.org/doc/144019),
*Inventiones Mathematicae* **109** (1992), 221--229, introduced the
symmetric-power formal-immersion criterion, and Loïc Merel,
[“Bornes pour la torsion des courbes elliptiques sur les corps de nombres”](https://perso.imj-prg.fr/wp-content/uploads/merel-pub/torsion.pdf),
*Inventiones Mathematicae* **124** (1996), 437--449, used the winding
quotient to obtain uniform bounds. Merel's bound is not sharp enough to
replace Mazur's degree-one classification.
