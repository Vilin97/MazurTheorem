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
both universal fixed-level discriminant calculations are also complete.
Thus both odd-prime full-level subgroup obstructions are unconditional.

Here is a compact certificate for those two calculations. Translate the
abscissa by `-b₂/12`; polynomial discriminants are invariant under
translation, and the two-division cubic then has the form

\[
D=4X^3+2uX+v.
\]

Put

\[
\delta=8u^3+27v^2=-\Delta
\]

and define the low division polynomials

\[
\begin{aligned}
q={}&3X^4+3uX^2+3vX-\frac{u^2}{4},\\
r={}&2X^6+5uX^4+10vX^3-\frac52u^2X^2-uvX
      -\frac{u^3}{4}-v^2,\\
p={}&rD^2-q^3,\\
s={}&pq^3-r^3D^2.
\end{aligned}
\]

These are, respectively, the translated `Ψ₃`, `preΨ₄`,
`preΨ₅`, and `preΨ₇`. Let `S=D'/2`, and put

\[
h=Dr'-5q^2.
\]

Straight polynomial normalization gives the short syzygy list

\[
D'=2S,\qquad q'=3D,\qquad r+D^2=qS,
\]

\[
h=rS-q^2,\qquad hq=p+r^2,\qquad p'=5Dh. \tag{2}
\]

The only primitive resultant calculation is the cubic one

\[
\operatorname{Res}(D,D')=64\delta.
\]

Indeed,

\[
q=3XD-\frac{(D')^2}{16}
\]

implies

\[
\operatorname{Res}(D,q)=-\delta^2.
\]

Reducing `r+D²=qS` modulo `q` then gives

\[
\operatorname{Res}(r,q)=\delta^4.
\]

All signs here follow from the standard convention
`\operatorname{Res}(f,g)=(-1)^{\deg f\deg g}\operatorname{Res}(g,f)`;
all displayed degree products are even except the explicitly retained
minus sign in `Res(D,q)`.

Now reduce `p=rD²-q³` successively modulo `D`, `q`, and `r`. Multiplicativity
of resultants gives

\[
\operatorname{Res}(p,D)=\delta^6,\qquad
\operatorname{Res}(p,q)=\delta^8,\qquad
\operatorname{Res}(p,r)=\delta^{12}.
\]

Taking the resultant with `p` in `hq=p+r²` gives

\[
\operatorname{Res}(p,h)\operatorname{Res}(p,q)
 =\operatorname{Res}(p,r)^2,
\]

and hence `Res(p,h)=δ¹⁶`. Since `p'=5Dh`, while `p` has
degree twelve and leading coefficient five,

\[
\operatorname{Res}(p,p')
 =5^{12}\delta^{22}
 =5\,\operatorname{disc}(p).
\]

Therefore

\[
\operatorname{disc}(p)=5^{11}\delta^{22}
 =5^{11}\Delta^{22}.
\]

The seventh-division calculation reuses the same small resultants. Set

\[
g=p-r^2,\qquad
J=2pq^2-r^3S-r^2q^2.
\]

Differentiating `s` and using (2) yields two remarkably short identities:

\[
s'=7DJ,\qquad qJ=2s+r^2g. \tag{3}
\]

The defining recurrences give the following reductions:

\[
\begin{array}{c|c}
\text{modulus}&s\text{ modulo that modulus}\\ \hline
D&-q^6\\
q&-r^3D^2\\
r&-q^6\\
g&-r^4.
\end{array}
\]

For the last line, first note that `g≡-q³ (mod r)`, so
`Res(g,r)=δ¹²`. The table and multiplicativity now give

\[
\operatorname{Res}(s,D)=-\delta^{12},\quad
\operatorname{Res}(s,q)=\delta^{16},\quad
\operatorname{Res}(s,r)=\delta^{24},\quad
\operatorname{Res}(s,g)=\delta^{48}.
\]

Apply `Res(s,-)` to the second identity in (3):

\[
\operatorname{Res}(s,q)\operatorname{Res}(s,J)
 =\operatorname{Res}(s,r)^2\operatorname{Res}(s,g).
\]

Ellipticity gives `δ≠0`, so cancellation yields
`Res(s,J)=δ⁸⁰`. The first identity in (3) therefore gives

\[
\operatorname{Res}(s,s')
 =7^{24}\operatorname{Res}(s,D)\operatorname{Res}(s,J)
 =-7^{24}\delta^{92}.
\]

The polynomial `s` has degree twenty-four and leading coefficient seven;
the discriminant sign `(-1)^{24\cdot23/2}` is positive. Dividing by that
leading coefficient proves

\[
\operatorname{disc}(s)=-7^{23}\delta^{92}
 =-7^{23}\Delta^{92}.
\]

Thus the apparent degree-24 determinant is reduced to one cubic
discriminant and a fixed list of sparse polynomial identities. This is
the certificate architecture selected for Lean: every equality is checked
by the kernel, and no opaque evaluator is needed.

### 3.3 Possible point orders

The element `(0,1)` in the invariant-factor presentation has order `b`.
Mazur's point-order theorem says that a rational torsion point has order

\[
b\in\{1,2,3,4,5,6,7,8,9,10,12\}.
\]

The elementary divisor-closure part of this statement is already
machine-checked. If a positive integer `n` is outside the displayed set,
choose its least divisor outside the set. A prime choice is at least
eleven. If the choice is composite, both proper factors are allowed and
at most twelve, so a finite classification below 145 gives exactly

\[
14,15,16,18,20,21,24,25,27,35,49.
\]

If a finite-order point has order divisible by one of these numbers (or by
a prime at least eleven), multiplying it by the complementary quotient
produces a point of exactly that order. Thus the remaining geometric
point-order proof has a precise interface: exclude all prime orders at
least eleven and those eleven minimal composite orders. This is
`exists_prime_or_kubertForbiddenOrder_dvd` followed by
`addOrderOf_mem_cyclicOrders_of_order_obstructions`.

The compiled rational wrapper
`rationalTorsion_orders_mem_cyclicOrders_of_obstructions_except_sixteen`
already substitutes the unconditional level-sixteen proof into this divisor
argument.  Its remaining composite callback therefore ranges over the ten
members different from sixteen, rather than silently asking a caller to
reprove that finished case.

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

The Lean implementation now reaches the same two obstructions directly,
without first constructing quotient isogenies or modular curves.

For `C₂ × C₁₀`, the Chinese remainder theorem extracts full rational
two-torsion and a rational point `Q` of exact order five. A coordinate
change sends `Q` to `(0,0)` on Tate normal form

\[
y^2+(1-c)xy-by=x^3-bx^2.
\]

The tangent and chord formulas give

\[
2Q=(b,bc),\qquad 3Q=(c,b-c).
\]

Since `5Q=0`, one has `3Q=-2Q`; equality of abscissas forces `b=c`.
The coordinate change retains a nonzero scale `u` and gives

\[
u^{12}\Delta_E=c^5(c^2-11c-1). \tag{4}
\]

Full rational two-torsion supplies three distinct rational roots
`r₁,r₂,r₃` of the two-division cubic. Its discriminant calculation is
the Vandermonde square

\[
\Delta_E=
\left(4(r_1-r_2)(r_1-r_3)(r_2-r_3)\right)^2.
\]

Writing `Δ_E=d²` in (4) and dividing by `c⁴` therefore produces

\[
\left(\frac{u^6d}{c^2}\right)^2=c^3-11c^2-c. \tag{5}
\]

Write `c=m/n` in lowest terms with `n>0`. Clearing denominators in (5)
shows that

\[
mn(m^2-11mn-n^2)
\]

is a square. The three factors are pairwise coprime; the only apparently
exceptional zero factor would imply a square equal to five times a square
and is impossible. Splitting the signs of the three coprime factors then
reduces every surviving case, after possibly exchanging `m` and `n`, to

\[
e^2=X^4-11X^2Y^2-Y^4,\qquad
\gcd(X,Y)=1,\quad XY\ne0. \tag{6}
\]

All steps through (6), including the denominator and sign bookkeeping,
are machine-checked. The final quartic obstruction is also machine-checked
by the following elementary infinite descent.

Normalize a hypothetical solution so that `X,Y>0` and `e≥0`, and choose
one with `Y` minimal. A complete calculation modulo eight says that `X`
and `e` are odd and that `4∣Y`. In particular, write `Y=2z` with `z>0`
and put

\[
A=2X^2-11Y^2.
\]

The quartic equation gives

\[
A^2=(2e)^2+125Y^4,\qquad A>2e\ge0. \tag{7}
\]

Oddness makes the following two numbers integral, and the strict
inequality in (7) makes them positive:

\[
D_+=\frac{A+2e}{4},\qquad
D_-=\frac{A-2e}{4}.
\]

Their product and sum are

\[
D_+D_-=125z^4,\qquad
D_++D_-=X^2-22z^2. \tag{8}
\]

They are coprime. Indeed, let a prime `p` divide both. If `p∣z`, the sum
in (8) implies `p∣X`, contradicting `gcd(X,z)=1`. Otherwise the product
forces `p=5`. Reducing the sum modulo five then gives
`X²=2z²`; since two is a nonsquare modulo five, this forces
`5∣z` and then `5∣X`, again a contradiction.

Exactly one of `D_+` and `D_-` is therefore divisible by five. Multiplying
that factor by five turns (8) into a product of two coprime integers equal
to `(5z)⁴`. Unique factorization in the integers splits the factors into
fourth powers. After interchanging their names if necessary, there are
coprime nonzero integers `a,b` such that

\[
\{D_+,D_-\}=\{a^4,125b^4\},\qquad
z^2=(ab)^2.
\]

Substituting these identities into the sum in (8) produces the primitive
Pythagorean triple

\[
X^2=(a^2+11b^2)^2+(2b^2)^2.
\]

The two legs are coprime, the first is odd, and both are positive.
The standard primitive Pythagorean parametrization therefore gives
coprime positive integers `m,n` with

\[
a^2+11b^2=m^2-n^2,\qquad b^2=mn.
\]

Since a product of the coprime positive integers `m,n` is a square, write
`m=u²` and `n=v²`, with `u,v` coprime and nonzero. The preceding equations
then give

\[
a^2=u^4-11u^2v^2-v^4. \tag{9}
\]

Thus `(u,v,a)` is another primitive nonzero solution of (6). Moreover,
`b²=(uv)²` and `z²=(ab)²`, so

\[
|v|\le |b|\le |z|<2|z|=Y.
\]

This contradicts the minimal choice of `Y`. In Lean the descent step is
`exceptional_quartic_descent_step`; `Nat.find` chooses the least
`Int.natAbs` of the second coordinate, and
`ExceptionalTwoTen.noExceptionalQuartic` closes the contradiction.

For `C₂ × C₁₂`, choose three distinct nonzero two-torsion points with
abscissas `r₁,r₂,r₃`, a point `P` satisfying `2P=T₁`, and a nonzero
three-torsion point `Q`. Put

\[
A=r_1-r_2,\quad B=r_1-r_3,\quad
z=x(P)-r_1,\quad \xi=x(Q)-r_1.
\]

The compiled halving identity and translated three-division equation give

\[
AB=z^2
\]

and

\[
3\xi^4+4(A+B)\xi^3+6AB\xi^2-(AB)^2=0. \tag{10}
\]

Set

\[
t=\frac{\xi}{z},\qquad
S=\frac{A+B}{z},\qquad
D=\frac{A-B}{z}.
\]

Distinctness of the torsion points gives `z,t,D≠0`; equations (10) become

\[
S^2-D^2=4,\qquad
3t^4+4St^3+6t^2-1=0.
\]

Squaring the second equation and eliminating `S` gives

\[
(4t^3D)^2=(t^2-1)^3(9t^2-1).
\]

The same identity proves `t²≠1` and `9t²≠1`. Thus

\[
w=\frac{4t^3D}{t^2-1}
\]

is nonzero and satisfies

\[
w^2=(t^2-1)(9t^2-1). \tag{11}
\]

There is an explicit map from a nondegenerate point of (11) to

\[
Y^2=(X-10)(X-6)(X+6):
\qquad
X=\frac{2(w+1)}{t^2},\quad
Y=\frac{2(X-10)}t. \tag{12}
\]

It also records

\[
t^2(X^2-36)=4(X-10).
\]

Consequently it is enough to prove that the affine rational points of the
displayed cubic have

\[
X\in\{-6,2,6,10,18\}.
\]

This is not a new elliptic curve: under

\[
X=4x+2,\qquad Y=8y,
\]

the displayed cubic becomes exactly

\[
y^2=x^3-x^2-4x+4,
\]

the displayed `X₀(24)` model above. The required `X`-coordinate list is
equivalent to `x∈\{-2,0,1,2,4\}`.

Substitution in the last relation then forces exactly the degenerate cases
excluded above. The complete reduction (10)--(12), including extraction of
all five torsion points from an injective `C₂×C₁₂`, is machine-checked.
The remaining fixed cubic has now been pushed substantially farther in
Lean. Write it in the translated form

\[
E:y^2=u(u^2+2u-3)=u(u-1)(u+3)
\]

and introduce the two-isogenous companion

\[
E':Y^2=X(X^2-4X+16).
\]

The first denominator calculation proves that every rational abscissa on
`E'` is a square. Indeed, for `X=m/n` in lowest terms the curve equation
gives a square product

\[
(mn)(m^2-4mn+16n^2)=C^2.
\]

Every common divisor of the two displayed factors divides `16`. Splitting
off their gcd shows that `mn` is either a square or twice a square. The
twice-a-square alternative gives

\[
q^2=2(U^4-2U^2W^2+4W^4)
\]

with coprime `U,W`; its residues modulo `16` are impossible. Hence `X` is
a rational square.

For a nonzero rational abscissa `u=m/n` on `E`, the analogous product is

\[
(mn)(m^2+2mn-3n^2)=C^2.
\]

Here a common divisor of the two factors divides `3`. The same coprime
factor argument gives exactly four possible rational square classes:

\[
u\in \mathbb Q^{\times2},\quad
-\mathbb Q^{\times2},\quad
3\mathbb Q^{\times2},\quad
-3\mathbb Q^{\times2}. \tag{13}
\]

This square-class calculation is constructive enough to reverse
duplication. If `u=s²`, put `t=y/s`, so
`t²=u²+2u-3`, and define

\[
X=2+2u-2t,\qquad Y=2sX.
\]

Then `(X,Y)∈E'(ℚ)`, so the previous paragraph writes `X=q²`. Set

\[
v=-1+\frac X2-\frac{Y}{2q},\qquad w=qv.
\]

A direct chord-and-tangent calculation proves `(v,w)∈E(ℚ)` and
`2(v,w)=(u,y)`. For the other three classes in (13), subtract respectively

\[
D=(-1,2),\qquad F=(3,6),\qquad T=(0,0);
\]

the abscissa of the difference becomes a square, so the same reverse
duplication applies. Consequently every rational point belongs to one of
four cosets:

\[
E(\mathbb Q)=2E(\mathbb Q)\ \cup\
(D+2E(\mathbb Q))\ \cup\
(F+2E(\mathbb Q))\ \cup\
(T+2E(\mathbb Q)). \tag{14}
\]

Thus `[E(ℚ):2E(ℚ)]≤4`, in particular the doubling image has finite index.
The formal naïve-height parallelogram estimate, rational Northcott
finiteness, and abstract descent theorem now imply that `E(ℚ)` is finitely
generated. Its points killed by two are exactly

\[
O,\ (0,0),\ (1,0),\ (-3,0),
\]

so `#E(ℚ)[2]=4`. For any finitely generated commutative group,

\[
[G:nG]=n^{\operatorname{rank}G}\#G[n].
\]

Applying this with `n=2` to (14) gives

\[
4\ge [E(\mathbb Q):2E(\mathbb Q)]
  =2^{\operatorname{rank}E(\mathbb Q)}\cdot4.
\]

Hence the rank is zero, and finite generation then makes `E(ℚ)` finite.
All steps through this finiteness statement are machine-checked.

Rank zero by itself does not exclude an odd torsion factor or higher
two-power torsion, so a logically separate cardinality argument is still
needed.  The compiled good-reduction certificate supplies it.  Direct
enumeration gives `#E(𝔽₅)=8`; the exact-pin reduction theorem is injective
on the now-finite rational point group, and therefore `#E(ℚ)≤8`.  The eight
explicit rational points listed below inject into this group and hence
exhaust it.  This closes `ExceptionalCubicIsTrivial` and the
`C₂ × C₁₂` obstruction unconditionally.

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
once the point-order theorem is available.  Both exceptional product
branches, including the eight-point bound for the `C₂ × C₁₂` cubic, are
now closed.

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
The local formal foundation now performs the normalization with its
discriminant scale, checks the coordinates through explicit `5P`, and
provides a denominator-aware recurrence for `Q+P` used to compute `6P`.
These are algebraic inputs to the small-level modular equations, not a
claim that their rational points have already been classified.

The order-fourteen branch is now explicit far enough to display the whole
remaining argument.  Normalize a point `P` of exact order fourteen to

\[
E_{b,c}:y^2+(1-c)xy-by=x^3-bx^2,\qquad P=(0,0).
\]

Write

\[
\begin{aligned}
A&=c^2+c-b,&
B&=b^2-bc-c^3,\\
C&=2b^2-bc^2-3bc+c^2,&
D&=b^3-3b^2c+bc^3+3bc^2-c^5-c^4-c^3.
\end{aligned}
\]

The addition recurrence, checked at the level of nonsingular affine
points, gives

\[
x(7P)=-\frac{bcAC}{B^2},\qquad
y(7P)=\frac{b^2A^2D}{B^3}. \tag{15}
\]

None of `b,c,b-c,A,B,C` may vanish.  For example, vanishing of `A`
makes the abscissa of `5P` zero, so `5P=P` or `5P=-P`; either alternative
makes `4P` or `6P` zero.  Vanishing of `B` similarly compares `6P` with
`±P`, and vanishing of `C` compares `7P` with `±P`.  Each conclusion
contradicts exact order fourteen.  The earlier factors are treated by the
same checked `2P` and `3P` formulas.

Now `7P` has exact order two.  On Tate normal form, a point `(x,y)` is its
own negative exactly when

\[
2y+(1-c)x-b=0.
\]

Insert (15), multiply by `B³/b`, and use the established nonvanishing:

\[
2bA^2D-(1-c)cACB-B^3=0. \tag{16}
\]

This implication, together with the scale identity
`u¹²Δ_E=Δ(E_{b,c})`, is the compiled
`exists_tateOrderFourteen_certificate`.

For orientation, put `q=-b`, so the normal equation is
`y²+(1-c)xy+qy=x³+qx²`.  A classical birational model for (16) is

\[
C_{14}:s^2+st+s=t^3-t.
\]

The forward transformation, with `a=1-c`, is

\[
a=
\frac{t^4-st^3+(2s-4)t^2-st+1}
 {(t+1)(t^3-2t^2-t+1)}
\]

and

\[
q=
\frac{-t^7+2t^6+(2s-1)t^5+(-2s-1)t^4
      +(-2s+2)t^3+(3s-1)t^2-st}
 {(t+1)^2(t^3-2t^2-t+1)^2}. \tag{17}
\]

For the formal proof it is substantially smaller to use the inverse map
directly.  On the exact-order Tate locus it is

\[
\begin{aligned}
t&=\frac{D}{(b-c)C},\\
U&=4(t+1)=\frac{4\bigl(D+(b-c)C\bigr)}{(b-c)C},\\
V&=\frac{4(b-2c^2-c)B}{bA^2}. \tag{17a}
\end{aligned}
\]

All denominators in (17a) were already proved nonzero.  Clearing them
reduces `V²=U(U²-11U+32)` to (16) times an explicit polynomial.  The same
calculation also keeps the image away from the six rational points below.
Indeed, `U=8` would give

\[
D-(b-c)C=AB=0,
\]

contrary to the nonvanishing of `A` and `B`.  If `U=4`, then `D=0`;
if `U=0`, then `D+(b-c)C=0`.  Bézout identities in `b` for these two
possibilities and (16) have resultants `-c³³` and `4c³¹`,
respectively, so either one contradicts `c≠0`.

The open modular locus also requires

\[
t(t-1)(t+1)(t^3-9t^2-t+1)
  (t^3-2t^2-t+1)\ne0. \tag{18}
\]

Here is an elementary proof of the required rational-point classification.
Set

\[
U=4(t+1),\qquad V=4(2s+t+1).
\]

Then

\[
V^2=U(U^2-11U+32), \tag{19}
\]

and its two-isogenous curve is

\[
W^2=Z(Z^2+22Z-7). \tag{20}
\]

For (19), the standard squareclass map has possible values
`±1,±2`, because the constant term is `32`.  The quadratic
`U²-11U+32` has discriminant `-7` and is everywhere positive; hence a
rational point must have `U≥0`, eliminating the negative classes.  Both
remaining classes are represented by the identity and `(0,0)`, so this
image has order two.

For (20), only `±1,±7` can occur.  The classes `-1` and `7` would give,
after choosing coprime numerator and denominator `m,n`,

\[
\begin{aligned}
w^2&=-m^4+22m^2n^2+7n^4,\\
\text{or}\qquad
w^2&=7m^4+22m^2n^2-n^4.
\end{aligned} \tag{21}
\]

If exactly one of `m,n` is odd, either right-hand side is `7 mod 8`.
If both are odd, it is `12 mod 16`.  These are not square residues, and
coprimality excludes both even.  Thus the dual image is exactly
`{1,-7}`, again of order two.  The two-isogeny index formula is therefore

\[
4\cdot2^{\operatorname{rank}C_{14}(\mathbb Q)}
=2\cdot2,
\]

so the rank is zero.

The curve has good reduction at three and exactly six points over
`𝔽₃`.  Torsion specialization is injective; meanwhile `(t,s)=(1,0)`
generates six visible rational points.  Consequently

\[
C_{14}(\mathbb Q)=
\{O,(1,0),(0,0),(-1,0),(0,-1),(1,-2)\}.
\]

Every one violates (18), so all is cuspidal and exact order fourteen is
impossible.  This entire branch is now compiled.  `OrderFourteenModel`
checks the cleared identities in (17a) and proves that its image avoids
`U=0,4,8`; `XOneFourteenDescent` checks the two-isogeny descent, two doubling
cosets, finite generation, rank-zero argument, finiteness, and six visible
points; and `XOneFourteenReduction` proves injectivity at three and the
six-point finite-field count.  Their composition is
`no_rational_point_of_order_fourteen`.

The order-fifteen branch has an analogous genus-one endgame.  Its standard
affine modular model is

\[
C_{15}:s^2+st+s=t^3+t^2.
\]

The integral change

\[
U=4(t+1),\qquad V=4(2s+t+1)
\]

identifies it with

\[
E_{15}:V^2=U(U^2-7U+16), \tag{21a}
\]

whose two-isogenous curve is

\[
E'_{15}:W^2=Z(Z^2+14Z-15). \tag{21b}
\]

Here is the elementary two-isogeny descent.  On `E₁₅`, clearing a rational
abscissa into coprime numerator and denominator shows that its squareclass
is initially `1` or `2`.  The second class would give the primitive quartic

\[
N^2=2A^4-7A^2B^2+8B^4.
\]

Its right-hand side is a nonsquare modulo eight or sixteen in every
primitive parity case, so every nonzero abscissa on `E₁₅` is a square.
On the dual curve, the possible classes are
`±1,±3,±5,±15`.  The classes `-1`, `3`, `-5`, and `15` lead to four
primitive quartics with the same modulo-sixteen obstruction.  Thus the
dual image is exactly represented by `1,-15,5,-3`.

The reverse-doubling calculation is explicit.  The first two dual classes
give a direct half on `E₁₅`; translation by the visible point

\[
G=(4,4)
\]

turns the remaining classes `5` and `-3` into those direct cases.  Therefore

\[
E_{15}(\mathbb Q)=2E_{15}(\mathbb Q)
 \;\cup\; \bigl(G+2E_{15}(\mathbb Q)\bigr). \tag{21c}
\]

Naïve-height descent makes the group finitely generated.  Its rational
two-torsion consists exactly of the identity and `T=(0,0)`, so the index
formula applied to (21c) gives

\[
2\ge [E_{15}(\mathbb Q):2E_{15}(\mathbb Q)]
=2^{\operatorname{rank}E_{15}(\mathbb Q)}\cdot2.
\]

Hence the rank is zero and the rational point group is finite.  To sharpen
this to the four visible points, reduce at seven: direct enumeration gives
eight points over `𝔽₇`, so rational torsion injects into a group of order
eight.  It remains only to exclude a rational point `Q` of order eight.
The normalized duplication identity is

\[
x(2Q)(2y(Q))^2=(x(Q)^2-16)^2.
\]

Writing `R=2Q`, uniqueness of nonzero rational two-torsion gives
`2R=T`.  The same identity forces `x(R)^2=16`; the value `-4` would require
a rational square equal to `-240`, hence `x(R)=4`.  Applying the identity
once more and using (21a), with `x=x(Q)`, gives

\[
x^4-16x^3+80x^2-256x+256=0. \tag{21d}
\]

This polynomial is monic, so a rational root is integral.  Its reduction
has no root in `𝔽₁₇`, a finite check, and therefore (21d) has no rational
root.  A finite abelian group of order at most eight containing `G` of
order four has order four or eight.  If it had order eight while its
two-torsion had cardinality two, the order-eight classification would make
it cyclic and produce the excluded point of order eight.  Consequently

\[
E_{15}(\mathbb Q)=\{O,(0,0),(4,4),(4,-4)\}.
\]

Equivalently,
`C₁₅(ℚ)={O,(0,0),(-1,0),(0,-1)}`; these are precisely the cuspidal
points.  The two-isogeny descent through finiteness is compiled in
`XOneFifteenDescent`; the Tate-parameter inverse map and sharp
reduction/order-eight enumeration are also compiled.  Thus exact rational
order fifteen is excluded without a callback.

The order-eleven Tate calculation now has an equally explicit model bridge,
though its final rank-zero step remains open.  Normalize an exact
order-eleven point to `P=(0,0)`.  The equality `6P=-5P`, using the checked
coordinates of both multiples, gives

\[
(b-c)^3(b^2-bc-c^3)-bc(c^2+c-b)^3=0. \tag{21e}
\]

Every factor divided by below is proved nonzero from exact order.  Put

\[
r=\frac bc,\qquad q=\frac{c^2}{b-c},\qquad
N=rq-2r+1,\qquad K=q^2-q-r+1.
\]

After clearing `c` and `b-c`, equation (21e) becomes

\[
r^2-rq^3+3rq^2-4rq+q=0. \tag{21f}
\]

The rational functions

\[
U=\frac K N,\qquad V=\frac{(q-r)K}{N^2}-1 \tag{21g}
\]

satisfy

\[
V^2+V=U^3-U^2. \tag{21h}
\]

Identity (21f) also proves `N≠0`, `K≠0`, and `q-r≠0`; consequently
`U≠0,1`.  The compiled theorem therefore sends every exact
order-eleven point to a non-cusp affine point on this standard model of
`X₁(11)`.  Conversely, the five visible rational points are the point at
infinity together with `(0,0)`, `(0,-1)`, `(1,0)`, and `(1,-1)`.
Reduction modulo three has exactly the same five points.  Once
`X₁(11)(ℚ)` is known finite, good reduction injects it into this
five-element group, so the visible points exhaust the rational locus and
contradict `U≠0,1`.

The global descent has now been reduced to one explicit finite-coset
statement.  Write `E₁₁` for (21h) and `P₀=(0,0)`.  Direct additions give

\[
2P_0=(1,-1),\quad 3P_0=(1,0),\quad
4P_0=(0,-1),\quad 5P_0=O,
\]

so `P₀` has exact order five.  The degree-five quotient predicted by
Vélu's formulas is

\[
E' : y^2+y=x^3-x^2-10x-20,
\]

with rational functions

\[
x'=x+\frac1{x^2}+\frac{2x-1}{(x-1)^2},\qquad
y'=y-\frac{2y+1}{x^3}
       -\frac{x(2y+1)}{(x-1)^3}. \tag{21i}
\]

Lean verifies by a factored polynomial identity that (21i) maps the
equation of `E₁₁` to the equation of `E'` whenever `x≠0,1`.  Extending it
by sending `O` and the four points with `x=0` or `1` to `O` gives a total
point function with exactly that affine zero fibre.  Additivity of this
raw function has not been assumed.  The accompanying Kummer function for
the five-isogeny calculation is

\[
f(x,y)=\frac{y^2(y+x)}{(x-1)^2}. \tag{21j}
\]

The part of the Mordell--Weil argument after the Selmer computation is
already complete.  Good reduction modulo three is injective on
`E₁₁(ℚ)[5]`; the reduced curve has five points, and the five multiples
above are distinct.  Therefore

\[
\#E_{11}(\mathbb Q)[5]=5. \tag{21k}
\]

It remains to prove precisely

\[
\forall P\in E_{11}(\mathbb Q)\quad
\exists\,i\in\{0,1,2,3,4\},\ Q\in E_{11}(\mathbb Q),
\qquad P=iP_0+5Q. \tag{21l}
\]

Assuming (21l), the five points `iP₀` surject onto
`E₁₁(ℚ)/5E₁₁(ℚ)`, so this quotient has at most five elements.  A checked
five-fold naïve-height descent proves finite generation from this finite
index: repeated use of the approximate parallelogram law yields

\[
25h(P)-C_0\le h(5P)
\]

and a translate estimate `h(P)≤2h(G+P)+C_G`.  The finitely generated
abelian-group formula then gives

\[
[E_{11}(\mathbb Q):5E_{11}(\mathbb Q)]
 =5^{\operatorname{rank}E_{11}(\mathbb Q)}
  \#E_{11}(\mathbb Q)[5].
\]

By (21k) and the upper bound five, the rank is zero.  Finite generation
then makes the point group finite, so reduction modulo three shows that
the five displayed points exhaust it.  This contradicts the non-cusp
point constructed from order eleven.  Thus (21l)—the explicit
five-isogeny Selmer coset computation—is the sole honest missing
level-eleven input; a finite-field count alone does not supply it.

The order-thirteen branch reaches an analogous but genuinely genus-two
boundary.  Exact order thirteen gives `7P=-6P` on Tate normal form.
Writing

\[
A=c^2+c-b,\quad B=b^2-bc-c^3,\quad
C=2b^2-bc^2-3bc+c^2,
\]

the checked coordinates yield

\[
(b-c)B^3+bcA^3C=0. \tag{X13-a}
\]

Every factor subsequently divided by is proved nonzero from exact order.
Set `r=b/c` and `s=c²/(b-c)`.  Then

\[
\begin{aligned}
0={}&r^3+
(-s^4+5s^3-9s^2+4s-2)r^2\\
&+(-s^3+6s^2-3s+1)r-s^3. \tag{X13-b}
\end{aligned}
\]

The rational transformation

\[
x=-\frac{(r-1)(s-1)}{r-s}
\]

together with the explicitly completed-square ordinate sends (X13-b) to

\[
C_{13}:\quad
y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1. \tag{X13-c}
\]

The retained factors prove `x≠0,-1`; these are precisely the two affine
cusp abscissae relevant to the forward map.  Thus an order-thirteen point
would give a noncuspidal rational point on `C₁₃`.

The sextic has the checked order-six symmetry

\[
\sigma(x,y)=
\left(-\frac1{x+1},\frac{y}{(x+1)^3}\right),\qquad
\sigma^3(x,y)=(x,-y). \tag{X13-d}
\]

On the noncuspidal chart its quotient invariants

\[
u=\frac{x^3-3x-1}{x(x+1)},\qquad
v=\frac{y}{x(x+1)}
\]

satisfy `v²=u²+2u+5`.  Every quotient point except `u=-1` is
parameterized by

\[
u=\frac{t^2+4t-1}{1-t^2},\qquad
v=\frac{2(1+t^2)}{1-t^2}. \tag{X13-e}
\]

The exceptional value would make `x` a rational root of the monic cubic
`x³+x²-2x-1`; reduction modulo two rules this out.  The three abscissae in
a symmetry orbit are the roots of

\[
z^3-uz^2-(u+3)z-1, \tag{X13-f}
\]

whose discriminant is `(u²+3u+9)²`.  Write the canonical parameter as
`t=m/n`, with `m,n` coprime and `n>0`.  Clearing denominators in
(X13-f) gives a homogeneous cyclic cubic, and the square root of its
discriminant is

\[
D(m,n)=
7m^4-4m^3n+2m^2n^2+4mn^3+7n^4. \tag{X13-g}
\]

Now use coordinates `a+bρ`, where `ρ²-ρ+1=0` and
`N(a+bρ)=a²+ab+b²`.  For

\[
a=m^2+4mn-n^2,\qquad b=3(n^2-m^2)
\]

one has `N(a+bρ)=D(m,n)`.  Moreover

\[
19=(3+2\rho)(5-2\rho),
\]

and direct lattice algebra proves

\[
\begin{aligned}
(3+2\rho)\mid(a+b\rho)&\Longleftrightarrow19\mid(5a+2b),\\
(5-2\rho)\mid(a+b\rho)&\Longleftrightarrow19\mid(3a-2b).
\end{aligned}
\]

A complete check over `ZMod 19` shows that both divisibilities would force
`19∣m,n`, contradicting primitivity.  This is the local split-prime data
needed by the Mazur--Tate descent.

There is also an exact function-field certificate.  Independently
computed polynomials `H,K∈ℤ[x]`, of degrees nineteen and sixteen, satisfy

\[
H^2-f_{13}K^2=-4, \tag{X13-h}
\]

where `f₁₃` is the sextic in (X13-c).  Lean expands and verifies
(X13-h) exactly.  On the reciprocal infinity chart the identity becomes

\[
H_\infty(z)^2-
 f_{\infty}(z)K_\infty(z)^2=-4z^{38};
\]

the boundary values distinguish the two infinity branches.  In divisor
language this is the certificate underlying

\[
\operatorname{div}(H+yK)=19(\infty_--\infty_+).
\]

The exact pin lacks a genus-two divisor/Picard/Jacobian implementation, so
that last interpretation is not yet a Lean theorem.  After it, the
remaining global steps are the Mazur--Tate surjectivity of the prime
`3+2γ₂` on `J₁(13)(ℚ)`, the computation that its rational torsion is
cyclic of order nineteen, and Ogg's assertion that the Abel--Jacobi image
meets this subgroup only at the six cusps.  These are stated as the
remaining proof obligations, not assumed.

The cyclic orders twenty and twenty-four are now excluded by the following
short two-isogeny argument.  Treat both as order `2m`, with `m=10` or `12`.  If `Q` has
that order, then

\[
T=mQ
\]

is its nonzero point of order two.  Translate `T` to `(0,0)` and complete
the square, obtaining

\[
E:y^2=x(x^2+ax+b).
\]

The admissible change, transformed-curve equality, normalized origin, and
additive point equivalence are packaged by the compiled
`TwoTorsionNormalization.Data`; its pullback lemmas preserve exact order
and transport the relation `mQ=T`.

The standard two-isogenous curve and the quotient functions are

\[
\begin{aligned}
E'&:Y^2=X(X^2-2aX+a^2-4b),\\
\phi(x,y)&=
\left(\frac{y^2}{x^2},
      \frac{y(b-x^2)}{x^2}\right).
\end{aligned} \tag{21m}
\]

The denominator-free point definition sends both infinity and `(0,0)` to
infinity.  Direct substitution proves that (21m) lands on `E'`; another
coordinate calculation proves that its only rational kernel points are
exactly those two.  Translation by `(0,0)` is

\[
(x,y)\longmapsto
\left(\frac bx,-\frac{by}{x^2}\right),
\]

and leaves (21m) unchanged.  The checked dual formulas satisfy both

\[
\widehat\phi(\phi(P))=2P,\qquad
\phi(\widehat\phi(P'))=2P' \tag{21n}
\]

for every rational point, with the zero, kernel, and non-kernel cases
handled separately.

No general additivity theorem for the raw point function is needed.
Substituting one composite identity into the other proves directly

\[
\phi(2P)=2\phi(P),\qquad
\widehat\phi(2P')=2\widehat\phi(P'), \tag{21o}
\]

and induction gives compatibility with every power-of-two multiple.

Suppose first that `Q` has order twenty.  In the normalized model
`10Q=(0,0)`.  Put

\[
S=\phi(5Q),\qquad A=\phi(4Q).
\]

Equation (21o) shows `2S=0`.  If `S=0`, the exact kernel would give
`10Q=0`, impossible; hence `S` has order two.  It cannot be the target
origin `T'=(0,0)`, because applying the dual and (21n) to `S=T'` would
again give `10Q=0`.  Four iterations of (21o), together with `20Q=0`,
give `16A=A`, so `15A=0`.  If `3A=0`, then `4A=A`; applying the dual and
using (21o) gives `32Q=8Q`, and hence `24Q=0`, contradicting exact order
twenty.  Thus `R=3A` has exact order five.  Since `S` and `R` have
coprime orders, `C=S+R` has exact order ten, and `5C=S`.

For exact order twenty-four, normalize so that `12Q=(0,0)` and put

\[
S=\phi(6Q),\qquad B=\phi(3Q),\qquad A=\phi(8Q).
\]

The same kernel argument makes `S` a nonzero order-two point distinct
from `T'`.  Equation (21o) gives `2B=S`; hence `B` has exact order four.
It also gives `4A=A`, so `3A=0`; the exact kernel and `16Q≠0` show
`A≠0`, and therefore `A` has exact order three.  Consequently `C=B+A`
has exact order twelve and `6C=S`.

In either case, the unique nonzero order-two point in the cyclic group
`⟨C⟩` is its half, namely `S`.  Since `T'≠S`, we have `T'∉⟨C⟩`.
The two `ZMod` generator maps therefore combine into an injection
`ZMod 2 × ZMod m → E'(ℚ)`, with `m=10` or `12`.  These contradict the
unconditional `C₂×C₁₀` and `C₂×C₁₂` obstructions.  The normalization,
both composite identities, all fixed-multiple calculations, independence
proofs, and product generation are machine-checked; no unproved
isogeny-to-homomorphism interface is used.

The order-twenty-one arithmetic has also been isolated on the standard
conductor-21 model

\[
E_{21}:y^2+xy=x^3-4x-1. \tag{X21-a}
\]

Completing the square with

\[
V=4x+1,\qquad W=8y+4x
\]

gives an affine equivalence with

\[
W^2=V(V-9)(V+7). \tag{X21-b}
\]

Here is the complete elementary two-descent up to its two global leaves.
For `V≠0`, write `V=m/n` in lowest terms.  Clearing the denominator in
(X21-b) gives

\[
(Wn^2)^2=(mn)(m^2-2mn-63n^2). \tag{X21-c}
\]

Any common divisor of the two factors on the right divides `63`: from a
common divisor one obtains divisibility of `m³` and `63n³`, and
coprimality of `m,n` cancels the latter cube.  Divide by the gcd in
(X21-c).  The resulting coprime factors multiply to a square, so each is
a signed square.  Since the positive gcd divides `63`, its squarefree part
is one of `1,3,7,21`.  Consequently

\[
V\in\{\pm r^2,\ \pm3r^2,\ \pm7r^2,\ \pm21r^2\}. \tag{X21-d}
\]

If `V=dr²` and `r=m/n` is again canonical and primitive, clearing
denominators gives the precise homogeneous space

\[
c^2=d(dm^2-9n^2)(dm^2+7n^2). \tag{X21-e}
\]

Primitivity says at least one of `m,n` is odd.  Exhaustion in
`ZMod 16` proves that (X21-e) has no such solution for `d=-1` or `d=3`.
The other branches are paired by translation by `(0,0)`:

\[
\tau(V,W)=
\left(-\frac{63}{V},\frac{63W}{V^2}\right). \tag{X21-f}
\]

Direct substitution proves that `τ(V,W)` again satisfies (X21-b).
Using (X21-f), all surviving branches reduce to `d=1` and `d=-3`.
After removing the forced square factor in the second branch, the two
remaining primitive statements are

\[
\begin{aligned}
c^2&=m^4-2m^2n^2-63n^4
  \Longrightarrow m=0\ \lor n=0\ \lor m^2=9n^2,\\
c^2&=-3m^4-2m^2n^2+21n^4
  \Longrightarrow m=0\ \lor n=0\ \lor m^2=n^2.
\end{aligned} \tag{X21-g}
\]

Both require genuine global descent: `(m,n,c)=(3,1,0)` and `(1,1,4)`
are primitive visible solutions, so a local-solubility contradiction
cannot prove (X21-g).  Assuming exactly those two classifications, the
compiled argument gives

\[
V\in\{0,9,-7,-3,21\}
\]

and then enumerates

\[
\begin{aligned}
(V,W)\in\{&(0,0),(9,0),(-7,0),\\
          &(-3,\pm12),(21,\pm84)\}.
\end{aligned}
\]

Together with infinity these are eight rational points.  In the original
coordinates the seven affine points are

\[
\left(-\frac14,\frac18\right),(2,-1),(-2,1),
(-1,2),(-1,-1),(5,8),(5,-13).
\]

The independent modular reconnaissance also records the denominator-free
equation obtained by equating the classical `X₀(3)` and `X₀(7)`
Hauptmodul formulas, plus four visible pairs and their `j`-values.  It does
not yet prove that an exact order-twenty-one point maps to a noncuspidal
point of (X21-a).  Thus the two honest remaining parts of this branch are
the infinite descents (X21-g) and a checked modular/Tate birational bridge;
neither is hidden as an assumption.

Order sixteen is now excluded completely.  Suppose `R` has exact order
sixteen and put

\[
P=2R,\qquad Q=4R,\qquad T=8R.
\]

Then `P,Q,T` have orders eight, four, and two.  Translate the abscissa of
`T` to zero and complete the square.  The explicit variable change induces
an additive equivalence of point groups and gives the normalized model

\[
E_{a,b}:Y^2=X^3+aX^2+bX,\qquad T=(0,0). \tag{22}
\]

For a non-two-torsion point `S=(x,y)` on (22), direct simplification of
the tangent formula gives the denominator-free identity

\[
x(2S)(2y)^2=(x^2-b)^2. \tag{23}
\]

Apply (23) successively to `R`, `P`, and `Q`.  Exact orders show that all
three abscissas are nonzero, the ordinates of `R` and `P` are nonzero, and
`x(P)\ne x(Q)`.  The last step has `x(T)=0`, hence
`b=x(Q)^2`.  Moreover,

\[
\left(\frac{x(R)^2-b}{2y(R)}\right)^2=x(P),\qquad
\left(\frac{x(P)^2-b}{2y(P)}\right)^2=x(Q).
\]

Choose `f,g` with `f²=x(P)` and `g²=x(Q)`, so `b=g⁴`, and scale

\[
n=\frac fg,\quad s=\frac{y(Q)}{g^3},\quad
\xi=\frac{x(R)}{g^2},\quad
t=\frac{y(P)}{g^3},\quad \eta=\frac{y(R)}{g^3}.
\]

The curve equations and (23) become

\[
\begin{aligned}
t^2&=n^6+(s^2-2)n^4+n^2,&
4t^2&=(n^4-1)^2,\\
\eta^2&=\xi^3+(s^2-2)\xi^2+\xi,&
4n^2\eta^2&=(\xi^2-1)^2.
\end{aligned} \tag{24}
\]

The first row yields

\[
4s^2n^4=(n^2-1)^4.
\]

Eliminating `s²` from the second row gives the square identity

\[
\bigl(n(\xi^2+1)-2n^3\xi\bigr)^2
=\bigl(\xi(n^4-1)\bigr)^2. \tag{25}
\]

Splitting the equality of squares in (25), and solving the resulting
linear equation, gives `N=n` or `N=-n` and a rational `V` satisfying

\[
V^2=(N^2-1)(N^2+1)(N^2+2N-1),\qquad
N\ne0,\quad N^2\ne1. \tag{26}
\]

It remains to show that the nondegenerate part of (26) is empty.  Write
`N=m/n` in lowest terms.  Clearing denominators says that

\[
(m^2-n^2)(m^2+n^2)(m^2+2mn-n^2)
\]

is a square.  Both `m,n` are nonzero and `m²-n²≠0`.

If `m,n` have opposite parity, the three displayed factors are pairwise
coprime.  Unique factorization makes

\[
m^2-n^2=\pm a^2,\qquad m^2+n^2=b^2.
\]

Consequently

\[
b^4-a^4=(2mn)^2,
\]

contradicting the already-compiled nondegenerate
quartic-difference theorem.

If `m,n` are both odd, write

\[
m=r+s,\qquad n=r-s.
\]

Then `r,s` are coprime and have opposite parity.  Removing the exact
factor `16` from the cleared square gives

\[
rs(r^2+s^2)(r^2+2rs-s^2)=w^2.
\]

The four factors have the required pairwise coprimality.  Thus
`r=±a²`, `s=±b²`, and `r²+s²=c²`, so

\[
a^4+b^4=c^2,
\]

contradicting Fermat's exponent-four theorem `not_fermat_42`.  The both-even
case contradicts coprimality.  This proves
`no_rational_point_of_order_sixteen`; unlike the neighboring genus-one and
genus-two branches, level sixteen has no remaining classification input.

The order-eighteen branch has also reached its standard genus-two boundary.
If `Q` has exact order eighteen, then `2Q` has exact order nine and `9Q`
has exact order two.  Normalize `2Q` to the marked point on Tate normal
form.  The two order conditions hold on this one curve:

\[
\begin{aligned}
0={}&c^5+c^4+(1-b)c^3-3bc^2+3b^2c-b^3,\\
0={}&4r^3+\bigl((1-c)^2-4b\bigr)r^2
        +2b(c-1)r+b^2
\end{aligned} \tag{27}
\]

for a rational abscissa `r` of the two-torsion point.  The first polynomial
has the more revealing form

\[
c^5-(b-c)c^3-(b-c)^3=0.
\]

Since exact order proves `c≠0` and `b-c≠0`, set

\[
d=\frac{c^2}{b-c}.
\]

Clearing only this nonzero denominator in the last equation gives

\[
c=d^2(d-1),\qquad
b=c(d^2-d+1),\qquad d\ne0,1. \tag{28}
\]

The constant term `b²` in the second equation of (27) also gives `r≠0`.
Define

\[
s=\frac{(1-c)r-b}{2rc}.
\]

Substitution of (28) into the two-division cubic, followed by one ring
normalization, gives

\[
(2s+1)\bigl(d^2(d-1)s^2-(d^2-d+1)\bigr)-s^2=0. \tag{29}
\]

The last denominator needed below cannot vanish.  Indeed, if `1+ds=0`,
then `s=-1/d`, and the left side of (29) becomes

\[
-\frac{(d-1)^4}{d^2},
\]

contradicting `d≠0,1`.  Now put

\[
X=\frac{d-s+2ds}{1+ds},\qquad
Y=2Xd-(X^3-2X^2+3X-1).
\]

The exact certificate identity is

\[
\begin{aligned}
Y^2-\bigl(X^6-4X^5+10X^4-10X^3
  +5X^2-2X+1\bigr)
={}&
\frac{4(d-1)^2(2ds+d-s)}{(1+ds)^4}\\
&\cdot\bigl((2s+1)
 (d^2(d-1)s^2-(d^2-d+1))-s^2\bigr).
\end{aligned} \tag{30}
\]

Equation (29) therefore puts `(X,Y)` on

\[
C_{18}:Y^2=X^6-4X^5+10X^4-10X^3+5X^2-2X+1. \tag{31}
\]

The degenerate abscissas are excluded algebraically: `X=0` forces the
left side of (29), after solving for `s`, to be a nonzero multiple of
`(d-1)^5`; `X=1` forces `s=-1` and then gives
`-d(d-1)^2=0`.  Thus the compiled theorem
`exists_orderEighteen_genusTwo_certificate` reaches a nondegenerate
rational point of (31), while retaining (27)--(29), every denominator,
and the original twelfth-power discriminant identity.

Under `X↦-X`, (31) is the usual `X₁(18)` model

\[
Y^2=X^6+4X^5+10X^4+10X^3+5X^2+2X+1.
\]

The remaining assertion that all of its rational points are cuspidal is a
genuine genus-two Jacobian calculation (rank zero plus torsion and
Mordell--Weil saturation), not something supplied by the Tate algebra.
It remains an explicit, honest boundary.

Two additional pieces of that boundary are now kernel-checked.  Modulo
five, the polynomial in (31) is

\[
X^6+X^5+3X+1.
\]

Its derivative is `X⁵+3`, and an explicit Bézout identity proves that the
two polynomials are coprime.  Thus the sextic is separable.  Direct
enumeration gives the four affine solutions

\[
(0,\pm1),\qquad(1,\pm1),
\]

and the monic even-degree infinity chart contributes two smooth normalized
directions.  This is an exact six-element finite-field certificate, not yet
an injection theorem for rational points on a projective genus-two curve.

Over `ℚ`, (31) admits the order-three symmetry

\[
\sigma(X,Y)=
\left(\frac1{1-X},-\frac{Y}{(1-X)^3}\right).
\]

On the noncuspidal domain `X≠0,1`, the third iterate is the identity.  The
checked invariants

\[
u=\frac{X^3-3X+1}{X(X-1)},\qquad
v=\frac{Y}{X(X-1)}
\]

satisfy

\[
v^2=u^2-4u+12. \tag{32}
\]

Moreover `u` is the sum of the three abscissas in a `σ`-orbit and their
product is `-1`.  These formulas expose the cyclic cubic cover of the conic
(32) on which the classical Eisenstein-integer descent operates.  They do
not by themselves construct the Jacobian quotient or prove rank zero, so
the order-eighteen exclusion remains open at exactly that arithmetic step.

The elementary quotient descent is now more explicit.  The exceptional
fiber `u=1` would require a rational root of

\[
z^3-z^2-2z+1,
\]

but monicity makes such a root integral and reduction modulo two rules it
out.  Every remaining conic point is parameterized by

\[
u=\frac{t^2-6t-3}{t^2-1},\qquad
v=-\frac{3t^2+2t+3}{t^2-1}.
\]

The three abscissas in the order-three orbit form the cyclic cubic

\[
z^3-uz^2+(u-3)z+1=0, \tag{33}
\]

whose discriminant is `(u²-3u+9)²`.  Take the canonical reduced fraction
`t=m/n`, with `m,n` coprime and `n>0`.  Clearing `n²` in (33) gives a
primitive homogeneous cubic whose discriminant factors as

\[
(m^2+3n^2)^2(7m^2+6mn+3n^2)^2. \tag{34}
\]

In the Eisenstein coordinate ring `ℤ[ω]`, `ω²+ω+1=0`, these factors are

\[
\begin{aligned}
m^2+3n^2&=N((m+n)+2n\omega),\\
7m^2+6mn+3n^2&=N((3m+n)+(m-n)\omega).
\end{aligned}
\]

Writing `π=3+ω`, the checked identities give `N(π)=7`,
`7=π\bar π`, and

\[
\pi\mid(a+b\omega)\quad\Longleftrightarrow\quad 7\mid 2a+b.
\]

They imply that the two norm factors in (34) cannot both be divisible by
seven when `m,n` are coprime.  This produces the complete primitive/local
descent package attached to a noncuspidal rational point.

The remaining classical step is global, not another clearing-denominators
argument: construct the induced `ℤ[ω]` action on `J₁(18)`, prove
surjectivity by `π` on its rational Mordell--Weil group, determine the
rational Jacobian torsion (classically cyclic of order twenty-one), and
show that the Abel--Jacobi image of the curve meets it only in cusps.  The
present formalization stops before each of those assertions.

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

F. Patrick Rabarison,
[“Structure de torsion des courbes elliptiques sur les corps quadratiques”](https://doi.org/10.4064/aa144-1-3),
*Acta Arithmetica* **144** (2010), 17--52, gives the plane
Tate-parameter equation, the transformation (17), and the six rational
points of `X₁(14)` in §4.2.  The present proof plan replaces its
computer-table rank assertion by the explicit two-isogeny descent
(19)--(21).

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
