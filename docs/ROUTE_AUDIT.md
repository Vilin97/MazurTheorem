# Prime-order route audit: formal immersion at five

## Decision

The canonical roadmap now uses Mazur's 1978 formal-immersion proof for the
prime-order callback and reuses the same squarefree-level engine for exact
order `35`.  It does **not** use the global
semistability--division-field--Herbrand--Shafarevich chain from Chapter III of
Mazur's 1977 paper.

The prime-level proof is specialized further than Mazur's printed torsion
proof: it uses the single auxiliary prime `5`.  This is the cheapest residue
characteristic for that uniform callback:

* it is away from the exceptional characteristic `2` in the formal-immersion
  theorem;
* it never equals a remaining prime level (`11` or at least `17`), so no
  bad-level formal geometry is needed in the local collision;
* the base field `ℚ₅` is unramified, so `e=1<5-1` in the torsion
  specialization lemma;
* additive fibres are tame, avoiding the characteristic-two and
  characteristic-three wild cases; and
* `#E(𝔽₅) ≤ 10`, already smaller than every prime order under consideration;
  the roadmap checks this by normalizing and enumerating the 25 short models,
  so it need not first formalize the general Hasse theorem.

Level `13` remains an explicit finite endpoint: `X₀(13)` has genus zero, so
its Jacobian has no nontrivial quotient to which Mazur's Proposition 3.1 can
be applied.  The same uniform argument covers order `11` and every prime
order at least `17`, including `17`.

For exact order `35`, use auxiliary prime `11`, not `5` (which divides the
level) or `3` (which is a wild small characteristic).  The level is
squarefree, the quotient `X₀(35)/w₅` is the rank-zero elliptic curve
`y²+y=x³+x²+9x+1`, and `#E(𝔽₁₁)≤18<35`.  Thus the incremental work is one
explicit optimal quotient and its checked rank-zero certificate; the generic
formal-immersion, cusp, and tame Néron APIs are reused. Finiteness of the
checked explicit model now transports to any supplied abelian variety through
a genuine scheme isomorphism. Constructing that isomorphism from the modular
quotient remains part of the route rather than an inferred identification.

This is a route migration, not a progress claim.  All 48 public node IDs, the
1,000-point denominator, every completion flag, and every registered
Challenge are retained.  Obsolete node IDs are immutable ledger addresses;
their revised mathematical roles are recorded in `route_history` fields in
[`coordination/program.json`](../coordination/program.json).  In particular,
the cyclotomic Challenge remains a mandatory release obligation, but is no
longer represented as a logical premise of Mazur's theorem.

## Checked mathematical chain

Fix a rational prime `N` with `N = 11` or `17 ≤ N`, an elliptic curve
`E/ℚ`, and a rational point `P` of exact order `N`.

1. The cyclic subgroup `C = ⟨P⟩` defines a rational point
   `x = (E,C) ∈ X₀(N)(ℚ)`.
2. Let `A` be the nontrivial optimal Eisenstein quotient of `J₀(N)`.  The
   retained Eisenstein rank-zero calculation proves that `A(ℚ)` is finite.
   Hence the image of `x` under the cusp-normalized Abel--Jacobi projection
   `f : X₀(N) → A` has finite order.
3. Suppose `E` has potentially multiplicative reduction at `5`.  The
   integral modular point specializes to a cusp.  An Atkin--Lehner involution
   moves that cusp to `∞`.
4. Mazur's Proposition 3.1 says that the projection to **any** nontrivial
   optimal quotient of the new modular Jacobian is a formal immersion along
   `∞` away from characteristic `2`; in particular it is one in
   characteristic `5`.
5. The quotient point `f(x)` specializes to zero.  The specialization lemma
   for a torsion section over an unramified DVR (`e=1<5-1`) therefore gives
   `f(x)=0`.
6. The sections `x` and `∞` now meet in the special fibre and have the same
   image under `f`, while their generic points differ.  Surjectivity on
   completed local rings—the definition of formal immersion—makes this
   impossible.  Thus `E` has potentially good reduction at `5`.
7. Since `N ≠ 5`, the marked point retains exact order `N` in the Néron
   special fibre.  For the torsion contradiction it is enough to prove the
   marked-point consequence `12 • P ∈ E₀`: `12` annihilates every tame
   elliptic component group of order at most four and is coprime to every
   prime `N ≥ 11`.  Reduction from `E₀` to the five-element additive group,
   followed by the pro-five formal kernel, then kills `P`.  The checked Lean
   consumer uses exactly this component-exponent statement and does not need
   to construct or count the full component quotient. The additive special
   group at `5` (and at `11` for order `35`) is now constructed by checked
   singular-cubic normalization and finite enumeration. Potentially good
   reduction also excludes a multiplicative fibre, so the reduction is good.
8. The point injects into `E(𝔽₅)`, but the checked finite-field certificate
   gives `#E(𝔽₅) ≤ 10`, a contradiction. Mathematically this is the `q=5`
   case of Hasse; in Lean it is cheaper to normalize to short form and
   enumerate 25 coefficient pairs.

Steps 3--6 are Mazur's Corollary 4.3 specialized to `ℚ₅`.  Corollary 4.4
supplies the Eisenstein quotient for `N=11` and prime `N≥17`.  Mazur prints
Step 8 with the auxiliary prime `3`; changing it to `5` is a direct inference
from the preceding all-primes-away-from-two corollary and removes the wild
small-characteristic cases.

## What remains genuinely hard

Formal immersion is not a shortcut around the modular quotient.  The
following remain on the theorem's critical path:

* enough curve Picard/Jacobian theory to construct `J₀(N)` and the
  cusp-based Abel--Jacobi map;
* the integral `X₀(N)` cusp neighbourhood and its `q`-parameter at the
  auxiliary primes `5` and `11`;
* Hecke correspondences, cotangent action, and the `q`-expansion recursion;
* a nontrivial optimal Eisenstein quotient for `N=11` or prime `N≥17`;
* finiteness of that quotient's rational points; and
* the focused Néron and finite-flat theory used in the last assertion,
  including genuine identity-component comparison and the tame
  Tate--Kodaira theorem that the marked class in the quotient by canonical
  nonsingular reduction has finite order at most four at `5` and `11`. The
  checked pointwise interface already converts this exact assertion into the
  uniform exponent `12` used downstream; a full component-cardinality bound
  is only a stronger fallback. The integral-`j` valuation inequality,
  preservation under integral valuation-unit coordinate changes, and the
  obstruction to every arbitrary translation followed by a scale of valuation
  below one are checked first steps. Additive reduction now constructs its
  singular residue point, and the lifted complete short-normal-form change
  produces an integral model whose special fibre is exactly `Y² = X³` and
  whose five coefficients all lie in the maximal ideal at both selected
  primes. Bundled one-factor total-transform quotients at the closed cusp are
  now checked without asserting strict-transform or chart-coverage geometry.
  Their first coefficient-depth branch proves every local point has canonical
  nonsingular reduction; the prime-order and order-35 consumers exclude that
  branch and force `a₆ ∈ 𝔪²` on the same exact model. In the next `a₄/ϖ`
  branch, a checked tangent calculation puts the marked double in canonical
  nonsingular reduction and the same consumers force `a₄ ∈ 𝔪²`. The proof
  splits by ordinate depth: a tangent-slope pole enters the formal kernel, a
  unit slope reduces the double away from the cusp, and the anti-diagonal case
  doubles to zero. The next exact-depth-two `a₆` branch is also pointwise:
  after doubling stays at the cusp, the secant for the triple either has a
  pole and enters the formal kernel or is a unit and reduces away from the
  cusp. Real marked consumers therefore force `a₆ ∈ 𝔪³` at five and eleven.
  A same-model marked exceptional-cubic package now derives its residue root
  equation. The checked tangent split puts the marked double in canonical
  nonsingular reduction whenever that root is simple, so real five- and
  eleven-adic exact-order consumers force the marked derivative to vanish.
  For a repeated nonzero root, the doubled cusp point either already enters
  canonical nonsingular reduction or has exceptional root `-2r`, whose
  derivative is `9r²`; the simple-root theorem applied to `2P` therefore puts
  `4P` and then `12P` in the subgroup. The arithmetic consumers force `r=0`
  and consequently `x ∈ 𝔪²`, `a₄ ∈ 𝔪³`, and `a₆ ∈ 𝔪⁴` on the same model and
  uniformizer, still without a Kodaira or component-incidence claim. The next
  pointwise calculation does not take fourth depth as an independent premise:
  the point equation and `a₆ ∉ 𝔪⁵` force the ordinate to have exact depth two.
  Its tangent keeps the double at the cusp, and the following secant either
  has a pole and enters the formal kernel or has unit slope and reduces the
  triple away from the cusp; the equal-abscissa cases are checked separately.
  Thus `3P`, hence `12P`, lies in canonical nonsingular reduction, and the
  actual five- and eleven-adic consumers force `a₆ ∈ 𝔪⁵` while retaining the
  already checked fourth-depth conclusion on the identical model. The later
  weighted `a₄` branch and the final minimality contradiction are still
  required. The
  canonical reduction predicate, subgroup, and marked multiples now transport
  through the integral unit normalization, so each future normalized-case
  conclusion can be carried back to the original selected equation without a
  new geometric assumption.

The point-group shadow of the cyclic quotient is now checked: quotienting by
the supplied rational cyclic subgroup has the exact kernel, multiplication by
the level descends, both quotient/dual composites are level multiplication,
and these identities are natural under admissible Weierstrass variable
changes. This is not the elliptic quotient scheme `E/C`; representability and
base change remain part of the first modular step above.

The rank-zero input is why the existing finite-flat work is retained, but its
integral scope must be stated precisely. In Mazur 1977 III.3 the
pre-admissible group over `Spec ℤ` is flat, quasi-finite, separated, and of
finite presentation; it becomes finite only after inverting the level. The
two constant-or-multiplicative factors on that open have four possible
integral closures: `ℤ/p`, its bad-level flat extension, `mu_p`, and its
bad-level flat extension. Thus the finite-flat two-factor API is a reusable
subcase, not the theorem itself. The selected proof still uses Raynaud
uniqueness over an unramified DVR, the four elementary fppf-cohomology
calculations, completely toric reduction at the level, and Mordell--Weil
finite generation. The roadmap does not ask for a full Oort--Tate
classification or connected--étale theory unless a named rank-zero consumer
actually needs it.

Here `p` is the coefficient prime of an admissible `p`-group, `N` is the
modular level, and the formal-immersion reduction prime is a third parameter
`ℓ` (`5`, or `11` for level `35`). Mazur assumes `p ≠ N` in the bad-level
calculation. The two page-49 localization sequences have quotient sheaves
supported on the fibre at `N`; those supported terms are not quasi-finite flat
group schemes. They therefore belong in a sheaf-level locally-surjective exact
interface, separately from the quasi-finite quotient presentations used for
actual admissible filtrations.

The formal-immersion proof itself needs less Hecke algebra than the old
roadmap suggested.  In degree one, the cotangent map only has to detect the
first Fourier coefficient.  A nonzero simultaneous Hecke eigenvector in the
cotangent space of the quotient cannot have `a₁=0`, because the standard
Hecke recursions would then kill all of its coefficients and the
`q`-expansion principle would kill the form.  Kamienny's linear independence
of several Hecke operators is a higher-symmetric-power generalization, not a
prerequisite here.

The local algebra bridge is now checked one layer below the modular geometry:
localizing an explicit affine special fibre agrees naturally with quotienting
the ambient local ring by the base-fibre ideal, and degree-one cotangent data
on that fibre feeds the completed ambient map. Canonical affine stalk
equivalences now identify this map with the actual stalk map of `Spec.map`, so
the same data proves formal immersion for a genuine affine-scheme morphism.
A principal localized cusp maximal ideal with generator `q` surviving modulo
its square now supplies the exact degree-one cotangent dimension. A concrete
localized first-order identity with unit `q` coefficient constructs the
detected vector and reaches formal immersion of the genuine `Spec.map`.
Surjectivity of the ambient localized residue-field map now descends through
the compatible special-fibre quotients and is transported across the
localization/quotient equivalences, so the fibre residue map is no longer a
second premise. Moreover, a nonzero simultaneous Hecke eigen-expansion in an
actual completed-local power-series coordinate constructs the detected
cotangent vector without an asserted linear coefficient.
At both selected auxiliary primes, checked consumers identify that affine
point with the same integral cusp specialization used by the collision and
carry the resulting formal immersion through the marked
component-exponent-twelve arithmetic endpoint. What remains is the represented
modular affine presentation and sections, its cusp prime and parameter proofs,
the ambient residue surjection, the quotient collision, and the
optimal-quotient Hecke/q-expansion identity.

The theorem also does **not** consume the exact order of `[0]-[∞]`, an
identification of all of `A(ℚ)` with the cuspidal subgroup, or local
principality of the Eisenstein ideal except insofar as one of those facts is
unavoidably used internally to construct and prove nontriviality of the
chosen quotient.  The stable public interface is only:

```lean
ModularCurve.EisensteinQuotient.nontrivial_of_level_eleven_or_ge_seventeen
ModularCurve.EisensteinQuotient.mordellWeil_finite
ModularCurve.OptimalNewQuotient.formalImmersionAtInfinity_of_residueChar_ne_two
ModularCurve.EisensteinQuotient.formalImmersionAtInfinity_modFive
```

Each declaration must have a compiled consumer in
`primeTorsion_potentiallyGoodReductionAtFive` before its API is accepted.

## Route comparison

| Route | Attractive feature | Formalization cost that decides against it |
|---|---|---|
| Mazur 1978, optimal Eisenstein quotient + degree-one formal immersion | After the quotient is available, the proof is one local collision and a ten-point finite-field bound | Still requires `J₀(N)`, Hecke/q-expansions, and a rank-zero quotient; this is the selected minimum |
| Mazur 1977 / Snowden course route | Closely documented and already reflected in some checked cyclotomic work | Adds global semistability, all-bad-prime component analysis, a division field over `ℚ(ζ_N)`, unramifiedness, Herbrand--Kummer, splitting, an isogeny iteration, and Shafarevich finiteness |
| Merel's winding quotient | Gives the largest quotient with nonvanishing `L(A,1)` and generalizes well to number fields | Adds modular symbols, abelian-variety `L`-functions, analytic nonvanishing, and Kolyvagin--Logachev rank zero; none is present at the project pin, and a larger quotient does not improve the degree-one formal-immersion criterion |
| Kamienny/Merel symmetric-power criterion | Essential for degree greater than one | Requires linear independence of several Hecke operators and symmetric powers; degree one only needs nonvanishing of the first coefficient |
| Calegari--Emerton deformation/R=T reinterpretation | Reproves parts of Eisenstein Hecke algebra structure conceptually | Introduces pseudodeformations, local deformation conditions, Breuil modules, and a precisely matched `R=T` theorem; it does not remove the modular Jacobian or rank-zero quotient |
| Bilu--Parent/Kamienny Hecke-independence presentation | Modern and clean for formal immersions on symmetric powers and Cartan curves | Solves a more general tangent-space problem than the rational degree-one theorem needs |
| Direct explicit `X₁(N)` rational-point classification for all primes | Avoids generic modular Jacobians in each fixed level | Is not uniform in unbounded prime `N` and simply moves the missing theorem into infinitely many high-genus Diophantine classifications |

The winding quotient remains a sensible future optimization only if a pinned
dependency already supplies a theorem of the form
`L(A,1) ≠ 0 → Finite A(ℚ)` with its complete provenance and axiom audit.  It
is not economical to formalize that analytic/Euler-system cone solely to
replace a finite Eisenstein quotient already needed by Mazur's argument.

## Consequences for the public dependency graph

The eight immutable prime-argument IDs now form this chain:

```text
MT-PRIME-SEMISTABLE
  modular point + finite quotient image
    ↓
MT-PRIME-OUTSIDE-IDENTITY
  cusp reduction at 5
    ↓
MT-PRIME-EISENSTEIN-SPECIALIZATION
  formal immersion ⇒ potentially good at 5
    ↓
MT-PRIME-DIVISION-FIELD
  prime-to-5 torsion specialization
    ↓
MT-PRIME-HERBRAND-KUMMER
  additive fibre impossible
    ↓
MT-PRIME-SPLIT-SEQUENCE
  good reduction at 5
    ↓
MT-PRIME-SHAFAREVICH
  #E(𝔽₅) ≤ 10
    ↓
MT-PRIME-ISOGENY-CHAIN
  exclude 11 and every prime ≥17
```

The old names remain visible only as immutable IDs and `route_history` data;
their titles, artifacts, and dependency edges now state the actual work.
Neither the cyclotomic node nor any global Shafarevich theorem is an input to
this chain.

The endpoint audit produced two further reductions:

* `MT-O35-EXCLUDE` consumes the same optimal-quotient formal-immersion theorem
  at `11`.  It constructs `X₀(35)/w₅`, proves that elliptic quotient has
  finite rational points, and finishes with tame specialization and the
  checked 121-model bound `#E(𝔽₁₁)≤18`. It does not classify all rational
  points of the genus-three curve `X₀(35)` or require a general Hasse theorem.
* `MT-O49-TOWER` now sends the cyclic subgroup generated by an exact order-49
  point directly to the already classified `X₀(49)(ℚ)`.  Since the checked
  rank-zero model has only its two cusps, the roadmap no longer asks for
  additivity of the explicit Vélu point function or a nonbacktracking
  isogeny tower.

Order `25` cannot be absorbed: `X₀(25)` has genus zero and hence no
nontrivial Jacobian quotient.  Its explicit `X₁(25)`/Tate-normal-form
endpoint remains necessary.  The same genus-zero obstruction explains why
level `13` and order `18` stay in their explicit lanes.

Order `11` is removed from the genuinely exceptional finite mathematics.
The retained `MT-X11-COSET` Challenge is not deleted or weakened: after the
uniform theorem excludes noncuspidal `X₁(11)(ℚ)` points, the preferred proof
is to establish the reverse explicit moduli bridge, enumerate the five cusp
points, and prove the coset statement with zero quotient representative.  Its
direct five-isogeny Selmer proof remains a fallback and an independent API
check.

That preferred finite-endpoint bridge is now checked conditionally on the
uniform theorem.  `OrderElevenModelInverse` constructs the reverse rational
functions, proves all denominator conditions and the raw round trip, and uses
a Bézout/resultant certificate plus the rational-root theorem to show that the
reconstructed Tate curve has nonzero discriminant and an exact order-eleven
marked point.  `XOneElevenUniformCoset` consumes any uniform order-eleven
exclusion, identifies the four affine cusp points and infinity with the five
visible multiples of `(0,0)`, and proves `FiveCosetBound` with `Q=0`.
Accordingly, no new explicit Selmer premise has been added to the selected
route: the remaining dependency is `MT-X11-JOIN` and the immutable Challenge
bridge.  The node remains open with zero credit until those declarations
compile unconditionally.

## Acceptance and fallback rules

The new route is accepted only after the following downstream chain compiles:

```text
formalImmersionAtInfinity_of_residueChar_ne_two
  → formalImmersionAtInfinity_modFive
  → primeTorsion_potentiallyGoodReductionAtFive
  → goodReductionAtFive
  → rationalPoint_addOrderOf_ne_prime_ge_seventeen
  → rationalTorsion_orders_mem_cyclicOrders
```

No declaration may assume that the modular point is integral, that a
torsion section specializing to zero vanishes, that the quotient is
nontrivial, or that additive component groups are small: each is a separately
checked premise in the graph.

If Proposition 3.1 proves unexpectedly expensive at the pinned APIs, first
retain the same local-at-five theorem and change only the proof of the
cotangent nonvanishing statement.  The preferred fallback order is:

1. a direct completed-local-ring calculation from the `q`-expansion;
2. the equivalent cotangent-space criterion;
3. a specialized formal immersion theorem only for the constructed
   Eisenstein quotient; then
4. the old 1977 representation route, reintroduced only by a new reviewed
   route revision.

Failure of one formal-immersion encoding is not evidence for adopting the
winding quotient or `R=T`; those alternatives change the mathematical
dependency cone rather than merely its Lean interface.

## Primary literature and audited exposition

* Barry Mazur,
  ["Rational isogenies of prime degree"](https://www.math.columbia.edu/~goldfeld/Mazur-Goldfeld1978.pdf),
  *Inventiones Mathematicae* **44** (1978), 129--162.  Proposition 3.1 is
  the formal immersion for any nontrivial optimal new quotient; Corollary
  4.3 is the cusp-collision/potential-good-reduction argument; Corollary 4.4
  supplies the finite Eisenstein quotient in the required levels; Theorem 4.1
  finishes rational torsion by a small finite field.
* Barry Mazur,
  ["Modular curves and the Eisenstein ideal"](https://www.numdam.org/item/PMIHES_1977__47__33_0/),
  *Publications Mathématiques de l'IHÉS* **47** (1977), 33--186.  Chapter
  III.3 contains the finite-Mordell--Weil input retained here; Chapter III.5
  is the larger prime-order route retired from the theorem cone.
* A. P. Ogg,
  ["Rational points of finite order on elliptic curves"](https://eudml.org/doc/142069),
  *Inventiones Mathematicae* **12** (1971), 105--111.  This independently
  excludes order 17, but no separate order-17 endpoint is needed because
  Mazur's Corollary 4.4 and the prime-five argument include it.
* Bryden Cais,
  ["Universal Families and Ruling Out Small Primes"](https://math.stanford.edu/~conrad/vigregroup/vigre03/kubert.pdf)
  (VIGRE Mazur Seminar, 2003), §4.  This gives the genus-three model of
  `X₀(35)`, the degree-two quotient by `w₅`, the elliptic model
  `z²+z=w³+w²+9w+1`, and its rational torsion.  The roadmap reuses the
  quotient but replaces the notes' analytic-rank assertion/fibre enumeration
  with a checked rank-zero proof and the shared local formal-immersion
  criterion.
* Sheldon Kamienny,
  ["Torsion points on elliptic curves and q-coefficients of modular forms"](https://eudml.org/doc/144019),
  *Inventiones Mathematicae* **109** (1992), 221--229.  This is the
  symmetric-power/Hecke-independence generalization, not the source of
  Mazur's degree-one Proposition 3.1.
* Loïc Merel,
  ["Bornes pour la torsion des courbes elliptiques sur les corps de nombres"](https://perso.imj-prg.fr/wp-content/uploads/merel-pub/torsion.pdf),
  *Inventiones Mathematicae* **124** (1996), 437--449.  The introduction
  explicitly replaces the Eisenstein quotient by the winding quotient and
  invokes Kolyvagin--Logachev for finite Mordell--Weil group.
* Yuri Bilu and Pierre Parent,
  ["Serre's uniformity problem in the split Cartan case"](https://annals.math.princeton.edu/wp-content/uploads/annals-v173-n1-p13-p.pdf),
  *Annals of Mathematics* **173** (2011), 569--584.  Its formal-immersion
  appendix is useful API prior art for Hecke cotangents, but its Cartan and
  higher-degree scope is not imported into this roadmap.
* Frank Calegari and Matthew Emerton,
  ["On the ramification of Hecke algebras at Eisenstein primes"](https://math.uchicago.edu/~emerton/pdffiles/ramification.pdf),
  *Inventiones Mathematicae* **160** (2005), 97--144.  This recovers parts
  of Mazur's Eisenstein algebra through deformation theory; it is recorded as
  an alternative, not an assumed shortcut.
* Andrew Snowden,
  ["Course on Mazur's theorem"](https://websites.umich.edu/~asnowden/teaching/2013/679/)
  (2013), especially Lectures 11 and 18--23.  These notes are an excellent
  audit of the 1977 route and the rank-zero criterion.  They are secondary
  exposition and do not override the 1978 primary-source route selection.
