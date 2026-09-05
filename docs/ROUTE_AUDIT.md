# Route audit: degree-one formal immersion at five

Date: 2026-08-15
Ledger route: `formal-immersion-at-five-v1`
Execution revision: `canonical-foundations-v4`

This page is explanatory, not a second roadmap. The canonical machine-readable
decision and reviewed-source record are `route_revision` and
`execution.proof_route` in
[`coordination/program.json`](../coordination/program.json).

## Decision

Retain Mazur's 1978 degree-one formal-immersion proof for prime torsion, at
auxiliary prime `5`. Construct the required witness internally from a
nontrivial optimal Eisenstein quotient.

The route itself did not change in this audit. The architecture did:

- the checked theorem
  `MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_formalImmersionAtFive`
  is already a route-neutral argument boundary: it consumes the actual map,
  sections, formal immersion, specialization, and quotient collision directly;
- `MazurTorsion.PrimeOrder.DegreeOneFormalImmersionWitness` is a proposed
  packaging layer, not a checked declaration;
- Jacobian, Hecke, Eisenstein, and finite-Mordell–Weil machinery are intended to
  construct that proposed witness privately;
- constructing the Eisenstein quotient no longer depends on the downstream
  Néron-specialization node; the prime collision retains direct dependencies on
  both inputs;
- the public project endpoint is the full fifteen-group classification;
- the immutable `ncard ≤ 16` challenge is recorded separately;
- canonical coherent-cohomology actions, finite-free proper-curve low-degree
  targets, coherent finite strict-support models with finite global sections,
  and open-local support-comodel assembly, one Weierstrass secant chart, and
  the represented polynomial-cusp collision are recorded as checked
  prerequisites without promoting them to Riemann--Roch, a group scheme, or
  represented `X₀`; and
- conditional finite-level experiments are paused while canonical foundations
  are built.

This is the smallest credible uniform route found that aligns with both the
checked reduction argument and the repository's exact-pin API. That is an
audited engineering judgment, not a proof that no smaller formalization route
exists.

## Checked argument boundary and proposed package

The checked prime-order theorem currently requires the following route-neutral
data directly:

1. schemes `X` and `Y` and a morphism `f : X ⟶ Y`;
2. two sections of `X` over the completed integer ring at `5`, representing
   the modular point and cusp in the intended application;
3. formal immersion of `f` at the cusp section's closed-fibre point;
4. distinctness of the two sections;
5. an implication from failure of the `j`-valuation bound to equality of their
   closed-fibre points; and
6. an implication from the same failure to equality of the two whole sections
   after composition with `f`.

The roadmap proposes packaging those inputs as
`MazurTorsion.PrimeOrder.DegreeOneFormalImmersionWitness`. The record does not
yet exist in checked source, so documentation and the site must not present it
as the current theorem boundary.

Mazur's Corollary 4.3 uses torsion of the image of the point under
consideration, but the checked generic theorem does not take that torsion fact
as an argument. Torsion and Néron specialization are private means of deriving
the whole-section equality in item 6. They do not require the public collision
statement to know all of `A(ℚ)` or to identify it with a cuspidal subgroup.
Global finiteness of `A(ℚ)` is a sufficient private source of the relevant
torsion fact.

Its proposed private constructor is recorded as
`ModularCurve.EisensteinQuotient.toDegreeOneFormalImmersionWitness`. It must
construct, rather than assume, the modular Jacobian, optimal quotient,
nontriviality, and the specialized finite-Mordell–Weil input, then use the
torsion-specialization data to derive the checked theorem's quotient equality.

## Primary and modern sources

- [Mazur 1978, Proposition 3.1 and Corollaries 4.3–4.4](https://www.math.columbia.edu/~goldfeld/Mazur-Goldfeld1978.pdf)
  is the controlling degree-one formal-immersion and collision argument.
- [Mazur 1977](https://www.numdam.org/item/10.1007/BF02684339.pdf)
  supplies the Eisenstein-quotient and finite-Mordell–Weil construction used
  privately.
- [Merel 2024, “Mazur's work with the Eisenstein ideal”](https://celebratio.org/Mazur_BC/article/1148/)
  isolates the theorem-level need, for prime `N = 11` or `N > 13`, as a
  nonzero quotient of `J₀(N)` with finite rational points; it does not require
  a public classification of every rational point on that quotient.
- [Siksek, *Explicit Arithmetic of Modular Curves*, Chapter 7](https://samirsiksek.github.io/siksek.github.io/teaching/modcurves/lecturenotes.pdf)
  presents the residue-disc uniqueness pattern as formal immersion plus a
  rank-zero quotient.
- [Cambridge 2020 Eisenstein-ideal study group](https://www.dpmms.cam.ac.uk/~jcsl5/mazur/mazur.html)
  confirms the same division into integral modular curves, Néron models,
  admissible group schemes, rank zero, and the quotient.
- The [MIT Fall 2023 STAGE seminar](https://math.mit.edu/nt/old/stage_f23.html)
  and Snowden's 2013 Math 679 lectures
  [11](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L11.html),
  [18](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L18.html),
  [20](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L20.html),
  and
  [21](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L21.html)
  corroborate the integral `X₀`/Jacobian/Néron/finite-flat/Eisenstein order of
  construction; they do not remove those represented-object foundations.
- [Darmon's account in *Arithmetic Geometry*, pages 38--39](https://www.claymath.org/wp-content/uploads/2022/03/cmip08c.pdf)
  explains that the winding quotient replaces the delicate Eisenstein descent,
  while its finiteness input comes through relative homology, Heegner points,
  Gross--Zagier, Kolyvagin, and analytic nonvanishing.
- [Balakrishnan--Mazur 2024](https://arxiv.org/html/2307.04752) confirms the
  optimal-quotient/formal-immersion architecture. Its Chabauty variants are
  bounded-level computations, not a uniform replacement for the prime-level
  argument.

## Prime-order proof spine

Let `P ∈ E(ℚ)` have prime order `N`, with `N = 11` or `N ≥ 17`.

1. The exact-order point generates a finite-flat constant cyclic subgroup.
   The represented `Γ₀(N)` moduli problem sends this honest subgroup scheme to
   a noncuspidal rational point `x ∈ X₀(N)(ℚ)`.

2. Construct the degree-one witness from the nontrivial optimal Eisenstein
   quotient. The public argument sees only its normalized map, formal
   immersion, and torsion-image property.

3. If `E` has potentially multiplicative reduction at `5`, the integral
   modular point specializes to a cusp. At prime level the two rational cusps
   are exchanged by Atkin–Lehner, so normalize the collision to `∞`.

4. The quotient image is torsion. Over `ℚ₅`, the ramification index is
   `1 < 5 - 1`; torsion specialization forces an image reducing to zero to be
   zero.

5. The modular section and the cusp meet in the special fibre and have equal
   quotient image. Formal immersion forbids this collision unless the generic
   points agree, contradicting noncuspidality. Hence `j(E)` is `5`-integral.

   The local polynomial-chart construction now provides genuine `sectionAt`
   sections and proves their closed-point collision with the zero section. The
   checked `valuation_j_le_one_of_polynomialCuspSectionAtFive` theorem consumes
   exactly that local geometry. It does not identify either section with a
   represented modular point or cusp, and it retains the specialization and
   equal-quotient-image hypotheses.

6. Integral `j` rules out potentially multiplicative reduction. The checked
   marked weighted-depth argument rules out additive reduction on Mathlib's
   selected minimal equation. Thus `E` has good reduction at `5`.

7. Because `N` is prime to `5`, the marked point keeps exact order after good
   reduction. The checked exhaustive calculation gives `#E(𝔽₅) ≤ 10`,
   contradicting `N ≥ 11`.

Level `13` remains a separate finite endpoint. The same collision mechanism
may be reused at `11` for order `35`. The explicit characteristic-eleven
infinity-chart quotient is now checked to be formally immersive at its selected
cusp; the still-open step is its comparison with the represented modular
special fibre and quotient. This composite-level specialization is not part of
the uniform prime theorem.

## Private constructor: irreducible inputs

The witness constructor still needs substantial honest mathematics:

- the represented compactified `X₀(N)` and an identification of its smooth
  infinity neighbourhood at `5` with the checked polynomial cusp chart;
- the modular Jacobian and cusp-based Abel–Jacobi morphism;
- the Hecke action and the q-expansion principle needed for one nonzero
  cotangent eigenvector;
- a nontrivial optimal Eisenstein quotient;
- finite generation and the narrowly specialized Eisenstein-primary descent
  proving that quotient's rational points finite;
- the precise finite-flat/fppf and Néron specialization results used by that
  descent and the collision.

At degree one, formal immersion needs a single nonzero normalized
eigen-cotangent vector. If its first coefficient vanished, the Hecke recursion
would force every q-coefficient to vanish, contradicting the q-expansion
principle. General symmetric-power Hecke independence is therefore outside the
route.

## Alternatives considered

### Winding quotient

Rejected for the critical path. Merel's winding quotient is naturally
described using modular homology and the winding element. Its finite
Mordell–Weil theorem passes through modular `L`-values, analytic nonvanishing,
and Gross–Zagier/Kolyvagin results. It replaces a delicate Eisenstein descent,
but does not replace its deep arithmetic with a smaller checked foundation.
That is valuable mathematics but a larger currently credible Lean dependency
cone than the specialized Eisenstein construction.

See [Merel 1996](https://perso.imj-prg.fr/wp-content/uploads/merel-pub/torsion.pdf)
and [Darmon, pages 38--39](https://www.claymath.org/wp-content/uploads/2022/03/cmip08c.pdf).

### Modular symbols and Kamienny's criterion

Rejected for degree one. Direct modular-symbol formulations either reconstruct
the winding route or add independence of `T₁e, …, T_de`, which matters for
symmetric powers and degree `d > 1`. Mazur's degree-one argument only needs the
first q-coefficient. See [Kamienny 1992](https://eudml.org/doc/144019).

### Explicit models and Chabauty

Retained only for bounded exceptional endpoints. A separate rational-point
classification for unboundedly many `X₁(N)` does not give a uniform proof of
the prime theorem. The revised
[Balakrishnan--Mazur survey](https://arxiv.org/html/2307.04752) supports this
bounded-level use.

### Elliptic-matroid realization spaces

[Baker 2026](https://arxiv.org/abs/2608.05299) gives a concrete realization-space
model for the irreducible open `X₁(n)°` over `ℤ[1/n]`. It is useful secondary
geometry, but not a shortcut for this route: the open excludes the rational
cusps needed by the collision, the construction takes compactified
generalized-elliptic moduli as known, and its nonrepresentability statement is
equivalent to the prime-torsion theorem rather than an independent proof of it.

### The broader global representation route

Rejected. Global semistability, division fields over cyclotomic fields,
unramified-character arguments, isogeny iteration, and Shafarevich finiteness
form a strictly larger cone after the quotient exists. Existing checked
lemmas from that history may remain useful, but they are not dependencies of
the selected theorem route.

## Explicit non-goals of the critical path

Do not add the following merely because they occur in stronger or more general
theorems:

- the exact order of the cusp-difference class;
- equality of the quotient's rational points with a cuspidal subgroup;
- the complete rational torsion subgroup of `J₀(N)`;
- full local principality, Gorenstein, or `I/I²` calculations beyond the
  fragments consumed by the witness constructor;
- a general Hasse–Weil bound;
- a general Kodaira or component-group classification for the source curve;
- full Oort–Tate classification when the specialized two-factor statement is
  enough;
- residue-characteristic-dividing-level or arbitrary squarefree-level formal
  immersion;
- winding quotients, analytic `L`-functions, or symmetric-power Hecke
  independence.

## Finite endpoints

The point-order reduction also needs:

- order `13`: the explicit `X₁(13)` endpoint;
- order `18`: the explicit `X₁(18)` endpoint;
- order `25`: the Tate-normal-form endpoint;
- order `35`: a squarefree formal-immersion instance at `11` with the explicit
  rank-zero elliptic quotient, whose explicit affine cusp calculation is
  checked but whose represented modular comparison remains open;
- order `49`: a direct represented `X₀(49)` rational-point classification.

These contracts are mathematically required, but only order `49` remains an
active vertical slice during the current foundation phase. The others are
paused, not deleted.

## Revision policy

The route changes only if a replacement has a strictly smaller audited theorem
cone and a credible Lean foundation at the project's exact pins. A proposed
shortcut must list its missing represented objects, arithmetic theorems,
specialization results, and named downstream consumer. Replacing a canonical
object by a conditional record does not count as a smaller cone.

The canonical machine-readable decision, execution lanes, and paused set live
in [`coordination/program.json`](../coordination/program.json).
