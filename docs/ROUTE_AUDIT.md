# Route audit: degree-one formal immersion at five

Date: 2026-08-14
Ledger route: `formal-immersion-at-five-v1`
Execution revision: `canonical-formal-immersion-v3`

## Decision

Retain Mazur's 1978 degree-one formal-immersion proof for prime torsion, at
auxiliary prime `5`. Construct the required witness internally from a
nontrivial optimal Eisenstein quotient.

The route itself did not change in this audit. The architecture did:

- the public collision theorem consumes a route-neutral witness;
- Jacobian, Hecke, Eisenstein, and finite-Mordell–Weil machinery construct that
  witness privately;
- the public project endpoint is the full fifteen-group classification;
- the immutable `ncard ≤ 16` challenge is recorded separately;
- conditional finite-level experiments are paused while canonical foundations
  are built.

This is the smallest rigorous uniform route found in the original papers or
in recent expository accounts.

## The public boundary

The prime-order consumer should require only a package of the following data:

1. a represented integral modular point `x` and the cusp `∞`;
2. a cusp-normalized map `f : X₀(N) → A` to an abelian/Néron target;
3. formal immersion of `f` at `∞` in residue characteristic `5`;
4. torsion of the particular point `f(x)`;
5. compatible specialization of the two sections and their images.

The roadmap names this proposed package
`MazurTorsion.PrimeOrder.DegreeOneFormalImmersionWitness`.

Mazur's Corollary 4.3 needs the image of the point under consideration to be
torsion. It does not require the collision theorem's public statement to know
all of `A(ℚ)` or to identify it with a cuspidal subgroup. Global finiteness of
`A(ℚ)` is a sufficient private construction of the required torsion fact.

The private constructor is recorded as
`ModularCurve.EisensteinQuotient.toDegreeOneFormalImmersionWitness`. It must
construct, rather than assume, the modular Jacobian, optimal quotient,
nontriviality, and the specialized finite-Mordell–Weil input.

## Primary and modern sources

- [Mazur 1978, Proposition 3.1 and Corollaries 4.3–4.4](https://www.math.columbia.edu/~goldfeld/Mazur-Goldfeld1978.pdf)
  is the controlling degree-one formal-immersion and collision argument.
- [Mazur 1977](https://www.numdam.org/item/10.1007/BF02684339.pdf)
  supplies the Eisenstein-quotient and finite-Mordell–Weil construction used
  privately.
- [Merel 2024, “Mazur's work with the Eisenstein ideal”](https://celebratio.org/Mazur_BC/article/1148/)
  gives a concise modern decomposition: for prime `N = 11` or `N > 13`, the
  deep input is a nonzero quotient of `J₀(N)` with finite rational points.
- [Siksek, *Explicit Arithmetic of Modular Curves*, Chapter 7](https://samirsiksek.github.io/siksek.github.io/teaching/modcurves/lecturenotes.pdf)
  presents the residue-disc uniqueness pattern as formal immersion plus a
  rank-zero quotient.
- [Cambridge 2020 Eisenstein-ideal study group](https://www.dpmms.cam.ac.uk/~jcsl5/mazur/mazur.html)
  confirms the same division into integral modular curves, Néron models,
  admissible group schemes, rank zero, and the quotient.

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

6. Integral `j` rules out potentially multiplicative reduction. The checked
   marked weighted-depth argument rules out additive reduction on Mathlib's
   selected minimal equation. Thus `E` has good reduction at `5`.

7. Because `N` is prime to `5`, the marked point keeps exact order after good
   reduction. The checked exhaustive calculation gives `#E(𝔽₅) ≤ 10`,
   contradicting `N ≥ 11`.

Level `13` remains a separate finite endpoint. The same collision mechanism
may be reused at `11` for order `35`, but that composite-level specialization
is not part of the uniform prime theorem.

## Private constructor: irreducible inputs

The witness constructor still needs substantial honest mathematics:

- the represented compactified `X₀(N)` and its smooth cusp chart at `5`;
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
and Gross–Zagier/Kolyvagin-style results. That is valuable mathematics but a
larger formal dependency cone than the specialized Eisenstein construction.

See [Merel 1996](https://perso.imj-prg.fr/wp-content/uploads/merel-pub/torsion.pdf).

### Modular symbols and Kamienny's criterion

Rejected for degree one. Direct modular-symbol formulations either reconstruct
the winding route or add independence of `T₁e, …, T_de`, which matters for
symmetric powers and degree `d > 1`. Mazur's degree-one argument only needs the
first q-coefficient. See [Kamienny 1992](https://eudml.org/doc/144019).

### Explicit models and Chabauty

Retained only for bounded exceptional endpoints. A separate rational-point
classification for unboundedly many `X₁(N)` does not give a uniform proof of
the prime theorem.

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
  rank-zero elliptic quotient;
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
