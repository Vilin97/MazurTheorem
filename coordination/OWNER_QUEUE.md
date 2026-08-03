# Integration-owner dependency queue

This is the execution view of the canonical ledger in
`coordination/program.json`. The ledger owns weights, dependencies, contract
metadata, and completion; this file records dependency-critical ordering,
handoff policy, and the next checked acceptance boundaries. It awards no
progress independently.

Snapshot: 2026-08-02, route revision `formal-immersion-at-five-v1`, merged
over owner checkpoint `686bf31`. The ledger still has 48 nodes / 1,000
points: three completed nodes worth 85 points and 45 unfinished nodes. No
weight, public node ID, or Challenge was removed; the reviewed Tau Ceti A1
and exact-pin completions remain credited.

## Route decision

The theorem-critical prime path is Mazur's 1978 degree-one formal-immersion
argument at auxiliary prime `5`, not the former global
semistability--division-field--cyclotomic--Herbrand--splitting--Shafarevich
chain. The same formal-immersion engine is reused at `11` for squarefree level
`35`. The full mathematical and literature audit is in
`docs/ROUTE_AUDIT.md`.

The hard core that remains is substantial: construct the relevant modular
Jacobian, Hecke-stable optimal quotient, finite Mordell--Weil certificate,
cusp formal immersion, and focused Néron/finite-flat consumers. The route
change is valuable because everything after that quotient becomes one local
collision at `5` and a ten-point finite-field bound.

## Checkpointed work to retain and review

| Branch | Retained value | Integration consequence |
|---|---|---|
| `codex/mazur-owner-uw` | Completed exact-pin migration and Tau Ceti A1, integrated finite-flat declarations, and checked explicit X₁(11) five-isogeny composition | Keep A1 and pin migration at full credit. Finite-flat and X₁(11) are partial checked infrastructure and earn no node credit yet. |
| `codex/mt-a2-product-formula` | A2 local-order and proper-curve groundwork built over the permanent A1 API | Re-audit against the Picard/Jacobian consumer, then continue the residue-degree product formula without changing the A1 interface. |
| `codex/mt-ffgs-basic` | Checked finite-flat/Affine substrate, kernel presentation, and the constant-rank point-exponent consumer | Keep the sound declarations. Complete quotient/base-change and constant/`μ_p` examples only through the admissible-filtration/rank-zero consumer. Partial infrastructure earns zero completion credit. |
| `codex/mt-tc-a3-divisor-line-bundle` | Divisor/line-bundle cocycle and descent substrate | Preserve it as the lower Picard/Jacobian path. Review transport, normalization, cocycle, restriction, and a real downstream `DivisorCocycle` consumer before freezing the API. |
| `codex/mt-cyclotomic-unramified-cft` | Checked Kummer--Artin and Hilbert-94 infrastructure plus an honest isolated reciprocity boundary | Keep it as an independent release obligation. It is not a premise of the formal-immersion theorem. |
| `codex/owner-o49-tower` | Checked level-seven correspondence and explicit Vélu work; reusable Tate normalization is isolated at `9dad18d` | Retain as useful library work, but pivot the endpoint to the direct rational cyclic-subgroup map into the already classified two-cusp `X₀(49)`. Do not require Vélu additivity or a nonbacktracking tower. |
| `codex/owner-x11-selmer` | Checked isogeny kernels and an empty-support fifth-power Selmer factor at `be3f2b7` | Freeze as a fallback and release-API check. Further Selmer work is not theorem-critical after the uniform order-eleven theorem. |

The independent Tau Ceti order-support and product-dimension contracts remain
valid. Every worker commit must be reviewed against the revised consumer,
rather than accepted because it extends the superseded route.

## Theorem-critical queue

Work may proceed in parallel across the numbered lanes, but integration
within each lane follows the listed order.

### 1. Shared geometry and cyclic quotients

1. Completed `MT-TC-A1-ORDER-SUPPORT` (15); next
   `MT-TC-A2-PRODUCT-FORMULA` (15) →
   `MT-TC-A3-DIVISOR-LINE-BUNDLE` (18).
2. From A3, build `MT-TC-B1-COHERENT-COHOMOLOGY` (35), then in parallel
   `MT-TC-B2-RR-SERRE` (25) and `MT-TC-C1-RELATIVE-COHOMOLOGY` (30).
3. Build `MT-TC-C2-SYMMETRIC-POWERS` (15) and
   `MT-TC-D1-PICARD-FUNCTOR` (35), then
   `MT-TC-D2-PICARD-REPRESENTABILITY` (45).
4. Close `MT-TC-E0-PRODUCT-DIM` (2), then integrate it with D2 as
   `MT-TC-E1-JACOBIAN-VARIETY` (20).
5. Combine C1 and E1 in `MT-TC-F1-ABEL-JACOBI` (20).
6. In parallel, narrow `MT-EC-ISOGENY-WEIL` (25) to rational cyclic
   subgroups, their quotient/classifying data, duals and multiplication
   kernels actually consumed by `X₀(N)` and reduction. A general Weil-pairing
   theory is not an acceptance target without a named consumer.

### 2. Focused Néron and Eisenstein rank-zero infrastructure

1. `MT-NERON-BASE` (40) consumes E1 and the cyclic-quotient lane. Its public
   API stops at section extension for the modular quotient and elliptic local
   models.
2. `MT-NERON-COMPONENTS` (30) supplies completely toric level reduction and
   the tame additive component bound at `5` and `11`.
3. `MT-NERON-SPECIALIZATION` (30) supplies prime-to-residue injection and the
   full formal-kernel torsion lemma for `e < p-1`. The latter is essential
   because the quotient image can have residue-primary torsion.
4. Independently finish `MT-FFGS-BASIC` (20), then
   `MT-FFGS-CONNECTED-ETALE` (20) as admissible filtrations plus their fppf
   cohomology, then `MT-FFGS-OORT-RAYNAUD` (40) as the unramified Raynaud
   uniqueness and rank-zero criterion. Do not build unconsumed classification
   generality.

### 3. Modular curve, quotient, and formal immersion

1. `MT-X0-MODULI` (30): attach a rational `X₀(N)` point directly to a
   rational cyclic subgroup. This also unlocks the simplified order-49
   endpoint.
2. `MT-X0-INTEGRAL` (30): compactification and cusp neighbourhoods only in
   the generality consumed at auxiliary primes `5` and `11` and at the level
   for toric reduction.
3. `MT-X0-CUSPS` (20): cusp sections, Atkin--Lehner transport, and the exact
   reduction-type bridge.
4. `MT-X0-JACOBIAN` (20) → `MT-X0-HECKE` (30): cusp-normalized Abel--Jacobi,
   Hecke action, cotangent map, and q-expansion recursion.
5. `MT-X0-EISENSTEIN-ALGEBRA` (30): package a nontrivial optimal new quotient
   and prove Mazur 1978 Proposition 3.1 away from characteristic `2`. Degree
   one needs first-coefficient detection, not Kamienny's multi-Hecke linear
   independence.
6. `MT-X0-EISENSTEIN-QUOTIENT` (40): construct the quotient for level `11`
   or prime level at least `17`, prove its rational points finite via the
   focused rank-zero lane, and compile the characteristic-five formal-
   immersion consumer. Exact cusp order is not a public acceptance API.

### 4. Prime-order callback at five

The immutable IDs below are ledger addresses whose revised roles are recorded
in `route_history`:

1. `MT-PRIME-SEMISTABLE` (10): modular point and torsion image in the finite
   quotient.
2. `MT-PRIME-OUTSIDE-IDENTITY` (10): potentially multiplicative reduction
   gives cusp specialization at `5`.
3. `MT-PRIME-EISENSTEIN-SPECIALIZATION` (20): torsion collision plus formal
   immersion proves potentially good reduction at `5`.
4. `MT-PRIME-DIVISION-FIELD` (15): preserve the exact prime-to-five order of
   the marked point in the Néron fibre.
5. `MT-PRIME-HERBRAND-KUMMER` (10): exclude tame additive reduction using the
   formal kernel, additive quotient, and component group.
6. `MT-PRIME-SPLIT-SEQUENCE` (10): conclude good reduction at `5`.
7. `MT-PRIME-SHAFAREVICH` (15): prove `#E(𝔽₅) ≤ 10`; a checked enumeration of
   the 25 short models is an acceptable and potentially cheaper consumer than
   a general Hasse theorem.
8. `MT-PRIME-ISOGENY-CHAIN` (10): exclude exact order `11` and every prime
   order at least `17`.

### 5. Finite endpoints

The independent explicit lanes `MT-X13-NONCUSP` (26),
`MT-X18-NONCUSP` (18), and `MT-O25-EXCLUDE` (16) remain unchanged: their
genus-zero `X₀` quotients do not support the selected argument.

- `MT-X11-JOIN` (2) consumes the uniform prime theorem. Afterwards,
  `MT-X11-COSET` (12) proves its immutable Challenge preferably by the reverse
  `X₁(11)` moduli bridge and the five visible cusps; the prepared five-isogeny
  Selmer calculation remains a fallback. The Challenge is a release
  obligation, not a prerequisite of the point-order theorem.
- `MT-O35-EXCLUDE` (14) constructs the explicit optimal elliptic quotient
  `X₀(35)/w₅ : y²+y=x³+x²+9x+1`, proves finite rational points, and reuses the
  squarefree-level formal immersion at auxiliary prime `11`; the local bound
  is `#E(𝔽₁₁) ≤ 18 < 35`.
- `MT-O49-TOWER` (10) maps the subgroup generated by a point of exact order
  `49` directly to the checked `X₀(49)(ℚ)` classification and rules out both
  cusps.
- `MT-FINITE-JOIN` (2) assembles level `13` and the four composite callbacks;
  order `11` is already uniform.

### 6. Integration

1. Completed `MT-PIN-MIGRATION` (20): clean exact-pin builds, lifecycle and
   provenance are permanently checked.
2. `MT-API-INTEGRATION` (10): compile
   `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders` from finite and prime
   callbacks.
3. `MT-FINAL-ASSEMBLY` (15): compile
   `MazurTorsion.torsion_ncard_le_of_arithmetic_inputs` and the LeanPool
   theorem.
4. `MT-EXPOSITION-AUDIT` (5): after final assembly and both independent
   release obligations below, run axiom, source, license, prior-art, graph,
   clean-checkout, quality, and authorized full-build audits.

## Noncritical but mandatory release obligations

- `MT-CYCLOTOMIC-UNRAMIFIED` (20): solve the immutable locally-primary
  pseudo-unit Kummer reciprocity Challenge and compile its Kummer--Artin
  consumer. It no longer unlocks a prime-theorem node.
- `MT-X11-COSET` (12): solve the immutable five-coset Challenge after the
  uniform order-eleven theorem is available.

The final audit depends on both, so this separation cannot be used as a scope
or accounting shortcut.

## Checkpoint acceptance rules

- Preserve immutable Challenge statements, public node IDs, weights, and
  completion flags. Any further route migration needs a new audited revision.
- A compiled conditional interface is partial infrastructure, never evidence
  that its hypotheses have been proved.
- Require a compiled downstream consumer before accepting a public API.
- Build the smallest touched Lean targets with `LEAN_NUM_THREADS=1`, then run
  `python3 scripts/quality.py` and the Challenge immutability check.
- Record proved declarations, focused verification, remaining critical-path
  gaps, and active workers in every pushed integration checkpoint.
