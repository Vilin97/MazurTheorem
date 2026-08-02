# Integration-owner dependency queue

This is the live execution queue for the permanent integration branch. The canonical weights,
immutable dependency edges, and contract metadata remain in `coordination/program.json`; this file
records dependency-critical ordering, current ownership, and the next checked acceptance boundary.
It must be updated at integration checkpoints and never used to award progress independently of
the canonical ledger.

Snapshot: 2026-08-02. The ledger has 48 nodes / 1,000 points: three completed nodes (85 points) and
45 unfinished nodes (915 points). Open Challenge contracts
are temporary compiled handoffs and receive no completion credit.

## Active lanes

| Lane | Owner branch/worktree | Immediate acceptance boundary |
|---|---|---|
| `MT-TC-A2-PRODUCT-FORMULA` | `codex/mt-a2-product-formula`, separate Tau Ceti worktree | Prove the residue-degree-weighted product formula using the permanent A1 `orderSystem` and compile the immutable `degreeZero` consumer. |
| `MT-FFGS-BASIC` | `codex/mazur-owner-uw`, integrated checkpoint | Extend the checked point-representing kernels, constant/diagonalizable examples, `μ_n` multiplication kernel, and constant-group quotient to a generic finite-flat closed-subgroup quotient; prove kernel/quotient base-change compatibility and compile a connected–étale consumer. The node remains incomplete and earns zero credit. |
| `MT-O49-TOWER` | `codex/owner-o49-tower`, separate worktree | Derive the exact order-49 bridge from the checked X₀(49) correspondence endpoint and compile the point-order consumer. |
| Integration and finite-endpoint triage | `codex/mazur-owner-uw`, this worktree | Review workers, preserve API coherence, and advance the next independent finite or foundational lane. |

## Open Challenge registry

Every registered open contract is listed here. A row leaves this table only after its permanent
destination and named downstream consumer compile and the Challenge file becomes a checked bridge.

| Node | Contract file | State | Current route |
|---|---|---|---|
| `MT-X11-COSET` | `Challenge/XOneElevenCoset.lean` | open | Complete the one remaining five-isogeny Selmer/coset computation. |
| `MT-X13-NONCUSP` | `Challenge/XOneThirteenNoncusp.lean` | research open | Finish the genus-two rational-point classification from the checked split-19/Pell data. |
| `MT-X18-NONCUSP` | `Challenge/XOneEighteenNoncusp.lean` | research open | Classify rational points on the checked X₁(18) genus-two model. |
| `MT-O25-EXCLUDE` | `Challenge/OrderTwentyFive.lean` | research open | Build the order-25 modular/Tate reduction and endpoint. |
| `MT-O35-EXCLUDE` | `Challenge/OrderThirtyFive.lean` | research open | Build the order-35 modular/isogeny endpoint. |
| `MT-O49-TOWER` | `Challenge/OrderFortyNine.lean` | open | Bridge exact order 49 to the already checked X₀(49) correspondence endpoint. |
| `MT-TC-E0-PRODUCT-DIM` | `upstream/tauceti/MazurTauCetiChallenge/ProductDimension.lean` | decomposed | The goal is topological-Krull-dimension additivity for a scheme fiber product. First add the missing finite-type/fiber-product dimension layer upstream. |
| `MT-TC-A2-PRODUCT-FORMULA` | `Challenge/CurveProductFormula.lean` | active | Residue-degree product formula; checked consumer is `DivisorPicard.Dictionary.degreeZero`. |
| `MT-TC-A3-DIVISOR-LINE-BUNDLE` | `Challenge/DivisorLineBundle.lean` | queued after A2 | Complete cocycle/effectivity/principal detection/surjectivity and the global Picard comparison. |
| `MT-CYCLOTOMIC-UNRAMIFIED` | `Challenge/CyclotomicClassFieldTheory.lean` | research open | Prove locally-primary pseudo-unit Kummer reciprocity, then feed the checked Kummer-Artin bridges. |

## Dependency-ordered full queue

The entries below cover every unfinished canonical node. “Blocked” records a dependency edge, not
an external blocker. Nodes on independent lanes remain eligible for parallel work.

### Finite endpoints — 100 points

1. `MT-X11-COSET` — open/compiled, 12; prove the exact Challenge contract.
2. `MT-X11-JOIN` — blocked by X11 cosets, 2; compile the unconditional order-11 exclusion.
3. `MT-X13-NONCUSP` — research-open/compiled, 26; prove the exact Challenge contract.
4. `MT-X18-NONCUSP` — research-open/compiled, 18; prove the exact Challenge contract.
5. `MT-O25-EXCLUDE` — research-open/compiled, 16; prove the exact Challenge contract.
6. `MT-O35-EXCLUDE` — research-open/compiled, 14; prove the exact Challenge contract.
7. `MT-O49-TOWER` — open/compiled, 10; prove the exact Challenge contract using the checked correspondence endpoint.
8. `MT-FINITE-JOIN` — blocked by all six endpoint lanes, 2; assemble the finite point-order callback.

### Shared geometry and isogenies — 300 points

1. `MT-TC-A2-PRODUCT-FORMULA` — active open/compiled, 15; the exact-pin A1 dependency is complete.
2. `MT-TC-A3-DIVISOR-LINE-BUNDLE` — research-open/compiled after A2, 18. Retain the checked affine/descent substrate; before freezing the overlap API add chosen-pullback transport, normalization, diagonal/triple-cocycle laws, restriction naturality, and a real `DivisorCocycle` consumer.
3. `MT-TC-B1-COHERENT-COHOMOLOGY` — blocked by A3, 35; define coherent cohomology and prove finite-dimensionality/vanishing consumers.
4. `MT-TC-B2-RR-SERRE` — blocked by B1, 25; Riemann–Roch and Serre duality.
5. `MT-TC-C1-RELATIVE-COHOMOLOGY` — blocked by B1, 30; base change and semicontinuity.
6. `MT-TC-C2-SYMMETRIC-POWERS` — blocked by A3+C1, 15; effective divisors, symmetric powers, relative Abel map.
7. `MT-TC-D1-PICARD-FUNCTOR` — blocked by A3+C1, 35; rigidified relative Picard functor, degree zero, Poincaré bundle.
8. `MT-TC-D2-PICARD-REPRESENTABILITY` — blocked by B2+C2+D1, 45; representability and properness of Pic⁰.
9. `MT-TC-E0-PRODUCT-DIM` — audited open contract, 2. The pinned API reduces it exactly to topological-Krull-dimension additivity for a scheme fiber product; the route needs integral-extension dimension invariance, finite-type tensor-product dimension/Noether normalization, or an equivalent bridge from fixed smooth relative dimension. Product-with-trivial and smooth-relative-dimension-addition boundary lemmas compile but do not yet have a permanent consumer.
10. `MT-TC-E1-JACOBIAN-VARIETY` — blocked by D2+E0, 20; Jacobian representation, dimension/genus, genus-one consumers.
11. `MT-TC-F1-ABEL-JACOBI` — blocked by C1+E1, 20; universal property, base change, closed immersion.
12. `MT-EC-ISOGENY-WEIL` — independent planned lane, 25; quotients by finite subgroups, duals, multiplication kernels, Weil pairing, and named elliptic/modular consumers.

### Prime infrastructure — 400 points

1. `MT-NERON-BASE` — blocked by E1+isogenies, 40; Néron models and mapping property.
2. `MT-NERON-COMPONENTS` — blocked by Néron base, 30; identity component and component groups.
3. `MT-NERON-SPECIALIZATION` — blocked by components, 30; specialization exactness and prime-to-residue torsion injection.
4. `MT-FFGS-BASIC` — active partial substrate, 20; point-representing kernels, constant/diagonalizable examples, the `μ_n` multiplication-kernel presentation, and quotients of constant groups are integrated. Generic finite-flat closed-subgroup quotients and kernel/quotient base-change compatibility remain mandatory.
5. `MT-FFGS-CONNECTED-ETALE` — blocked by full FFGS basic, 20; construct, rather than assume, the functorial connected–étale sequence and base change.
6. `MT-FFGS-OORT-RAYNAUD` — blocked by connected–étale, 40; Oort–Tate classification and Raynaud uniqueness.
7. `MT-X0-MODULI` — independent planned lane, 30; Γ₀ moduli problem with a downstream integral-curve consumer.
8. `MT-X0-INTEGRAL` — blocked by X₀ moduli, 30; compactification and integral model.
9. `MT-X0-CUSPS` — blocked by integral X₀, 20; cusps and rational cusp divisor.
10. `MT-X0-JACOBIAN` — blocked by integral X₀+E1+F1, 20; modular Jacobian.
11. `MT-X0-HECKE` — blocked by X₀ Jacobian+isogenies, 30; Hecke correspondences.
12. `MT-X0-EISENSTEIN-ALGEBRA` — blocked by Hecke, 30; Eisenstein ideal and quotient algebra.
13. `MT-X0-EISENSTEIN-QUOTIENT` — blocked by cusps+Eisenstein algebra+Néron specialization+Oort–Raynaud, 40.
14. `MT-CYCLOTOMIC-UNRAMIFIED` — research-open/compiled, 20; solve reciprocity contract. Do not count `divisionField_everywhereUnramified` as a ramification proof while its input structure assumes `ramificationIndexOneAtFinitePlaces`.

### Prime-order argument — 100 points

1. `MT-PRIME-SEMISTABLE` — blocked by Néron specialization+Oort–Raynaud, 10.
2. `MT-PRIME-OUTSIDE-IDENTITY` — blocked by semistability, 10.
3. `MT-PRIME-EISENSTEIN-SPECIALIZATION` — blocked by outside-identity+Eisenstein quotient, 20.
4. `MT-PRIME-DIVISION-FIELD` — blocked by Eisenstein specialization+cyclotomic lane, 15; supply the missing local ramification proof, not only the current adapter.
5. `MT-PRIME-HERBRAND-KUMMER` — blocked by division field, 10; rule out the inverse-cyclotomic class quotient.
6. `MT-PRIME-SPLIT-SEQUENCE` — blocked by Herbrand–Kummer+isogenies, 10.
7. `MT-PRIME-SHAFAREVICH` — blocked by E1+isogenies, 15.
8. `MT-PRIME-ISOGENY-CHAIN` — blocked by split sequence+Shafarevich, 10; compile the prime-order exclusion endpoint.

### Integration and hardening — 50 points

1. `MT-API-INTEGRATION` — blocked by finite join+prime isogeny chain; the exact-pin audit is complete, 10; compile `MazurTorsion.rationalTorsion_orders_mem_cyclicOrders`.
2. `MT-FINAL-ASSEMBLY` — blocked by API integration, 15; feed the unconditional order theorem to `MazurTorsion.torsion_ncard_le_of_arithmetic_inputs` and compile the final Mazur/Lean-Pool theorem.
3. `MT-EXPOSITION-AUDIT` — blocked by final assembly, 5; final axiom, source, license, prior-art, blueprint-edge, quality, clean-checkout, and authorized full-build audit.

## Checkpoint acceptance rules

- Preserve immutable Challenge statements and every canonical dependency/weight.
- A compiled conditional interface is recorded as partial infrastructure, never as proof of its hypotheses.
- Require a compiled downstream consumer before accepting a new public interface.
- Build the smallest touched Lean targets with `LEAN_NUM_THREADS=1`, then run `python3 scripts/quality.py`.
- Record proved declarations, verification, remaining critical-path gaps, and active workers in every pushed integration checkpoint.
