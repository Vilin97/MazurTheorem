# Third-party notices

## EllipticCurves

- Author and upstream maintainer: Michael Stoll
- Source: https://github.com/MichaelStollBayreuth/EllipticCurves
- Source commit: `3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`
- License: Apache License 2.0; see `LICENSE`

The retained modules have been modified for Lean `4.33.0-rc1` and mathlib
`79d0395a1825a6264ad5d269e35e60537518955e`. The modifications and exact
production-file manifest are recorded in `PORTING.md`.
`MazurTorsion/EllipticCurve/NonsingularReduction.lean` and
`MazurTorsion/EllipticCurve/NonsingularReductionAdditive.lean` are downstream
singular-fibre adaptations of the pinned good-reduction construction and
retain Michael Stoll's author credit.

## Variable-change implementation and local singular-cubic extension

- Copyright holders recorded in source: Kevin Buzzard; Vasily Ilin for the local extension
- Authors recorded in source: Michael Stoll, Claude, and Vasily Ilin
- Files:
  - `MazurTorsion/EllipticCurve/VariableChange.lean`
  - `EllipticCurves/VariableChange.lean`
- License: Apache License 2.0; see `LICENSE`

The original copyright, license, and author credit remain in the retained implementation.
Its header additionally records Vasily Ilin's derivative-transport and singular-cubic
nonsingular-locus generalization. The compatibility file avoids duplicating the declarations.

## Lean Pool torsion foundations

- Author: Victor Aguiar
- Source:
  https://github.com/vaguiarl/lean-pool/tree/vaguiarl/mazur-foundations/LeanPool/MazurTorsionFoundations
- Source commit: `60bec1602de9e747b67ad69641bcfb4265849123`
- License: Apache License 2.0; see `LICENSE`

The retained `TwoTorsion.lean`, `ThreeTorsion.lean`, and
`FullFourTorsion.lean` files preserve their source headers. The exact-pin
audit and local changes are recorded in `docs/PRIOR_ART.md`.

## Lean Pool Grothendieck vanishing

- Authors and copyright holders recorded in source: Vasily Ilin and Brian Nugent
- Source: https://github.com/Vilin97/lean-pool/tree/4eef1ffb3b643d606665e3b5585aa69454e137d1/LeanPool/GrothendieckVanishing
- Source commit: `4eef1ffb3b643d606665e3b5585aa69454e137d1`
- Upstream Lean 4.33 migration reference: `cc54a3adb51cb00b78cbe025818a24b676aeada7`
- Migration co-authors recorded upstream: `github-actions[bot]`, Vasily Ilin,
  and Claude Opus 5
- License: Apache License 2.0; see `LICENSE`

The 15 retained modules are stored under
`MazurTorsion/Upstream/LeanPool/GrothendieckVanishing/` with their original
headers. They prove Grothendieck vanishing for abelian sheaves on Noetherian
topological spaces. The local exact-pin adaptations and the named smooth
proper curve consumer are recorded in `PORTING.md` and `docs/PRIOR_ART.md`.

## AINTLIB geometry foundations

- Upstream authorship retained from the selected file headers: Chris
  Birkbeck, Kenny Lau, Claude Fable 5, Claude Opus 4.8, and the AINTLIB
  ModularCurves contributors
- Source: https://github.com/CBirkbeck/AINTLIB
- Primary source snapshot:
  `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`; the three later prerequisite
  leaves and their exact revisions are identified below
- Source paths:
  - `projects/ModularCurves/ModularCurves/ForMathlib/CartierDual.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafOfModulesMonoidal.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleSheaf.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SheafCohomologyExact.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/FinitePresentationOfFinite.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/BaseChangeAlongCompat.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/InvariantBaseChange.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/InvariantLocalization.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/RepresentableAut.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/GradedQuotient.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/ProjFromGlobalSectionsMap.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TateNormalForm.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SpecGroupAction.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/PullbackLocalAtTarget.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/InvariantTorsor.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/EtaleCancellation.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/AffineQuotient.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeQuotient.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/SchemeActionFree.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/TorsorMap.lean`
  - `projects/ModularCurves/ModularCurves/ForMathlib/QuotientTorsor.lean`
  - `projects/ModularCurves/ModularCurves/Picard/Pic.lean`
- Additional adapted proof sources, not vendored as modules:
  - `projects/ModularCurves/ModularCurves/GroupScheme/TranslationBySection.lean`
    (blob `6223d2904bc6f2162d4ee4e77ed684a40396ef18`; Chris Birkbeck and
    Claude Opus 4.8)
  - `projects/ModularCurves/ModularCurves/Moduli/Representability.lean`
    (licensed default-branch blob
    `efd838f8a7702725bcbe974b9e7141e683eee644`)
  - `projects/ModularCurves/ModularCurves/ModularCurve/YOneAssembly.lean`
    (blob `7732e39a206a348ca7c6d59ecdb9b8359abccc33`)
  - `projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean`
    (licensed default-branch blob
    `0cea4fbbcd8f0976b8cb0949755ecacec6e58b26`)
  - `projects/ModularCurves/ModularCurves/EllipticCurve/AffinePointSection.lean`
    (blob `c64a5935d8b886faf3a912447e37a20a6c1fa480`)
- License: Apache License 2.0 as explicitly stated in the selected file
  headers or, where noted, under the audited repository-wide license. The
  adapted `TranslationBySection` blob had no header at the primary snapshot,
  but is byte-identical at AINTLIB commit
  `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, under root Apache-2.0 license
  blob `8dada3edaf50dbc082c9a125058f25def75e625a`. The needed
  `Representability.lean` prefix occurs in the licensed default-branch blob
  listed above; `YOneAssembly.lean` is byte-identical there and has an
  explicit Apache-2.0 header. See `docs/PRIOR_ART.md`.

The selected files are stored under `MazurTorsion/Upstream/AINTLIB/`. The two
sheaf-cohomology files preserve the upstream declarations and proofs, with
only attribution, documentation, and formatting changes. The other files
have the import and exact-pin compatibility adjustments recorded in
`PORTING.md`; source-level option commands and linter findings were removed.
The thirteen finite-action quotient files retain the upstream statements and
namespaces. Besides internal import repointing, formatting, and removal of
source-level compatibility options and linter suppressions forbidden by this
repository, `SpecGroupAction` has explicit coercion and primality witnesses
and `BaseChangeAlongCompat` uses the pinned Mathlib finite-affine and
fpqc-to-fppf proof APIs explicitly. `SchemeQuotient` uses current affine-open
naturality and diagonal-composition APIs. `QuotientTorsor` makes the affine
action invariance and pullback representatives explicit. No statement is
weakened. The additional adapted proof sources and their exact-blob license
evidence are described above. No AINTLIB geometry source beyond the listed
vendored or adapted files is included. Details are recorded in `PORTING.md`
and `docs/PRIOR_ART.md`.

`RepresentableAut.lean` is an unchanged, Mathlib-only Yoneda transport leaf,
with exact upstream blob `de1c89486034c2a167d7bb0200360148662091d0`. Its
explicit Apache-2.0 file header is retained; the identical blob also occurs at
the licensed default-branch commit named above.

`ProjFromGlobalSectionsMap.lean` comes from AINTLIB commit
`4b93c0d423dd009ecb6f4bb8497bfa3f0df655e5`, exact source blob
`7bab020b5a677bd1d6c6d63c1d28e007158767c0`, with its explicit Chris
Birkbeck Apache-2.0 header. Its only local exact-pin change is a proof-level
`show`-to-`change` elaboration repair. `TateNormalForm.lean` is unchanged from
AINTLIB blob `6955ff2b550043b1a430433348067ef7b7ec416e`, identical at the licensed
default-branch commit; its retained header attributes the original Mathlib PR
#25218 implementation to Kenny Lau and distinguishes AINTLIB's additions.

`GradedQuotient.lean` is unchanged from AINTLIB blob
`4ddeb0cda0187baa7c7f785e9e4ca6cc007625ec`, identical at the licensed
default-branch commit, and retains its explicit AINTLIB contributors
Apache-2.0 header.

`ProjQuotientAway.lean` selectively adapts the away-map surjectivity and
principal chart-kernel declarations from AINTLIB `ProjClosedImmersion.lean`,
exact blob `7713fc7254aadc94b713028a74178b0ec439e1f6`, identical at the licensed
default-branch commit. The option-dependent scheme closed-immersion theorem
is not included.

`StandardSmoothHypersurface.lean` adapts AINTLIB blob
`a1640ea5835d14050eea045a8ce3bacdb0504659`, identical at the licensed
default-branch commit and carrying Chris Birkbeck's explicit Apache-2.0
header. Its sole source transparency option is replaced by an explicitly
typed injectivity helper; the mathematical declarations and formulas are
retained.

The local `XZeroGammaOneTateBase.lean` adapts only the Tate normalization,
relative ring/base formulas, and proper-divisor lemma from the two listed
sources. It does not port or claim their fine-moduli representability or
classifying constructions.

The local `XZeroGammaOneTateProjectiveFamily.lean` adapts only the clean
homogeneous-quotient `Proj`, structure-map, infinity-section, and affine-origin
section prefixes from the two listed elliptic-model sources. Their explicit
Chris Birkbeck Apache-2.0 headers and exact licensed blobs are preserved in the
record above. The local proof removes the source transparency-option
dependency. A separate local leaf adapts the clean degree-zero and properness
prefix from the same `WeierstrassModel` blob. These files make no smoothness,
group-law, killed-locus, or moduli claim.

## AINTLIB Hilbert 92 and Hilbert 94 foundations

- Upstream author identified from repository authorship/history: Chris Birkbeck
- Source: https://github.com/CBirkbeck/AINTLIB
- Source commit: `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`
- Source paths:
  - `projects/FltRegular/FltRegular/NumberTheory/CyclotomicRing.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/SystemOfUnits.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/Hilbert92.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/Unramified.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/RegularPrimes.lean`
  - `projects/FltRegular/FltRegular/NumberTheory/Hilbert94.lean`
- License: Apache License 2.0 under the upstream repository-wide license; see
  `LICENSE`. The local selected files carry added attribution headers.

The selected files are stored under
`MazurTorsion/Upstream/AINTLIB/FltRegular/NumberTheory/`; only the
class-group power lemma is retained from `RegularPrimes.lean`. Imports and
proof details were adapted to the immutable Mathlib pin, including an
option-free universe-shrinking bridge for Hilbert 90. Details are recorded in
`PORTING.md` and `docs/PRIOR_ART.md`.

## Tau Ceti

- Upstream source: https://github.com/TauCetiProject/TauCeti
- Reviewed integration source: https://github.com/Vilin97/TauCeti
- Exact dependency commit: `a74dfee78f800df63f085a19006f7d502eee365e`
- Upstream base commit: `a3913fd9111b851af857f720b4ce6721e6634183`
- License: Apache License 2.0

Tau Ceti is an exact Git dependency, not vendored source. The root package and
the separate upstream-contract package deliberately resolve the same Tau Ceti,
Lean, and Mathlib revisions. The exact feature commit adds the finite-support
theorem for scheme-theoretic orders and its `OrderSystem` consumer, together
with faithful-integral, tensor-product, scheme-product, and abelian-variety
product-dimension theorems. It also constructs the rational-function map to
the projective line and proves the residue-degree product formula for smooth
proper integral curves, with a checked Picard-zero quotient consumer. Its
commits retain Tau Ceti's repository-wide license and contributor attribution.

## Mathlib Dedekind-zeta finite-fibre argument

- Author and copyright holder: Xavier Roblot
- Source: `Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- Source commit: `79d0395a1825a6264ad5d269e35e60537518955e`
- License: Apache License 2.0

`MazurTorsion/NumberTheory/WeakChebotarev.lean` adapts the short
finite-fibre counting rewrite from Mathlib's proof of the Dedekind-zeta
class-number formula. The local file retains Xavier Roblot's copyright and
authorship; the surrounding ideal-pair injection and pole argument are new.

## AI-assisted development

Parts of the proof development were produced in Claude Code and Codex agent
sessions, then reviewed, compiled, and committed under Vasily Ilin's
direction. Files that record `Claude` in their authorship header retain that
credit. AI generation is provenance, not verification: every completion
claim is based on compiled Lean and the repository's axiom/source gates.
