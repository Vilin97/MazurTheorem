# `X_0(N)` classifying-point dependency audit

Date: 2026-08-09

This note records the exact checked boundary after the elliptic quotient work
at repository revision
`b28e3fd8f273ad7fda149cf794910c2577964b25`. It makes no `MT-X0-MODULI`
completion claim.

## Verdict

The repository now constructs the actual quotient as a `CommGroupScheme`,
bundles its underlying over-scheme as a Tau Ceti `AbelianVariety ℚ`, proves
that the quotient projection is finite and étale, and identifies its
scheme-theoretic group-scheme kernel with the split finite-flat cyclic
subgroup. It also proves the corresponding finite, étale, kernel, and smooth
relative-dimension-one statements after every base change. It does not bundle
the quotient as an AINTLIB `EllipticCurve` or as a new `WeierstrassCurve`.

It still does **not** construct a represented or coarse modular-curve target,
a classifying point of that target from the cyclic datum, or an identification
of the fixed level-49 Weierstrass model with the relevant coarse modular curve.

Consequently neither intended endpoint can currently be implemented with a
codomain carrying a checked represented or coarse `Γ₀(N)` modular
interpretation:

```text
ModularCurve.XZeroModuli.pointOfRationalCyclicSubgroup
MazurTorsion.PrimeOrder.xZeroPoint_of_rationalPrimeTorsion
```

Defining either endpoint to return `RationalDatum`, `VariableChangeClass`, or a
caller-supplied point would rename the existing boundary rather than remove it.
Existence of the quotient `E/C` alone also does not manufacture a point of a
coarse moduli scheme.

## What is already checked

An abbreviated constructive dependency chain is:

```text
SchemeQuotient
  -> QuotientTorsor
  -> FiniteTranslationQuotientGroup
  -> XZeroEllipticQuotientAtlas
     + XZeroEllipticQuotientTranslation
     + XZeroEllipticQuotientGeometry
     + XZeroWeierstrassRelativeDimension
  -> XZeroEllipticQuotientRepresentability
  -> XZeroFortyNineEllipticQuotient
```

In particular, `EllipticQuotientRepresentability.quotient` constructs the
quotient scheme, `quotientAbelianVariety` bundles it as an abelian variety,
`projectionKernelIso` identifies the scheme-theoretic group-scheme kernel, and
`geometricQuotientPresentationBaseChange_kernel_exact` proves the result after
every base change. `XZeroFortyNineEllipticQuotient` is a real level-49
consumer: it accepts no supplied quotient presentation. It still takes the
concrete cubic `GrpObj` instance and an explicit
`CanonicalPointGroupLawCompatibility` proof used to construct its canonical
point equivalence.

The current moduli-facing types stop earlier:

- `XZeroModuli.RationalDatum` is a Weierstrass curve together with a split
  cyclic subgroup of its rational point group.
- `XZeroFiniteFlatModuli.SplitGammaZeroDatum` is the corresponding actual
  finite-flat subgroup scheme.
- `XZeroFiniteFlatClassifyingData` checks the round trip back to the raw
  rational datum; it produces no represented point.
- `XZeroModuli.RationalDatum.VariableChangeClass` quotients only the checked
  admissible Weierstrass changes. Its documentation explicitly disclaims a
  coarse-moduli interpretation.
- `XZeroFortyNineTransfer` still accepts a classifying function and its two
  noncuspidality laws from the caller. Nothing connects that function to the
  constructed elliptic quotient.

A read-only axiom audit of the quotient chain, its arbitrary-base-change
kernel theorem, and the level-49 quotient consumer reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Exact dependency audit

The core project uses Lean `v4.33.0-rc1`, Mathlib revision
`79d0395a1825a6264ad5d269e35e60537518955e`, and Tau Ceti revision
`a74dfee78f800df63f085a19006f7d502eee365e`.

No represented `X_0(N)`, coarse `Y_0(N)` classifying transformation, or
level-49 model-identification theorem was found in the project, its exact
Mathlib tree, its exact Tau Ceti tree, or LeanPool revision
`c2223fd6be2a245929bf777c01df1577f724d3f3`, the repository pin recorded in
`docs/PRIOR_ART.md`. LeanPool does contain prime-uniform analytic
modular-polynomial existence theorems: `Chudnovsky.exists_PhiQ_closed` in
`LeanPool/Chudnovsky/SingularModuli/ModularPolynomialQ.lean:1283` and
`Chudnovsky.exists_PhiZ_closed` in
`LeanPool/Chudnovsky/SingularModuli/ModularPolynomialZ.lean:830`. Their
contracts identify an orbit polynomial of complex upper-half-plane functions
with a specialization at analytic `j`; no theorem connects them to Mathlib
Weierstrass `j`, the constructed algebraic quotient, or the
zero-locus/cyclic-isogeny moduli interpretation needed here.

That LeanPool revision itself tracks Lean `v4.32.0-rc1` and Mathlib
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`, not the Mazur project's exact
pin. The two source files have explicit Xuanji Li and Apache-2.0 headers; their
exact blobs are `025d23267dfc18110f9b8cee6c04164b0d41e616` and
`c4da9c8753b8688d237e1df19a70ba7d99cb23a2`, and that revision's root
Apache-2.0 `LICENSE` blob is
`57bc88a15a0ee8266c259b2667e64608d3f7e292`.

The latest audited AINTLIB `dev/modular-curves` revision is
[`f6037f1f861eb74bd32f3333348bafd42164a7c8`](https://github.com/CBirkbeck/AINTLIB/commit/f6037f1f861eb74bd32f3333348bafd42164a7c8).
It uses the same Lean compiler but Mathlib revision
`3edb3c0658f69f197b1e501b1f7623f3f7b3898c`, 266 commits after the immutable
Mazur pin. The six relevant source blobs are unchanged from the previously
audited
[`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`](https://github.com/CBirkbeck/AINTLIB/commit/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684)
snapshot: `Moduli/CoarseSpace.lean`,
`Moduli/Coarse.lean`, `GroupScheme/CyclicSubgroup.lean`,
`GroupScheme/NIsogeny.lean`, `GroupScheme/NIsogSpace.lean`, and
`Moduli/GammaHRepresentability.lean`. The later
`Moduli/GammaFullToGammaOne.lean` file is not one of those six.

AINTLIB has substantial relevant scaffolding:

- `GroupScheme/CyclicSubgroup.lean:151-157` defines
  `GammaZeroStructure`.
- `Moduli/CoarseSpace.lean:248-250` constructs the scheme `YZeroCoarse` as the
  relative-invariant Borel quotient of the base scheme of the full-level
  representing `EllObj`.
- `Functor.RepresentableBy.coarsePr_existsUnique_lift` at lines 164-169 is
  the categorical quotient property for invariant morphisms *out of* the
  base scheme of that full-level object.

It does not supply the map needed here. `CoarseSpace.lean:37-41` explicitly
states that this scheme represents nothing and defers its geometric-points
description. No declaration maps `GammaZeroStructure` or a rational cyclic
datum to a point of `YZeroCoarse`.

The apparent alternatives do not close that gap:

- `EllipticCurve.exists_nIsogSpace` and
  `EllipticCurve.exists_gammaZeroSpace` are explicit `sorry` declarations.
- `NIsogModuli.exists_gammaZeroSpace` is conditional on a supplied
  `NIsogModuli`; AINTLIB has no checked theorem or definition constructing an
  inhabitant from the available data. Its use of `exists_cyclicityLocus` has
  an axiom cone containing the explicit-`sorry` theorem
  `generatorSpace_finiteLocallyFree_of_isGammaZeroFppf`.
- `ModularCurves.exists_coarse_gammaH` is an explicit `sorry` and only describes
  points over algebraically closed fields.
- `QuotientProblemData` and `gammaHNaive_toQuotient` concern geometric
  full-level orbits; they neither consume `GammaZeroStructure` nor produce a
  rational point of `YZeroCoarse`.

After comments and strings are removed, the current AINTLIB `CoarseSpace`
transitive closure contains 363 local AINTLIB-workspace modules and 45 `sorry`
occurrences in 19 files. The cone also uses source-level transparency and
heartbeat options forbidden in this repository. These source counts do not
by themselves show that every individual AINTLIB endpoint has nonstandard
axioms: unused open declarations in an imported file need not occur in a
theorem's axiom closure. They do show that a port must isolate and check its
precise declaration cone rather than copy this source closure wholesale.

The AINTLIB development branch has no root `LICENSE`. Five of the six files
named above have explicit Apache-2.0 headers. `GroupScheme/NIsogeny.lean` does
not; its development-branch blob
`71908700f09d4a1cce77b7e45407355aceaa6aaf` is byte-identical at licensed
default-branch commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, whose root
Apache-2.0 `LICENSE` blob is
`8dada3edaf50dbc082c9a125058f25def75e625a`. Any future port still needs a
file-by-file license and exact-import-cone review.

The four additional Gamma-one files cited below all have explicit Apache-2.0
headers at `f6037f1f861eb74bd32f3333348bafd42164a7c8`. Their exact blobs are
`4809e869324112d81f7c8963855bee7af41762b7` for `ModelRecord.lean`,
`c64a5935d8b886faf3a912447e37a20a6c1fa480` for
`AffinePointSection.lean`,
`3a82e1c48198254cfdda9c004778fbee63e79e96` for
`AffineSectionSpecPoints.lean`, and
`ec653e27c1d0081724e44e23d948b53b2142e467` for `YOneTatePoint.lean`.
All four blobs are also byte-identical at the licensed default-branch commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b` identified above.

No small, exact-pin, source-clean, option-compliant AINTLIB port yielding the
requested classifying point was identified. Porting only the Borel definition
or the conditional assembly would add unused infrastructure or recreate a
supplied boundary.

## Independent construction routes checked

### 1. General coarse `Y_0(N)`

The standard construction first represents an auxiliary rigid full-level
problem and then takes a finite group quotient. This is the route in
[Katz--Mazur, Chapter 8](https://www.jstor.org/stable/j.ctt1b9s05p) and in
[Loeffler's modular-curves notes](https://warwick.ac.uk/fac/sci/maths/people/staff/david_loeffler/teaching/modularcurves/lecture_notes.pdf).

At the exact pin, the project has neither the full-level moduli problem and
universal elliptic curve nor the natural transformation from Gamma-zero
objects to the quotient. Generic `Functor.RepresentableBy` and quotient-scheme
APIs cannot supply those mathematical inputs. The stabilizer `[-1]` also
prevents treating the naive Gamma-zero isomorphism-class functor as a fine
represented functor.

### 2. Split datum through `Y_1(N)`

The local datum is stronger than a general Gamma-zero datum: its finite cyclic
subgroup is pointwise rational, and `RationalCyclicSubgroup.generator` chooses
a rational generator. Mathematically this permits a route through the fine
open curve `Y_1(N)`, followed by the forgetful map to coarse `Y_0(N)`.

No such fine scheme, classifying morphism, or forgetful scheme morphism exists
in the local dependency graph. AINTLIB has two unbridged fine-curve
constructions: `yOneEllObj` represents `gammaOneNaiveProblem`, whereas
`YOneFine` is the base of a representative of `semiBorelQPD.prob`. No theorem
identifies those moduli problems or their representing schemes. There is also
no `YOneFine -> YZeroCoarse` morphism or quotient universal property for
`piOneFine`. The available map supplies only the upstream
full-level-to-Gamma-one leg `Y(N) ⟶ Y_1(N)`; there is no descent or universal
property producing the required Gamma-one-to-Gamma-zero morphism.

A later history audit found an important refinement. AINTLIB commit
`4887bb8224d8affd4b127a3827a065514c54197e` reports the direct theorem
`gammaOneNaive_representable` with axiom closure exactly `propext`,
`Classical.choice`, and `Quot.sound`. Commit
`4b93c0d423dd009ecb6f4bb8497bfa3f0df655e5` then moves that tree to Lean
`v4.33.0-rc1` and Mathlib `a5b963235893...`; the Mazur Mathlib revision
`79d0395a1825a6264ad5d269e35e60537518955e` is only three Mathlib commits
earlier. This makes a declaration-sliced exact-pin port materially more
plausible than the latest-revision gap suggested. It does not make a wholesale
source port admissible: `YOneTatePoint.lean` still imports a broad tree with
unrelated open declarations and forbidden source options, so the clean
headline axiom audit must be preserved by extracting only its actual theorem
cone.

Current AINTLIB supplies the concrete model-and-point infrastructure for the
first conversion steps. `EllipticCurve/ModelRecord.lean:73` defines
`modelEllipticCurve` from a Weierstrass model; only the routine `EllObj` record
wrapper remains. `EllipticCurve/AffinePointSection.lean:95` defines
`projModelAffineSection` from affine coordinates, and
`EllipticCurve/AffineSectionSpecPoints.lean:208` defines
`modelPointAddEquiv` between model-scheme points over a field extension and
Mathlib affine points. The value of that equivalence on the constructed
section is separately pinned by
`projModelPointsEquiv_affineSectionSpecPoint` at line 173.

What is not packaged is the end-to-end proof that the section obtained from
`RationalDatum.generator` and `addOrderOf_generator` satisfies AINTLIB's
`IsNaiveGammaOne`. `LevelStructure/Basic.lean:68` requires global `N`-killing
and exact order in every algebraically closed geometric fibre. This is a local
proof bridge rather than missing curve, section, or group infrastructure. The
audited upstream ingredients suffice: express each geometric point of
`Spec K` as a field map, use injectivity to preserve `addOrderOf`, and
transport through `modelPointAddEquiv`. That composite proof is not packaged,
has not been checked at the Mazur pin, and none of these newer upstream
adapters is ported into the local dependency graph.

The local coordinate API does prove the first algebraic step: injectivity of
`WeierstrassCurve.Affine.pointMap` preserves the generator's `addOrderOf = N`
over every field extension. The local tree has no theorem identifying the
pullback of `projectivePointOverMorphism` with that coordinate map, however,
and it has no `EllObj` or `IsNaiveGammaOne` consumer. Adding only the coordinate
lemma would therefore create an unused interface rather than a classifying
construction.

The smallest uniform candidate found is therefore more direct than bridging
the two AINTLIB Gamma-one constructions: transport the natural `(ZMod N)ˣ`
action `P ↦ u • P` on `gammaOneNaiveProblem` across
`yOne_representableBy`, act on `yOneEllObj.base`, and form its
relative-invariant quotient. AINTLIB has a generic represented-functor action
and relative-invariant quotient engine (`RepresentableBy.autMulHom`,
`baseSchemeAction`, and `coarseQuotient`), but no specific units action on this
Gamma-one functor, induced quotient classifier, orbit theorem for split
Gamma-zero data, or comparison with `YZeroCoarse`. None of that generic engine
is in the exact-pin local graph. Invariance of the quotient projection under
the units action would prove independence of the chosen generator; the
geometric orbit theorem is the separate obligation that gives the quotient
its intended coarse modular interpretation.

The Mathlib-only Yoneda part of that route is now isolated locally as the
byte-identical AINTLIB leaf `ForMathlib/RepresentableAut.lean` (exact blob
`de1c89486034c2a167d7bb0200360148662091d0`). Once the fine representative is
available, no additional coarse-space framework is required: transport the
units automorphisms with `RepresentableBy.autMulHom`, project them to the base
scheme, and apply the already integrated affine quotient engine to the top
affine open of `yOne`. The remaining hard work is consequently the fine
representative, its rational generator/section dictionary, the units action
on the moduli functor, and presentation compatibility—not another generic
scheme-quotient construction.

The first declaration-sliced fine-`Y₁` prerequisites have since been
isolated and compiled at the immutable pin. The retained
`ForMathlib/TateNormalForm.lean` supplies the Tate coordinate change,
division-polynomial bridge, and uniqueness theorem with a standard-only axiom
closure. `XZeroGammaOneTateBase.lean` then constructs the canonical
ring-equivalence for `ℤ[A,B][Δ⁻¹]`, the relative affine base
`Spec R[A,B][Δ⁻¹]`, and its elliptic Tate equation. The independent
`ForMathlib/ProjFromGlobalSectionsMap.lean` leaf supplies the homogeneous
coordinate naturality required for scheme sections. The exact
`ForMathlib/GradedQuotient.lean` leaf supplies the grading on a homogeneous
quotient. These leaves make no representability claim.

`XZeroGammaOneTateProjectiveFamily.lean` now implements the honest smaller
route: `Proj` of the homogeneous quotient by the Weierstrass equation, with
normalized coordinate evaluations for the `[0:1:0]` zero section and
`[0:0:1]` marked section. It retains nilpotent base structure and works over
arbitrary commutative rings. The two sections and their structure-map
identities compile with a standard-only axiom closure. The companion
`XZeroGammaOneTateProjectiveBaseChange.lean` constructs their categorical
pullback along every scheme morphism and pins the pullback square and both
pulled-back section identities. It does not assert the stronger identification
with `Proj` after coefficient extension, for which the exact Mathlib pin has
no general scalar-extension theorem. The clean degree-zero argument in
`XZeroGammaOneTateProjectiveProper.lean` also identifies the base ring and
proves the universal family projection proper, again with standard-only
axioms.

The chartwise surjectivity and principal-kernel facts for the homogeneous
quotient are now isolated in `ForMathlib/ProjQuotientAway.lean`; the public
endpoints compile with the same standard-only axiom closure. This slice omits
the source's option-dependent closed-immersion theorem. The independent
`ForMathlib/StandardSmoothHypersurface.lean` leaf now gives the localized
hypersurface standard-smooth calculation under default options, also with a
standard-only axiom closure. A separate attempted shortcut through Mathlib's
division polynomials does not yet remove the group law boundary: at the
immutable pin those files define and control the polynomials, but expose no
checked theorem identifying their vanishing at a nonsingular point with
`n • P = 0`. Consequently no exact-level locus or generic-prime classifier is
inferred from polynomial vanishing alone.

The exact-pin `ForMathlib/ProjectiveSpaceChart.lean` slice now identifies a
projective-space away chart with the polynomial ring in the other variables,
without importing the independent `AwayCongr` cone. The local
`XZeroGammaOneTateProjectiveChartCover.lean` leaf proves that the three
coordinate basic opens cover the homogeneous quotient model. Both public
boundaries have standard-only axiom closure. They still do not identify the
quotient chart with the dehomogenized hypersurface quotient or construct the
scheme/affine-point dictionary.

The repository's older projective-cubic API could not supply this family: it
is restricted to fields and constructs the reduced induced closed subscheme
of projective space. Extending that object to `tateRingOver R` would discard
nilpotent base structure. The next semantic boundary is now the genuine
projective group law and integer-multiplication morphisms, which must precede
the killed loci. The literal AINTLIB multiplication route traverses the large,
option-dependent chart-globalization and group-law-axiom cones. Defining the
eventual bare locus from the explicit marked section, rather than upstream's
opaque choice `tatePoint := choose exists_tatePoint`, still avoids dragging
the separate `YOneAtlasClassify` cone into the scheme construction, but it
cannot avoid the multiplication theorem itself.

The post-fine coarse audit also sharpens the quotient step. Since the intended
fine `Y₁` base is affine, its split-`Γ₀` target should be the direct affine
quotient of the stable top open,
`Spec (Γ(Y₁, ⊤)^((ZMod N)ˣ))`, rather than the general glued quotient. The
latter's affineness theorem unnecessarily asks for a point of `Y₁`; the direct
`localQuotient` construction has a categorical invariant-map universal
property without that assumption. The represented action has an inverse
variance convention: a functor automorphism scaling `P` by `u` is transported
by `SchemeAction.ofAut` to the base action classifying `u⁻¹P`. Any classifier
compatibility theorem must pin this inverse explicitly.

This affine quotient is only a split-`Γ₀` coarse candidate until two semantic
obligations are proved: algebraically closed field-valued morphisms have equal
quotient composites exactly when their fine objects differ by a unit, and
those orbits identify with cyclic-subgroup isomorphism classes. The existing
prime-spectrum orbit theorem does not establish either statement for
`Spec k` morphisms. Coarse quotient formation is likewise not claimed to
commute with arbitrary base change.

The alternative `YOneFine` route would first need an isomorphism between
`gammaOneNaiveProblem` and `semiBorelQPD.prob`, a morphism
`YOneFine ⟶ YZeroCoarse`, and compatibility of that morphism with
`piOneFine` and the generic Borel coarse projection from the full-level base.

The `YOneTatePoint` import closure has 277 local AINTLIB-workspace modules, 41
`sorry` occurrences in 16 files, and forbidden source options. The direct
Gamma-one master itself records a standard-only axiom closure, but its source
tree is not a small compliant port. This route also requires separate
treatment of levels 2 and 3 because the audited Gamma-one representation
assumes `4 <= N`.

### 3. The quotient and a modular-polynomial or `j`-pair

The new quotient is a Tau Ceti `AbelianVariety`; a separate theorem proves its
structure morphism smooth of relative dimension one. Neither the local
project nor the exact Tau Ceti pin provides a construction from this object to
a `WeierstrassCurve`, a `j`-invariant extractor, or a comparison with
Mathlib's explicit Weierstrass invariants. LeanPool's analytic
`exists_PhiQ_closed` and `exists_PhiZ_closed` theorems do not identify an
algebraic zero locus with cyclic isogenies. Hence they do not yet send the
constructed quotient to a represented modular-polynomial target.

### 4. Explicit level 49

The Kubert files contain significantly more special-purpose arithmetic:

- `orderSevenHauptmodulAt_spec` normalizes an exact order-seven point;
- `orderSevenQuotient` and `orderSevenPointMap` give explicit Velu formulas;
- `orderSevenG7F` is the level-seven correspondence polynomial; and
- `XZeroFortyNine.no_noncuspidal_correspondence_point` rules out rational
  solutions `G(s,B) = 0` with both coordinates nonzero.

There is a concrete primary-literature route for the missing special-case
comparison. Hoshino--Nakamura record the following explicit model of
`X_0(49)`:

```text
v^2 = 4*u^3 + 21*u^2 + 28*u
```

and give its degree-seven map to `X_0(7)` by

```text
s = ((u^2 + 7*u + 7)*v + 7*u^3 + 35*u^2 + 49*u + 16) / 2.
```

The change `X = 4*u`, `Y = 4*v` gives exactly the repository equation
`Y^2 = X*(X^2 + 21*X + 112)`. Algebraically translating the displayed
Hauptmodul by `t_7 = s - 8` gives the following candidate normalization in
the repository coordinates:

```text
t_7 = (Y*(X^2 + 28*X + 112) + 7*X*(X^2 + 20*X + 112)) / 128.
```

The source also identifies the point at infinity as the totally ramified cusp.
See Hoshino--Nakamura, *Belyi Function on `X_0(49)` of Degree 7*, Math. J.
Okayama Univ. 52 (2010), 61--63,
[Proposition A](https://ousar.lib.okayama-u.ac.jp/files/public/3/33500/20160528030831731188/fulltext.pdf).
The source is copyrighted. It is an external mathematical design reference:
a Lean port should rederive the identities algebraically with attribution, and
no source code is being vendored from it. The formulas are not a substitute
for the moduli theorem. In particular, the translated normalization still
needs a checked `j`-identity and the second degeneracy-coordinate or Fricke
comparison before it can be identified with the repository correspondence.

This is not yet a represented-moduli construction. `orderSevenPointMap` is a
point function, not the projection of the newly constructed quotient scheme,
and no theorem identifies `orderSevenQuotient` with
`EllipticQuotientRepresentability.quotientAbelianVariety`. The explicit
nonbacktracking path also still depends on
`OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence3`,
for which no proof exists. Completing that certificate and the remaining Tate
normalization/kernel bridge could finish a separate pointwise arithmetic
order-49 contradiction through `no_noncuspidal_correspondence_point`. It would
not implement `MT-X0-MODULI`: that goal still requires a represented point and
a modular interpretation compared with the actual quotient.

Finally, `XZeroFortyNineDescent.curve` is a checked `WeierstrassCurve`; the
generic construction `WeierstrassProjectiveCubic.scheme curve` supplies its
projective cubic scheme. The repository does not prove that this cubic is the
compact coarse `X_0(49)` or that `0` and `T` are precisely its cusps.
`XZeroFortyNineTransfer` internally assembles an element of Mathlib's
`curve.toAffine.Point` from a noncuspidal rational correspondence solution.
Despite the type name, `.zero` is the point at infinity, and this coordinate
point is not itself a scheme morphism. The separate generic
`WeierstrassProjectiveCubic.affinePointMorphism` can convert a coordinate point
to `Spec ℚ ⟶ scheme curve`, but the transfer file exposes neither that
composite nor a family morphism, birational equivalence, inverse, extension
across cusps, or modular interpretation and compatibility with the actual
quotient. For nonsquarefree level 49, this is not a harmless naming issue:
[Cesnavicius, *A modular description of X_0(n)*](https://arxiv.org/abs/1511.07475)
shows that the naive cyclic-subgroup compactification disagrees at the cusps
with the Deligne--Rapoport model and requires a refined moduli description.

## Smallest honest next theorem sequence

For the smallest identified split-`Y_1` route, the core classifying-point
boundary requires steps 1 through 5 below rather than a new conditional
wrapper:

1. Starting from the now-checked Tate-normal-form and relative-affine-base
   leaves, construct the universal projective Tate family, its zero and
   explicit `(0,0)` marked sections, and the minimum killed/open loci needed
   for the exact-pin `yOneEllObj` representative over `Spec ℚ`, where `N` is
   invertible. Then prove that the generator of a `RationalDatum ℚ N` defines
   an `IsNaiveGammaOne` section. Treat levels 2 and 3 separately.
2. Construct the `(ZMod N)ˣ` action, its relative-invariant quotient, and the
   projection's units-invariance. Prove the geometric orbit theorem that gives
   this target its coarse Gamma-zero modular interpretation. Then construct
   either the full natural classifying transformation or the exact
   field-valued theorem sending an actual split datum over `ℚ` to a morphism
   `Spec ℚ ⟶ Y_0(N)` with the required structure-map equation.
3. Prove that the classifying map is invariant under isomorphism, choice of
   generator, and admissible Weierstrass changes. A general full-level/Borel
   construction may replace steps 1 and 2 only if it proves the equivalent
   classifying and coarse-point contracts.
4. Make `pointOfRationalCyclicSubgroup` internally consume the checked split
   finite-flat subgroup and constructed elliptic quotient. It must also
   construct or bypass the quotient layer's current `GrpObj`, group-law
   compatibility, and point-equivalence inputs; accept neither a quotient nor
   a classifying point from the caller.
5. Define `PrimeOrder.xZeroPoint_of_rationalPrimeTorsion` by applying that map
   to `RationalCyclicSubgroup.ofPoint`, with a real generic-prime consumer and
   a concrete order-49 specialization into the new coarse target.
6. For level 49, prove the modular identification of the target with the
   checked explicit model, including the open/cusp comparison, and compile the
   order-49 contradiction without `classify` or `hclassify` arguments.
7. Audit the new public endpoints with `#print axioms`; the accepted result is
   the same standard-only closure as the quotient layer.

Step 6 is the additional requirement for connecting the new moduli point to
the repository's existing explicit `X_0(49)` descent and contradiction; it is
not required merely to construct the generic classifying-point endpoint.

Until those constructions exist, adding a public `X_0(N)` point name would
overstate what the checked dependency graph proves.
