import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "03 — Shared algebraic geometry and isogenies" =>

:::group "shared_geometry"
Reusable divisor, cohomology, Picard, Jacobian, Abel–Jacobi, and isogeny
infrastructure, developed upstream where possible. Stage weight: 300 points.
:::

:::theorem "MT-TC-A1-ORDER-SUPPORT" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "upstream, open, compiled, tau-ceti") (priority := "high") (effort := "large")
*Finite support of orders of rational functions.* A nonzero rational function
on a Noetherian integral scheme has nonzero order at only finitely many
codimension-one points.

*Status:* `open`; *scope:* exact compiled Tau Ceti challenge contract. The
target is
`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.finite_support_orderAt`, with
challenge bridge `MazurTauCetiChallenge.finite_support_orderAt`; it instantiates
Tau Ceti's existing `OrderSystem`.
:::

:::theorem "MT-TC-A2-PRODUCT-FORMULA" (parent := "shared_geometry") (uses := "MT-TC-A1-ORDER-SUPPORT") (tags := "upstream, open, compiled, tau-ceti") (priority := "high") (effort := "large")
*Degree-zero product formula.* Every principal divisor on a proper smooth
geometrically integral curve has residue-degree-weighted degree zero.

*Status:* `open`; *scope:* exact compiled challenge contract. The bridge
`MazurTheorem.Challenge.divisorProductFormula` pins the abstract order system to
scheme-theoretic orders of vanishing and states the residue-degree-weighted result consumed by
the checked absolute degree-zero Picard API.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem_isWeightedDegreeZero`
  State and prove the residue-degree-weighted product formula for every nonzero
  rational function on a proper smooth curve.
:::

:::theorem "MT-TC-E0-PRODUCT-DIM" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "upstream, open, compiled, tau-ceti") (priority := "high") (effort := "medium")
*Dimension of a product of abelian varieties.* Tau Ceti's abelian-variety
dimension is additive under its product construction.

*Status:* `open`; *scope:* exact compiled Tau Ceti challenge contract. The
target is `TauCeti.AlgebraicGeometry.AbelianVariety.prod_dim`, with challenge
bridge `MazurTauCetiChallenge.prod_dim`.
:::

:::definition "MT-TC-A3-DIVISOR-LINE-BUNDLE" (parent := "shared_geometry") (uses := "MT-TC-A2-PRODUCT-FORMULA") (tags := "upstream, research-open, compiled, tau-ceti") (priority := "high") (effort := "large")
*Divisor–line-bundle dictionary.* Construct the Picard group of line bundles
and identify divisor classes with line bundles on a smooth curve.

*Status:* `research_open`; *scope:* exact compiled existence-and-equivalence challenge
contract. The bridge `MazurTheorem.Challenge.divisorLineBundleDictionary`
contains the remaining global dictionary: chosen line-bundle representatives, exact principal
kernel, Picard surjectivity, and the resulting divisor-class/Picard equivalence. Checked code
derives principal-divisor line-bundle triviality and the full local-rank-one/tensor-unit Picard
comparison from those data. Conversely, it constructs the complete tensor-additive dictionary
from the full Picard comparison and divisor-class equivalence, proving these are exactly the two
irreducible global outputs. It also proves the basic-open tilde restriction isomorphism and
derives global tilde invertibility from Mathlib's finite free-localization cover and Tau Ceti
local trivializations. The checked local API supplies the unconditional affine Dedekind class
equivalence, tensor-additive module representatives, tilde line bundles detecting linear
equivalence exactly, and an absolute degree-zero D1 consumer; none is credited as the missing
global result. The localized tensor comparison is assembled into an affine tilde tensor-product
isomorphism, proving that tilde sends invertible modules to tensor units and inducing a canonical
injective module-Picard/scheme-Picard homomorphism. Consequently, the affine Dedekind divisor map
has exactly the principal divisors as kernel, descends to divisor classes, and gives an
unconditional equivalence from those classes to its scheme-Picard range; the actual tilde line
bundles are tensor-additive. It also characterizes existence of the full affine scheme-level
dictionary by the full comparison for arbitrary sheaves alone: canonical Picard surjectivity is
equivalent to the reverse tensor-unit/local-rank-one comparison. The forward affine gap is
isolated as reflection of invertibility through tilde, and a checked consumer turns that precise
localization predicate into the forward tensor-inverse comparison. None of these affine results
discharges those remaining comparison inputs or supplies global proper-curve gluing and
surjectivity.
The contract does not yet normalize the global correspondence on affine charts to the
standard-sign construction checked in the affine API.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PicardGroup`
  Expose line bundles modulo isomorphism as the Picard group of a smooth proper curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.classEquivPicard`
  Identify Weil divisors modulo principal divisors with the line-bundle Picard group.
* `structure` (`contract`): `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary`
  Record the exact forward tensor-inverse comparison, chosen line-bundle representatives,
  principal kernel, and surjectivity needed for the global equivalence; derive principal
  line-bundle triviality and the reverse Picard comparison in checked code.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.nonempty_lineBundle_iso_iff_linearlyEquivalent`
  Detect linear equivalence exactly by isomorphism of the chosen divisor line bundles.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.picardComparison`
  Recover the full equivalence between local rank-one sheaves and tensor units.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.ofClassEquivalence`
  Construct all chosen divisor line bundles from the full Picard comparison and class
  equivalence.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.nonempty_iff_picardComparison_and_classEquivalence`
  Characterize existence of the dictionary by precisely those two global outputs.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.lineBundle_add_iso`
  Identify divisor addition with tensor product of the chosen line bundles up to isomorphism.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.UniversalBasicOpenTildeTriviality`
  Package the checked restriction isomorphism on a free basic-open localization.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.universalTildeInvertibility`
  Prove global tilde invertibility from the basic-open comparison.
* `definition` (`contract`): `MazurTorsion.AlgebraicGeometry.AffineDedekind.classEquivPicard`
  Give the unconditional standard-sign affine Dedekind divisor-class/module-Picard equivalence.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.localizedTensorEquivOfIsLocalization`
  Identify the tensor of two localized modules with the localization of their tensor over an
  arbitrary chosen localization ring.
* `definition` (`contract`): `MazurTorsion.AlgebraicGeometry.AffineTilde.tildeTensorIso`
  Assemble the local fraction comparison into the objectwise tilde tensor-product isomorphism
  on an affine scheme.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.tilde_isTensorInvertible`
  Send every invertible module to a tensor-invertible tilde sheaf.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.modulePicToSchemePic`
  Give the canonical tilde-induced homomorphism from module Picard classes to scheme Picard
  classes.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.modulePicToSchemePic_injective`
  Prove that the canonical affine Picard comparison is injective.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.modulePicToSchemePic_surjective_iff_tensorUnitLocalTriviality`
  Identify surjectivity of the canonical affine Picard map exactly with the reverse
  tensor-unit/local-rank-one comparison.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.TildeReflectsInvertibility`
  Isolate the missing localization reflection from an invertible tilde sheaf to an invertible
  module.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.tensorInverseComparison_of_tildeReflectsInvertibility`
  Consume the localization reflection to construct tensor inverses for arbitrary affine
  invertible sheaves.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.picardComparison_iff_tensorInverseComparison_and_modulePic_surjective`
  Characterize the full affine Picard comparison by its forward tensor-inverse component and
  surjectivity of the canonical tilde map.
* `definition` (`contract`): `MazurTorsion.AlgebraicGeometry.AffineDedekind.lineBundle`
  Package its chosen module representative unconditionally as a Tau Ceti line bundle.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_lineBundleModule_add_equiv`
  Identify `O(D + E)` with `O(D) ⊗ O(E)` as invertible modules, unconditionally.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_lineBundle_add_iso`
  Identify `O(D + E)` with `O(D) ⊗ O(E)` for the actual tilde line bundles.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.classToSchemePic`
  Descend the canonical affine divisor construction to an injective divisor-class map into the
  scheme Picard group.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.classEquivSchemePicRange`
  Identify affine Dedekind divisor classes with the range of their canonical scheme-Picard
  realization.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.classEquivSchemePicOfTensorUnitLocalTriviality`
  Upgrade the range equivalence to the full scheme Picard group under exactly the reverse
  comparison.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.divisorToSchemePic`
  Construct the canonical affine divisor-to-scheme-Picard homomorphism through divisor classes.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.divisorToSchemePic_kernel`
  Prove that the canonical divisor-to-scheme-Picard map has exactly the principal divisors as
  its kernel.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_lineBundle_iso_iff_linearlyEquivalent`
  Detect affine Dedekind linear equivalence exactly by isomorphism of the chosen tilde line
  bundles.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_dictionary_iff_picardComparison_and_modulePicardEquivalence`
  Record the abstract two-input rewrite through a full Picard comparison and an additive
  module-Picard/scheme-Picard equivalence.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_dictionary_iff_picardComparison`
  Sharpen the affine Dedekind boundary: the full Picard comparison alone supplies the canonical
  divisor-class equivalence and hence the exact dictionary.
:::

:::definition "MT-TC-B1-COHERENT-COHOMOLOGY" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Coherent cohomology of proper curves.* Build finite-dimensional coherent
cohomology, affine acyclicity, and vanishing above degree one.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.CurveCohomology`
  Define degree-zero and degree-one coherent cohomology for sheaves on proper curves.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.CurveCohomology.finiteDimensional`
  Prove finite dimensionality, affine acyclicity, and vanishing above degree one in
  the required scope.
:::

:::theorem "MT-TC-B2-RR-SERRE" (parent := "shared_geometry") (uses := "MT-TC-B1-COHERENT-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Riemann–Roch and Serre duality for curves.* Define genus through $`H^1` and
prove Riemann–Roch, Serre duality, and the degree of the dualizing sheaf.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.genus`
  Define the genus of a proper smooth curve from the dimension of first coherent
  cohomology.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.riemannRoch`
  Provide the Riemann-Roch formula for divisors or line bundles on a proper smooth
  curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.serreDuality`
  Provide Serre duality and the resulting degree formula for the dualizing sheaf.
:::

:::definition "MT-TC-C1-RELATIVE-COHOMOLOGY" (parent := "shared_geometry") (uses := "MT-TC-B1-COHERENT-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Relative cohomology and base change.* Provide proper-flat pushforward,
cohomology-and-base-change, and semicontinuity in the form needed by Picard.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology`
  Package derived pushforward data for coherent sheaves in a proper flat family of
  curves.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology.baseChange`
  Prove the base-change comparison required by the relative Picard construction.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology.upperSemicontinuous`
  Prove upper semicontinuity of fibrewise cohomology dimensions in the required
  setting.
:::

:::definition "MT-TC-C2-SYMMETRIC-POWERS" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE, MT-TC-C1-RELATIVE-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Relative effective divisors and symmetric powers.* Represent degree-$`d`
effective divisors by $`\operatorname{Sym}^d X` and construct relative Abel
maps.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeEffectiveDivisor`
  Represent flat families of effective divisors of a fixed relative degree.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.SymmetricPower`
  Construct the relative symmetric power that represents effective divisors of degree
  d.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.relativeAbelMap`
  Construct the relative Abel map from the symmetric power to the degree-d Picard
  functor.
:::

:::definition "MT-TC-D1-PICARD-FUNCTOR" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE, MT-TC-C1-RELATIVE-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Rigidified relative Picard functor.* Define the fppf Picard sheaf, its
degree-zero subfunctor, rigidification, and Poincaré line bundle.

*Status:* `blocked`.

The checked A3 downstream adapter already transports weighted divisor degree zero to an
absolute subgroup of `Scheme.Pic` and chooses a Tau Ceti invertible-sheaf representative for
each of its elements. This is a genuine absolute precursor only; it does not claim the relative
fppf functor or representability.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativePicardFunctor`
  Define the rigidified fppf sheaf of line bundles modulo pullbacks from the base.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativePicardFunctor.degreeZero`
  Define the degree-zero subfunctor used to construct the relative Jacobian.
* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PoincareBundle`
  Package the normalized universal line bundle on the curve times its Picard space.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.degreeZero`
  Transport weighted degree-zero divisor classes to the absolute scheme Picard group.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.degreeZeroRepresentative`
  Choose an actual invertible-sheaf representative for every transported degree-zero class.
:::

:::theorem "MT-TC-D2-PICARD-REPRESENTABILITY" (parent := "shared_geometry") (uses := "MT-TC-B2-RR-SERRE, MT-TC-C2-SYMMETRIC-POWERS, MT-TC-D1-PICARD-FUNCTOR") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Representability and properness of $`\mathrm{Pic}^0`.* Represent the
degree-zero Picard functor and prove that its group scheme is proper and
geometrically connected.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme`
  Package a group scheme representing the degree-zero relative Picard functor.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme.representsDegreeZero`
  Prove the representing equivalence between points of PicardScheme and the degree-
  zero Picard functor.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme.proper_geometricallyConnected`
  Prove properness and geometric connectedness of the represented degree-zero
  component.
:::

:::definition "MT-TC-E1-JACOBIAN-VARIETY" (parent := "shared_geometry") (uses := "MT-TC-D2-PICARD-REPRESENTABILITY, MT-TC-E0-PRODUCT-DIM") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Jacobian variety and sanity checks.* Bundle $`\mathrm{Pic}^0` as an abelian
variety, prove that its dimension is the genus, and recover an elliptic curve
from its pointed genus-one Jacobian.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian`
  Package the represented Picard degree-zero component as an abelian variety.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.dimension_eq_genus`
  Identify the dimension of the Jacobian with the genus of the curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.ellipticCurveEquiv`
  Prove the pointed genus-one sanity check identifying an elliptic curve with its
  Jacobian.
:::

:::theorem "MT-TC-F1-ABEL-JACOBI" (parent := "shared_geometry") (uses := "MT-TC-C1-RELATIVE-COHOMOLOGY, MT-TC-E1-JACOBIAN-VARIETY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Abel–Jacobi universal property and base change.* Construct the Abel–Jacobi
morphism, prove its universal property and base-change compatibility, and show
it is a closed immersion in positive genus.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi`
  Construct the pointed Abel-Jacobi morphism from a curve to its Jacobian.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_universal`
  Prove the universal factorization property for pointed morphisms to abelian
  varieties.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_baseChange`
  Prove compatibility of the Abel-Jacobi construction with base change.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_closedImmersion`
  Prove that Abel-Jacobi is a closed immersion for curves of positive genus.
:::

:::definition "MT-EC-ISOGENY-WEIL" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, planned, nouns-missing, mathlib") (priority := "high") (effort := "large")
*Elliptic-curve isogenies, quotients, duals, and Weil pairing.* Supply
finite-subgroup quotients, dual isogenies, multiplication kernels, and the
Weil pairing, all compatible with base change.

*Status:* `planned`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `EllipticCurve.Isogeny`
  Package finite morphisms of elliptic curves with their group-homomorphism and degree
  data.
* `definition` (`proposed`): `EllipticCurve.quotientByFiniteSubgroup`
  Construct the quotient elliptic curve and quotient isogeny for a finite subgroup
  scheme.
* `definition` (`proposed`): `EllipticCurve.Isogeny.dual`
  Construct the dual isogeny and prove both composites are multiplication by the
  degree.
* `definition` (`proposed`): `EllipticCurve.weilPairing`
  Define the Weil pairing on multiplication kernels with functoriality and
  nondegeneracy.
:::
