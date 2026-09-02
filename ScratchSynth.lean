import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat

open AlgebraicGeometry

#synth IsZariskiLocalAtSource (@Flat)
#synth IsZariskiLocalAtSource (@LocallyOfFinitePresentation)
#synth IsZariskiLocalAtSource (@Flat ⊓ @LocallyOfFinitePresentation)
#synth HasRingHomProperty (@Flat) RingHom.Flat
#synth HasRingHomProperty (@LocallyOfFinitePresentation) RingHom.FinitePresentation
#check HasRingHomProperty.instIsZariskiLocalAtSource
#check CategoryTheory.MorphismProperty.IsLocalAtSource.inf
#synth CategoryTheory.MorphismProperty.RespectsIso (@Flat)
#synth CategoryTheory.MorphismProperty.RespectsIso (@LocallyOfFinitePresentation)
#synth CategoryTheory.MorphismProperty.ContainsIdentities (@Flat)
#synth CategoryTheory.MorphismProperty.ContainsIdentities (@LocallyOfFinitePresentation)
#check RingHom.FinitePresentation.id
#check HasRingHomProperty.containsIdentities
#check CategoryTheory.MorphismProperty.ContainsIdentities.inf
#check AlgebraicGeometry.sigmaSpec
#check AlgebraicGeometry.instIsIsoSchemeSigmaSpecOfFinite
#print CategoryTheory.MorphismProperty.IsLocalAtSource
#check AlgebraicGeometry.affineLocally_respectsIso
#synth CategoryTheory.Precoverage.IsStableUnderBaseChange AlgebraicGeometry.Scheme.fppfPrecoverage
#check CategoryTheory.Precoverage.instRespectsIsoOfIsStableUnderBaseChange
