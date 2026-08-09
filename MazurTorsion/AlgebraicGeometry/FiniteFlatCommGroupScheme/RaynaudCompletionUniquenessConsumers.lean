/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AffineGenericFiberFaithfulness
import MazurTorsion.EllipticCurve.IntegerPrimeSpecialization

/-!
# Generic-fibre uniqueness over the five- and eleven-adic completions

At the integer primes above five and eleven, morphisms and isomorphisms between fixed affine
finite-flat commutative group schemes over the completed local ring are determined by their
generic fibres.  These are unconditional arithmetic specializations of generic-fibre
faithfulness: the fraction-field instances for the completed local rings provide the required
injectivity automatically.

The results are only uniqueness statements.  In particular, they neither extend a morphism from
the completion field nor assert a Raynaud classification of finite-flat models.
-/

noncomputable section

open CategoryTheory
open IsDedekindDomain HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

namespace AlgebraicGeometry.AffineFiniteFlatCommGroupScheme

/-- Morphisms of affine finite-flat group schemes over the five-adic completion integers are
determined by their generic fibres over the five-adic completion of `ℚ`. -/
theorem hom_ext_of_completionGenericFiberAtFive_eq
    {G H : AffineFiniteFlatCommGroupScheme (atFive.adicCompletionIntegers ℚ)}
    {f g : G ⟶ H}
    (hfg :
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map f =
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map g) :
    f = g :=
  hom_ext_of_genericFiber_eq hfg

/-- Isomorphisms of affine finite-flat group schemes over the five-adic completion integers are
determined by their generic-fibre morphisms over the five-adic completion of `ℚ`. -/
theorem iso_ext_of_completionGenericFiberAtFive_hom_eq
    {G H : AffineFiniteFlatCommGroupScheme (atFive.adicCompletionIntegers ℚ)}
    (e e' : G ≅ H)
    (h :
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map e.hom =
      (baseChangeFunctor
        (R := atFive.adicCompletionIntegers ℚ)
        (K := atFive.adicCompletion ℚ)).map e'.hom) :
    e = e' :=
  iso_ext_of_genericFiber_hom_eq e e' h

/-- Morphisms of affine finite-flat group schemes over the eleven-adic completion integers are
determined by their generic fibres over the eleven-adic completion of `ℚ`. -/
theorem hom_ext_of_completionGenericFiberAtEleven_eq
    {G H : AffineFiniteFlatCommGroupScheme (atEleven.adicCompletionIntegers ℚ)}
    {f g : G ⟶ H}
    (hfg :
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map f =
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map g) :
    f = g :=
  hom_ext_of_genericFiber_eq hfg

/-- Isomorphisms of affine finite-flat group schemes over the eleven-adic completion integers are
determined by their generic-fibre morphisms over the eleven-adic completion of `ℚ`. -/
theorem iso_ext_of_completionGenericFiberAtEleven_hom_eq
    {G H : AffineFiniteFlatCommGroupScheme (atEleven.adicCompletionIntegers ℚ)}
    (e e' : G ≅ H)
    (h :
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map e.hom =
      (baseChangeFunctor
        (R := atEleven.adicCompletionIntegers ℚ)
        (K := atEleven.adicCompletion ℚ)).map e'.hom) :
    e = e' :=
  iso_ext_of_genericFiber_hom_eq e e' h

end AlgebraicGeometry.AffineFiniteFlatCommGroupScheme
