import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeCocycleDescent

open AlgebraicGeometry.CommGroupScheme.MultiplicativeCocycleDescent

#print axioms ComonadicRankOneDescent.descendedModule
#print axioms ComonadicRankOneDescent.baseChangeIso
#print axioms ComonadicRankOneDescent.descendedModuleLinearEquivBase
#print axioms MultiplicativeUnitCocycle.toCoalgebra
#print axioms MultiplicativeUnitCocycle.descendedModule
#print axioms MultiplicativeUnitCocycle.baseChangeIso
#print axioms MultiplicativeUnitCocycle.descendedModuleLinearEquivBase
#print axioms MultiplicativeUnitCocycle.primeAwayLinearEquivBase
#print axioms representedOverlapUnit_normalization
#print axioms representedOverlapUnit_pairTwelve
#print axioms representedOverlapUnit_pairTwentyThree
#print axioms representedOverlapUnit_pairThirteen
#print axioms RepresentedMultiplicativeOneCocycle.toMultiplicativeUnitCocycle
#print axioms RepresentedMultiplicativeOneCocycle.descendedModule
#print axioms RepresentedMultiplicativeOneCocycle.baseChangeIso
#print axioms RepresentedMultiplicativeOneCocycle.primeAwayLinearEquivBase

#check RepresentedMultiplicativeOneCocycle.toMultiplicativeUnitCocycle
#check RepresentedMultiplicativeOneCocycle.primeAwayLinearEquivBase

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

example : MultiplicativeUnitCocycle (A := A) (B := B) :=
  (1 : RepresentedMultiplicativeOneCocycle (A := A) (B := B)).toMultiplicativeUnitCocycle

example (ℓ : ℕ) (hℓ : ℓ.Prime)
    {B : Type} [CommRing B]
    [Algebra (Localization.Away (ℓ : ℤ)) B] [Nontrivial B]
    (hf : (algebraMap (Localization.Away (ℓ : ℤ)) B).FaithfullyFlat) :
    (1 : RepresentedMultiplicativeOneCocycle
      (A := Localization.Away (ℓ : ℤ)) (B := B)).descendedModule hf
        ≃ₗ[Localization.Away (ℓ : ℤ)] Localization.Away (ℓ : ℤ) :=
  RepresentedMultiplicativeOneCocycle.primeAwayLinearEquivBase ℓ hℓ 1 hf
