import MazurTorsion.AlgebraicGeometry.PicardAbelJacobi
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.DegreeZero

open AlgebraicGeometry

namespace Audit

universe u

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open MazurTorsion.AlgebraicGeometry

theorem immutableChallengeAdapter
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] [SmoothOfRelativeDimension 1 pi]
    (S : WeilDivisor.OrderSystem
      (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt) :
    S.IsWeightedDegreeZero (fun x ↦ (pi.residueDegree x : ℤ)) := by
  exact SchemeWeilDivisor.isWeightedDegreeZero_of_ord_eq_orderAt pi S hord
    (SchemeWeilDivisor.divisorProductFormula K X pi)

noncomputable def picardAbelJacobiConsumer
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] [SmoothOfRelativeDimension 1 pi]
    (S : WeilDivisor.OrderSystem
      (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (e : DivisorPicard.ClassEquivalence S X)
    {x0 : CodimensionOnePoint X}
    (hx0 : (pi.residueDegree x0 : ℤ) = 1)
    (x : CodimensionOnePoint X) :
    PicardGroup.degreeZero S (fun z ↦ (pi.residueDegree z : ℤ))
      (immutableChallengeAdapter K X pi S hord) e :=
  PicardGroup.weightedAbelJacobiClass S
    (fun z ↦ (pi.residueDegree z : ℤ))
    (immutableChallengeAdapter K X pi S hord) e hx0 x

#print axioms immutableChallengeAdapter
#print axioms picardAbelJacobiConsumer

end Audit
