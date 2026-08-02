/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Challenge: the divisor-line-bundle dictionary on a smooth proper curve

This contract captures the remaining A3 existence and equivalence deliverable: a scheme-level
dictionary relating chosen invertible-sheaf representatives, the Picard group, and Weil divisor
classes. The affine tilde restriction isomorphism and global tilde invertibility are now proved
in checked code. A checked equivalence reduces existence of the dictionary to the full Picard
comparison together with a divisor-class/Picard equivalence; chosen line bundles and their
compatibilities are constructed from those data. The contract does not prescribe a canonical
affine-chart normalization. Tensor product is now proved to commute with arbitrary module
localization; constructing the corresponding strong-monoidal tilde isomorphism still requires
assembling the local fraction maps into a locally bijective presheaf morphism. The contract is
open and earns no Mazur completion credit.
-/

open AlgebraicGeometry
open MazurTorsion.AlgebraicGeometry

namespace MazurTheorem.Challenge

universe u

/-- Construct an exact divisor-line-bundle dictionary for the geometric order system on a
smooth proper curve. -/
theorem divisorLineBundleDictionary
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (S : TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ))
    (hord : S.ord = TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt) :
    Nonempty (MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary S X) := sorry

/-- The two irreducible global outputs extracted from the dictionary contract. Checked code
proves conversely that these data construct all chosen divisor line bundles and dictionary
compatibilities. -/
theorem divisorPicardCoreData
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (S : TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ))
    (hord : S.ord = TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt) :
    PicardComparison X ∧ Nonempty (DivisorPicard.ClassEquivalence S X) := by
  apply DivisorPicard.Dictionary.nonempty_iff_picardComparison_and_classEquivalence.mp
  exact divisorLineBundleDictionary K X π S hord

/-- The divisor-class/Picard equivalence extracted from the exact dictionary. This is an
acceptance consumer for `divisorLineBundleDictionary`. -/
noncomputable def divisorClassEquivPicard
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (π : X ⟶ Spec (.of K)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    (S : TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ))
    (hord : S.ord = TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt) :
    S.ClassGroup ≃+ MazurTorsion.AlgebraicGeometry.PicardGroup X :=
  (divisorPicardCoreData K X π S hord).2.some

end MazurTheorem.Challenge
