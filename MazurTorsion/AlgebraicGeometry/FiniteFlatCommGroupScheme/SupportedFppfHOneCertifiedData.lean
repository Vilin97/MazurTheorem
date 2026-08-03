/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ElementaryGlobalSections
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfHOneBridge

/-!
# Certified good-open `H¹` data for Mazur's bad-level factors

The supported represented-`H¹` bridge identifies each bad-level elementary model, after
restriction to `D(level)`, with its finite-flat ambient model.  This file is the numerical
downstream consumer required by the low-degree Euler package: a genuine
`FinitePGroup.CertifiedData` certificate for the ambient represented `H¹` transports to the
canonical base change of the bad-level model without replacing either carrier by an abstract
finite group.

No finiteness or cardinality calculation is manufactured here.  In particular, the two
arithmetic inputs—the constant-group calculation and the multiplicative Kummer calculation—
remain explicit arguments, and no global bad-fibre cohomological localization sequence is
asserted.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe v u

open CommGroupScheme
open FiniteFlatCommGroupScheme

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
variable {p : ℕ}

/-- A certified cardinality for the represented `H¹` of the ambient constant group on
`D(level)` gives the same certificate for Mazur's constant-flat model there.  This is stated in
the carrier-preserving form consumed by the checked low-degree Euler sequence. -/
noncomputable def constantFlatFppfHOneAwayCertifiedData
    (level : R)
    (D : FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen level).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.constantScheme R G).obj))) :
    FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen level).ι).mapCommGrp.obj
          (constantFlat R G level).obj)) :=
  D.congr (constantFlatFppfHOneAwayMulEquiv level).symm

@[simp]
theorem constantFlatFppfHOneAwayCertifiedData_length
    (level : R)
    (D : FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen level).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.constantScheme R G).obj))) :
    (constantFlatFppfHOneAwayCertifiedData level D).length = D.length :=
  rfl

/-- The transported constant-flat certificate exposes the exact cardinal equality expected by
the low-degree rank-zero estimate. -/
theorem constantFlatFppfHOneAway_natCard_eq_pow
    (level : R)
    (D : FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen level).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.constantScheme R G).obj))) :
    Nat.card
        (CommGroupScheme.FppfHOne.{v}
          ((Over.pullback (levelOpen level).ι).mapCommGrp.obj
            (constantFlat R G level).obj)) =
      p ^ D.length :=
  (constantFlatFppfHOneAwayCertifiedData level D).card_eq

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level p : ℕ} [NeZero coeffPrime]

/-- A certified cardinality for the represented `H¹` of `μ_p` on `D(level)` gives the same
certificate for Mazur's multiplicative-flat model there.  The actual multiplicative-flat datum
is retained, so this applies directly to the canonical Fermat specialization. -/
noncomputable def muFlatFppfHOneAwayCertifiedData
    (datum : MuFlatDatum coeffPrime level)
    (D : FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen (level : ℤ)).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj))) :
    FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen (level : ℤ)).ι).mapCommGrp.obj
          (muFlat coeffPrime level datum).obj)) :=
  D.congr (muFlatFppfHOneAwayMulEquiv datum).symm

@[simp]
theorem muFlatFppfHOneAwayCertifiedData_length
    (datum : MuFlatDatum coeffPrime level)
    (D : FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen (level : ℤ)).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj))) :
    (muFlatFppfHOneAwayCertifiedData datum D).length = D.length :=
  rfl

/-- The transported multiplicative-flat certificate exposes the exact cardinal equality expected
by the low-degree rank-zero estimate. -/
theorem muFlatFppfHOneAway_natCard_eq_pow
    (datum : MuFlatDatum coeffPrime level)
    (D : FinitePGroup.CertifiedData p
      (CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (levelOpen (level : ℤ)).ι).mapCommGrp.obj
          (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj))) :
    Nat.card
        (CommGroupScheme.FppfHOne.{v}
          ((Over.pullback (levelOpen (level : ℤ)).ι).mapCommGrp.obj
            (muFlat coeffPrime level datum).obj)) =
      p ^ D.length :=
  (muFlatFppfHOneAwayCertifiedData datum D).card_eq

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme
