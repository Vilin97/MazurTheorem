/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5

/-!
# Step 6 data for the order-seven branch-zero resultant PRS

This serial data shard records one normalized primitive remainder and
exceptional content factor. Its linear pseudo-division quotient is
derived from leading coefficients and checked by the Lean recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section

def remainder8Coefficient0Chunk0 : Coefficient :=
  coefficientTerm 0
    (-((1 : ℚ)))

def remainder8Coefficient0Block0 : Coefficient :=
  remainder8Coefficient0Chunk0

def remainder8Coefficient0 : Coefficient :=
  remainder8Coefficient0Block0

def remainder8 : Bivariate :=
  outerTerm 0 remainder8Coefficient0

def quotient6 : Bivariate :=
  linearPseudoQuotient
    remainder6 remainder7
    2 1

def exceptionalUnit6 : Coefficient :=
  C
    (((((((26813799997641 : ℚ) * 10 ^ 36 +
      142369575613846289747847827330896388) * 10 ^ 36 +
      174087143449204393900331622823388931) * 10 ^ 36 +
      504208118624079313576123579518587434) * 10 ^ 36 +
      856069465570511249870923189965244671) * 10 ^ 36 +
      650107475862081909428552923558342334) * 10 ^ 36 +
      248809782697354987477701994402490000)

def exceptional6 : Coefficient :=
  exceptionalUnit6 *
  (parameter - 1) ^ 1 *
  (discriminantFactor) ^ 6 *
  (cmTwelve) ^ 1

def recurrence6 : Prop :=
  C ((remainder7.coeff 1) ^ 2) *
      remainder6 =
    remainder7 * quotient6 +
      C ((remainder6.coeff 2) ^ 2 *
        exceptional6) * remainder8

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
