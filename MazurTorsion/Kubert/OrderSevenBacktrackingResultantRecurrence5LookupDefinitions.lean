/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5

/-!
# Recurrence 5 lookup certificate: named intermediate consumers

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
@[expose] public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence5LeadingSquare : Coefficient :=
  remainder6Coefficient2 * remainder6Coefficient2

/-- Internal datum. -/ def recurrence5B2A2 : Coefficient :=
  remainder6Coefficient2 * remainder5Coefficient2

/-- Internal datum. -/ def recurrence5B1A3 : Coefficient :=
  remainder6Coefficient1 * remainder5Coefficient3

/-- Internal datum. -/ def recurrence5QuotientConstant : Coefficient :=
  recurrence5B2A2 - recurrence5B1A3

/-- Internal datum. -/ def recurrence5A3Square : Coefficient :=
  remainder5Coefficient3 * remainder5Coefficient3

/-- Internal datum. -/ def recurrence5ExceptionalProduct : Coefficient :=
  recurrence5A3Square * exceptional5

/-- Internal datum. -/ def recurrence5B2A3 : Coefficient :=
  remainder6Coefficient2 * remainder5Coefficient3

/-- Internal datum. -/ def recurrence5Scalar0Left : Coefficient :=
  recurrence5LeadingSquare * remainder5Coefficient0

/-- Internal datum. -/ def recurrence5Scalar0Main : Coefficient :=
  remainder6Coefficient0 * recurrence5QuotientConstant

/-- Internal datum. -/ def recurrence5Scalar0Exceptional : Coefficient :=
  recurrence5ExceptionalProduct * remainder7Coefficient0

/-- Internal datum. -/ def recurrence5Scalar1Left : Coefficient :=
  recurrence5LeadingSquare * remainder5Coefficient1

/-- Internal datum. -/ def recurrence5Scalar1First : Coefficient :=
  remainder6Coefficient0 * recurrence5B2A3

/-- Internal datum. -/ def recurrence5Scalar1Second : Coefficient :=
  remainder6Coefficient1 * recurrence5QuotientConstant

/-- Internal datum. -/ def recurrence5Scalar1Exceptional : Coefficient :=
  recurrence5ExceptionalProduct * remainder7Coefficient1

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
