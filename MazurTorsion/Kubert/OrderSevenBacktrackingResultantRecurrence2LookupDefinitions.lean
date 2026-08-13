/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2

/-!
# Recurrence 2 lookup certificate: named intermediate consumers

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
@[expose] public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

/-- Internal datum. -/ def recurrence2LeadingSquare : Coefficient :=
  remainder3Coefficient5 * remainder3Coefficient5

/-- Internal datum. -/ def recurrence2B5A5 : Coefficient :=
  remainder3Coefficient5 * remainder2Coefficient5

/-- Internal datum. -/ def recurrence2B4A6 : Coefficient :=
  remainder3Coefficient4 * remainder2Coefficient6

/-- Internal datum. -/ def recurrence2QuotientConstant : Coefficient :=
  recurrence2B5A5 - recurrence2B4A6

/-- Internal datum. -/ def recurrence2A6Square : Coefficient :=
  remainder2Coefficient6 * remainder2Coefficient6

/-- Internal datum. -/ def recurrence2ExceptionalProduct : Coefficient :=
  recurrence2A6Square * exceptional2

/-- Internal datum. -/ def recurrence2B5A6 : Coefficient :=
  remainder3Coefficient5 * remainder2Coefficient6

/-- Internal datum. -/ def recurrence2Scalar0Left : Coefficient :=
  recurrence2LeadingSquare * remainder2Coefficient0

/-- Internal datum. -/ def recurrence2Scalar0Main : Coefficient :=
  remainder3Coefficient0 * recurrence2QuotientConstant

/-- Internal datum. -/ def recurrence2Scalar0Exceptional : Coefficient :=
  recurrence2ExceptionalProduct * remainder4Coefficient0

/-- Internal datum. -/ def recurrence2Scalar1Left : Coefficient :=
  recurrence2LeadingSquare * remainder2Coefficient1

/-- Internal datum. -/ def recurrence2Scalar1Main : Coefficient :=
  remainder3Coefficient1 * recurrence2QuotientConstant

/-- Internal datum. -/ def recurrence2Scalar1Shift : Coefficient :=
  remainder3Coefficient0 * recurrence2B5A6

/-- Internal datum. -/ def recurrence2Scalar1Exceptional : Coefficient :=
  recurrence2ExceptionalProduct * remainder4Coefficient1

/-- Internal datum. -/ def recurrence2Scalar2Left : Coefficient :=
  recurrence2LeadingSquare * remainder2Coefficient2

/-- Internal datum. -/ def recurrence2Scalar2Main : Coefficient :=
  remainder3Coefficient2 * recurrence2QuotientConstant

/-- Internal datum. -/ def recurrence2Scalar2Shift : Coefficient :=
  remainder3Coefficient1 * recurrence2B5A6

/-- Internal datum. -/ def recurrence2Scalar2Exceptional : Coefficient :=
  recurrence2ExceptionalProduct * remainder4Coefficient2

/-- Internal datum. -/ def recurrence2Scalar3Left : Coefficient :=
  recurrence2LeadingSquare * remainder2Coefficient3

/-- Internal datum. -/ def recurrence2Scalar3Main : Coefficient :=
  remainder3Coefficient3 * recurrence2QuotientConstant

/-- Internal datum. -/ def recurrence2Scalar3Shift : Coefficient :=
  remainder3Coefficient2 * recurrence2B5A6

/-- Internal datum. -/ def recurrence2Scalar3Exceptional : Coefficient :=
  recurrence2ExceptionalProduct * remainder4Coefficient3

/-- Internal datum. -/ def recurrence2Scalar4Left : Coefficient :=
  recurrence2LeadingSquare * remainder2Coefficient4

/-- Internal datum. -/ def recurrence2Scalar4Main : Coefficient :=
  remainder3Coefficient4 * recurrence2QuotientConstant

/-- Internal datum. -/ def recurrence2Scalar4Shift : Coefficient :=
  remainder3Coefficient3 * recurrence2B5A6

/-- Internal datum. -/ def recurrence2Scalar4Exceptional : Coefficient :=
  recurrence2ExceptionalProduct * remainder4Coefficient4

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
