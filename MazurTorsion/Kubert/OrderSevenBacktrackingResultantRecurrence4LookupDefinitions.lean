/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4

/-!
# Recurrence 4 lookup certificate: named intermediate consumers

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence4LeadingSquare : Coefficient :=
  remainder5Coefficient3 * remainder5Coefficient3

def recurrence4B3A3 : Coefficient :=
  remainder5Coefficient3 * remainder4Coefficient3

def recurrence4B2A4 : Coefficient :=
  remainder5Coefficient2 * remainder4Coefficient4

def recurrence4QuotientConstant : Coefficient :=
  recurrence4B3A3 - recurrence4B2A4

def recurrence4A4Square : Coefficient :=
  remainder4Coefficient4 * remainder4Coefficient4

def recurrence4ExceptionalProduct : Coefficient :=
  recurrence4A4Square * exceptional4

def recurrence4B3A4 : Coefficient :=
  remainder5Coefficient3 * remainder4Coefficient4

def recurrence4Scalar0Left : Coefficient :=
  recurrence4LeadingSquare * remainder4Coefficient0

def recurrence4Scalar0Main : Coefficient :=
  remainder5Coefficient0 * recurrence4QuotientConstant

def recurrence4Scalar0Exceptional : Coefficient :=
  recurrence4ExceptionalProduct * remainder6Coefficient0

def recurrence4Scalar1Left : Coefficient :=
  recurrence4LeadingSquare * remainder4Coefficient1

def recurrence4Scalar1First : Coefficient :=
  remainder5Coefficient0 * recurrence4B3A4

def recurrence4Scalar1Second : Coefficient :=
  remainder5Coefficient1 * recurrence4QuotientConstant

def recurrence4Scalar1Exceptional : Coefficient :=
  recurrence4ExceptionalProduct * remainder6Coefficient1

def recurrence4Scalar2Left : Coefficient :=
  recurrence4LeadingSquare * remainder4Coefficient2

def recurrence4Scalar2First : Coefficient :=
  remainder5Coefficient1 * recurrence4B3A4

def recurrence4Scalar2Second : Coefficient :=
  remainder5Coefficient2 * recurrence4QuotientConstant

def recurrence4Scalar2Exceptional : Coefficient :=
  recurrence4ExceptionalProduct * remainder6Coefficient2

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
