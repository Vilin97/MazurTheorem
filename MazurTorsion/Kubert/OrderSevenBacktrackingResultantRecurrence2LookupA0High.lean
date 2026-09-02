/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A0 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A0_coeff_60 :
    remainder2Coefficient0.coeff 60 =
      (621725971190563657393235315757192056596706225030493894 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_61 :
    remainder2Coefficient0.coeff 61 =
      (3459292504659497610979380743349758433450163007452524369 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_62 :
    remainder2Coefficient0.coeff 62 =
      (-11110284307128431035158933978291100334801954980947472146 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_63 :
    remainder2Coefficient0.coeff 63 =
      (18090386868971818456858662029614161681345717082226652170 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_64 :
    remainder2Coefficient0.coeff 64 =
      (-15778242959145104133485300167950379020342628991290237379 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_65 :
    remainder2Coefficient0.coeff 65 =
      (-3178960320396938136119349815210378601274709185668604937 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_66 :
    remainder2Coefficient0.coeff 66 =
      (36416415138398479956000701682694083607585734323956960547 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_67 :
    remainder2Coefficient0.coeff 67 =
      (-68730293687975869875107587708993249866577186534605683258 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_68 :
    remainder2Coefficient0.coeff 68 =
      (80288771384155327696477068622320292133380775283507804161 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_69 :
    remainder2Coefficient0.coeff 69 =
      (-61687727358641659015289991008485945807169000866643639069 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_70 :
    remainder2Coefficient0.coeff 70 =
      (22622649723594544532826141549412266534983169558561402188 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_71 :
    remainder2Coefficient0.coeff 71 =
      (14915691153763092973853852477020507767130725417493824916 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_72 :
    remainder2Coefficient0.coeff 72 =
      (-33394678553273738523894447672201797175806248079960824229 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_73 :
    remainder2Coefficient0.coeff 73 =
      (31217689682422219822285482974369168030034942981141275460 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_74 :
    remainder2Coefficient0.coeff 74 =
      (-19675967917793710704235343250800850601613615115738019326 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_75 :
    remainder2Coefficient0.coeff 75 =
      (10745817826620269598676200057421220998636038861351205476 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_76 :
    remainder2Coefficient0.coeff 76 =
      (-8281322558401235238033851106880737444484475822509353739 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_77 :
    remainder2Coefficient0.coeff 77 =
      (8874202635339496410647718336739457874613827537931241641 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_78 :
    remainder2Coefficient0.coeff 78 =
      (-8171004906960062150958281833795327043585118995535503793 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_79 :
    remainder2Coefficient0.coeff 79 =
      (5142430892918680930903256032716510315963633132641078831 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_80 :
    remainder2Coefficient0.coeff 80 =
      (-1554480341109496625004429488308674062741406305645410850 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_81 :
    remainder2Coefficient0.coeff 81 =
      (-736087488191373628403549815668351514898023125492160919 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_82 :
    remainder2Coefficient0.coeff 82 =
      (1332657498309766410093961889457493240678510755788979622 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_83 :
    remainder2Coefficient0.coeff 83 =
      (-950964642855568595917937148463566556455742041776139030 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_84 :
    remainder2Coefficient0.coeff 84 =
      (408293016549124941092699581346964679441895603795325958 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_85 :
    remainder2Coefficient0.coeff 85 =
      (-83054877363276582153572517801866795997624065665320178 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_86 :
    remainder2Coefficient0.coeff 86 =
      (-23045195150113390851533850503264632732698437216591192 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_87 :
    remainder2Coefficient0.coeff 87 =
      (27180003515099636736288757639539073556892684559618223 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_88 :
    remainder2Coefficient0.coeff 88 =
      (-11482509351260787881775076202547517529217615946686081 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_89 :
    remainder2Coefficient0.coeff 89 =
      (2403877461037195963346376424656155043888088425166875 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_90 :
    remainder2Coefficient0.coeff 90 =
      (85446096580397680979268746891364634839534831385470 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_91 :
    remainder2Coefficient0.coeff 91 =
      (-230300761212428877959999864514542636268972701952935 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_92 :
    remainder2Coefficient0.coeff 92 =
      (71047281503988594395292188314575685858281974979711 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_93 :
    remainder2Coefficient0.coeff 93 =
      (-7242965276005198687250854010145591748681377657456 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_94 :
    remainder2Coefficient0.coeff 94 =
      (-1609474925545182656633135617398099675121374668988 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_95 :
    remainder2Coefficient0.coeff 95 =
      (594888352697172539251946829237087330057928808919 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_96 :
    remainder2Coefficient0.coeff 96 =
      (-35682081868816433525662072854424923464803899505 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_97 :
    remainder2Coefficient0.coeff 97 =
      (-13080880038331164717498911381112159427479572402 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_98 :
    remainder2Coefficient0.coeff 98 =
      (1682596274192633024084773447547225160481835569 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_99 :
    remainder2Coefficient0.coeff 99 =
      (329041432510035751706973504730628132940569628 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_100 :
    remainder2Coefficient0.coeff 100 =
      (-59718794864614781855680443009507852961443027 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_101 :
    remainder2Coefficient0.coeff 101 =
      (-7173045799197579454731740761038147002347352 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_102 :
    remainder2Coefficient0.coeff 102 =
      (1560530508013868545100650132777578578566977 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_103 :
    remainder2Coefficient0.coeff 103 =
      (107596482591299095251211202323863114511740 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_104 :
    remainder2Coefficient0.coeff 104 =
      (-21835855329074871209439970786676218209063 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_105 :
    remainder2Coefficient0.coeff 105 =
      (-1613170450578754187113664875608047773491 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_106 :
    remainder2Coefficient0.coeff 106 =
      (121420420245797158958065078024853838771 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_107 :
    remainder2Coefficient0.coeff 107 =
      (17117395763730572988598898971842175952 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_108 :
    remainder2Coefficient0.coeff 108 =
      (744894209253773091908300182564263888 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_109 :
    remainder2Coefficient0.coeff 109 =
      (15560161622173073532254368820081712 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_110 :
    remainder2Coefficient0.coeff 110 =
      (165026199140154693898992949889670 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_111 :
    remainder2Coefficient0.coeff 111 =
      (843753345028747037362040919139 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_112 :
    remainder2Coefficient0.coeff 112 =
      (1577196414728952886234267757 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_113 :
    remainder2Coefficient0.coeff 113 =
      (-1507245375088838010731695 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_114 :
    remainder2Coefficient0.coeff 114 =
      (-7487522096003555795152 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_115 :
    remainder2Coefficient0.coeff 115 =
      (-5072148110737246025 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_116 :
    remainder2Coefficient0.coeff 116 =
      (-558110085407786 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_117 :
    remainder2Coefficient0.coeff 117 =
      (-3841078186 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A0_coeff_118 :
    remainder2Coefficient0.coeff 118 =
      (-57 : ℚ) := by
  unfold
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
