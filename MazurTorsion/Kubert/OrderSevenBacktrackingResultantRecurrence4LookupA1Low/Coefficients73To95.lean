/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A1 source coefficients, low half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A1_coeff_73 :
    remainder4Coefficient1.coeff 73 =
      -((673406662380562441615730444 * 10 ^ 70 +
        5650599672541830834807385947703248823246143331196618802803505502368546) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_74 :
    remainder4Coefficient1.coeff 74 =
      ((1474689695816068070169752835 * 10 ^ 70 +
        3137200631707956748052241466478415799451737103455948953483302972125776) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_75 :
    remainder4Coefficient1.coeff 75 =
      -((3116335736672213691230325280 * 10 ^ 70 +
        3538908418090275412786499396601039306993363165059220917471457421234405) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_76 :
    remainder4Coefficient1.coeff 76 =
      ((6356434037364467604513070668 * 10 ^ 70 +
        6824225731186468962565164485480569693331231251160254622666918536864800) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_77 :
    remainder4Coefficient1.coeff 77 =
      -((12517196451644997210490589661 * 10 ^ 70 +
        8952793572317513989497192809713253440284703671390066152637559923532985) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_78 :
    remainder4Coefficient1.coeff 78 =
      ((23802177535863872741551485090 * 10 ^ 70 +
        0292887210790698825334823730949289720404805058300699356312956639384317) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_79 :
    remainder4Coefficient1.coeff 79 =
      -((43714735914136138419305211733 * 10 ^ 70 +
        4788662897140316478402336430454409513983949137084300037063944551147298) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_80 :
    remainder4Coefficient1.coeff 80 =
      ((77556782190389065407585725964 * 10 ^ 70 +
        4929527469090857054185679096334035236775874461065468012444502764401853) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_81 :
    remainder4Coefficient1.coeff 81 =
      -((132943038148629912951468831578 * 10 ^ 70 +
        0152789368545902747493388273741052920547537094210665543074496889729088) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_82 :
    remainder4Coefficient1.coeff 82 =
      ((220207724890644743085359855389 * 10 ^ 70 +
        0114225462401913753593214322415907050455633764214377182684412614230752) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_83 :
    remainder4Coefficient1.coeff 83 =
      -((352518670128378308979139979447 * 10 ^ 70 +
        3234358749932651839835564180854538276137875438787011874149603030403537) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_84 :
    remainder4Coefficient1.coeff 84 =
      ((545469161476402307353104070230 * 10 ^ 70 +
        7656316847916493234860914112510162245447135758104736039368205730526987) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_85 :
    remainder4Coefficient1.coeff 85 =
      -((815919284864171231676430146758 * 10 ^ 70 +
        6974465266589872663432128449433840896684202728687529278870045599237988) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_86 :
    remainder4Coefficient1.coeff 86 =
      ((1179935232981088818057549535421 * 10 ^ 70 +
        8191550837717204166369509184452180437352878650046362069941822351364446) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_87 :
    remainder4Coefficient1.coeff 87 =
      -((1649844212643411643634331665034 * 10 ^ 70 +
        2857350982664367409294799767717257040382397524622402320096834649432197) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_88 :
    remainder4Coefficient1.coeff 88 =
      ((2230674435053702559040424812780 * 10 ^ 70 +
        7897881866369854183869091199971464307651807369111756289413874227776966) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_89 :
    remainder4Coefficient1.coeff 89 =
      -((2916537555750793141066193944546 * 10 ^ 70 +
        2312656643238168859178457645928940452388899103897512486821310163953291) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_90 :
    remainder4Coefficient1.coeff 90 =
      ((3687752601862470316747143276375 * 10 ^ 70 +
        5560008013785500787097519619926894089579994372133560093973497750182057) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_91 :
    remainder4Coefficient1.coeff 91 =
      -((4509606164795666378851292554584 * 10 ^ 70 +
        7092885709740495363050355230729174597368905770385258128005813899488456) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_92 :
    remainder4Coefficient1.coeff 92 =
      ((5333509602328363454579365935103 * 10 ^ 70 +
        5581515286902021828766395956721222300966167730267180761867430032672331) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_93 :
    remainder4Coefficient1.coeff 93 =
      -((6100921162395537341992001700498 * 10 ^ 70 +
        9634890789284671657517608093554963352535873853749814565156813007108409) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_94 :
    remainder4Coefficient1.coeff 94 =
      ((6749803593406874386655262991563 * 10 ^ 70 +
        9032723311724993287976959976215791065959150148108192669649856306506384) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_95 :
    remainder4Coefficient1.coeff 95 =
      -((7222725338548068760455368176789 * 10 ^ 70 +
        0608447778611744077227400614602145429245539912289115627539754637699390) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
