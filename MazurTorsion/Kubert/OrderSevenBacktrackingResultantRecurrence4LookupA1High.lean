/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A1 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A1_coeff_96 :
    remainder4Coefficient1.coeff 96 =
      ((7475177460798968777583282313269 * 10 ^ 70 +
        8066718384764117436995108586200250777778185745543772160125771622169361) : ℚ) := by
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

theorem recurrence4A1_coeff_97 :
    remainder4Coefficient1.coeff 97 =
      -((7482451797703971722366361355000 * 10 ^ 70 +
        5270950568146464834893398230570805357347094986005454742401472601980335) : ℚ) := by
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

theorem recurrence4A1_coeff_98 :
    remainder4Coefficient1.coeff 98 =
      ((7243614148603187414932177774770 * 10 ^ 70 +
        3511422848650818334217699093914898487931426192418271730445719627103285) : ℚ) := by
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

theorem recurrence4A1_coeff_99 :
    remainder4Coefficient1.coeff 99 =
      -((6781690581702507758067397737376 * 10 ^ 70 +
        4734538555728387632604968013737638873832540799891614027876921972604357) : ℚ) := by
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

theorem recurrence4A1_coeff_100 :
    remainder4Coefficient1.coeff 100 =
      ((6140017427523117285803397662541 * 10 ^ 70 +
        8448716634365636828083858587388839773345016179486663380073920719746749) : ℚ) := by
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

theorem recurrence4A1_coeff_101 :
    remainder4Coefficient1.coeff 101 =
      -((5375554210578042600925739350267 * 10 ^ 70 +
        9898302329500112196149001603079423243961347340468666007474433875768123) : ℚ) := by
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

theorem recurrence4A1_coeff_102 :
    remainder4Coefficient1.coeff 102 =
      ((4550585390331270997222547994034 * 10 ^ 70 +
        7099109700348463158141813057573975091384837127745680877471881247431711) : ℚ) := by
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

theorem recurrence4A1_coeff_103 :
    remainder4Coefficient1.coeff 103 =
      -((3724477496928350026231910909241 * 10 ^ 70 +
        0666312848718010993686080104049483661578954328757820846239994666186564) : ℚ) := by
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

theorem recurrence4A1_coeff_104 :
    remainder4Coefficient1.coeff 104 =
      ((2946975260902021780599264580861 * 10 ^ 70 +
        1078341050731413751121957123404828488189389253902530281997849497641148) : ℚ) := by
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

theorem recurrence4A1_coeff_105 :
    remainder4Coefficient1.coeff 105 =
      -((2254005457602165681829979393411 * 10 ^ 70 +
        3720179010930614624379613894284279184166161606979984431402882679108241) : ℚ) := by
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

theorem recurrence4A1_coeff_106 :
    remainder4Coefficient1.coeff 106 =
      ((1666289279034895075944571826565 * 10 ^ 70 +
        2819970357199525437735572315291797311266751764408473362168504863481880) : ℚ) := by
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

theorem recurrence4A1_coeff_107 :
    remainder4Coefficient1.coeff 107 =
      -((1190440923042996367756715697392 * 10 ^ 70 +
        0986070029279986604449811523739018628786974308457964549438364727944960) : ℚ) := by
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

theorem recurrence4A1_coeff_108 :
    remainder4Coefficient1.coeff 108 =
      ((821803419234149993591490999051 * 10 ^ 70 +
        0426746426653445035338274175813464482599086124019518304690865767842911) : ℚ) := by
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

theorem recurrence4A1_coeff_109 :
    remainder4Coefficient1.coeff 109 =
      -((548109351697741238166283084386 * 10 ^ 70 +
        9470647752374042594647276219032955259228712677159647942417641353568025) : ℚ) := by
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

theorem recurrence4A1_coeff_110 :
    remainder4Coefficient1.coeff 110 =
      ((353133203097499911730942991457 * 10 ^ 70 +
        4129773425014224605868514857643823042759024778782340646601505980952053) : ℚ) := by
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

theorem recurrence4A1_coeff_111 :
    remainder4Coefficient1.coeff 111 =
      -((219741463674264861095895267338 * 10 ^ 70 +
        1610206486011710546496615755547375075949559716134298998318744939351872) : ℚ) := by
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

theorem recurrence4A1_coeff_112 :
    remainder4Coefficient1.coeff 112 =
      ((132043159619196054915996181816 * 10 ^ 70 +
        4065850479252478099559657915467719041118028544752132163508886933676552) : ℚ) := by
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

theorem recurrence4A1_coeff_113 :
    remainder4Coefficient1.coeff 113 =
      -((76608756571631665694525888022 * 10 ^ 70 +
        2897239801711860293432438077723790361816585229100664145171205528497700) : ℚ) := by
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

theorem recurrence4A1_coeff_114 :
    remainder4Coefficient1.coeff 114 =
      ((42907145090774203459211081320 * 10 ^ 70 +
        9033435008776763749977098687326871981357776769175542755505404326475257) : ℚ) := by
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

theorem recurrence4A1_coeff_115 :
    remainder4Coefficient1.coeff 115 =
      -((23195510046346500749846600983 * 10 ^ 70 +
        9129085229474743802767995792118189104328418741467371543881209847745440) : ℚ) := by
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

theorem recurrence4A1_coeff_116 :
    remainder4Coefficient1.coeff 116 =
      ((12101586850188405689909264983 * 10 ^ 70 +
        3770074072198420270202571350979399552965201310838640764313338784743622) : ℚ) := by
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

theorem recurrence4A1_coeff_117 :
    remainder4Coefficient1.coeff 117 =
      -((6092470096139417495259241813 * 10 ^ 70 +
        2783672712156360001938658891334201444099069419098159487678889689955344) : ℚ) := by
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

theorem recurrence4A1_coeff_118 :
    remainder4Coefficient1.coeff 118 =
      ((2959449843423416825051695423 * 10 ^ 70 +
        8491588558504025273457401767263972416884924298417024656667405485064981) : ℚ) := by
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

theorem recurrence4A1_coeff_119 :
    remainder4Coefficient1.coeff 119 =
      -((1386897056881075844868201486 * 10 ^ 70 +
        3842343684781607512394527258519171523025860585277581178356722717009967) : ℚ) := by
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

theorem recurrence4A1_coeff_120 :
    remainder4Coefficient1.coeff 120 =
      ((626922430927956722151146983 * 10 ^ 70 +
        3113294234255109841984963546344708080215270685116192794622704739178119) : ℚ) := by
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

theorem recurrence4A1_coeff_121 :
    remainder4Coefficient1.coeff 121 =
      -((273252287319724008947825275 * 10 ^ 70 +
        4931060169052733837388067309950901633713623800736332773038631348386682) : ℚ) := by
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

theorem recurrence4A1_coeff_122 :
    remainder4Coefficient1.coeff 122 =
      ((114755749683313425480081954 * 10 ^ 70 +
        0088118055028321473487985309150451780724302785413977701856614315519369) : ℚ) := by
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

theorem recurrence4A1_coeff_123 :
    remainder4Coefficient1.coeff 123 =
      -((46367610398937840092910333 * 10 ^ 70 +
        6364047477904953416282745852485488582340262490334116521024041391105763) : ℚ) := by
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

theorem recurrence4A1_coeff_124 :
    remainder4Coefficient1.coeff 124 =
      ((17976433179167116345358965 * 10 ^ 70 +
        5037332022733662693544706142939885054935077266689038261012468015078775) : ℚ) := by
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

theorem recurrence4A1_coeff_125 :
    remainder4Coefficient1.coeff 125 =
      -((6654656968012661083360849 * 10 ^ 70 +
        8242358489154342840707285094501257495302513459696481323433816564720037) : ℚ) := by
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

theorem recurrence4A1_coeff_126 :
    remainder4Coefficient1.coeff 126 =
      ((2332292100441059445809149 * 10 ^ 70 +
        5003694967883150483004052753840545330304835945050858207941675078892431) : ℚ) := by
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

theorem recurrence4A1_coeff_127 :
    remainder4Coefficient1.coeff 127 =
      -((762355627509772260392545 * 10 ^ 70 +
        9129020044352695264971612417428595617076454378843220177976414898731665) : ℚ) := by
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

theorem recurrence4A1_coeff_128 :
    remainder4Coefficient1.coeff 128 =
      ((225971502744677180661085 * 10 ^ 70 +
        5525852260351888724534114013330585989177653772033832694350594392677069) : ℚ) := by
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

theorem recurrence4A1_coeff_129 :
    remainder4Coefficient1.coeff 129 =
      -((57137577110467956671822 * 10 ^ 70 +
        1248603944744907758820562756995981522247446060216254197850658579152982) : ℚ) := by
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

theorem recurrence4A1_coeff_130 :
    remainder4Coefficient1.coeff 130 =
      ((10193177452723550279055 * 10 ^ 70 +
        9045052741753946736055387301144344446581502262552308079366786876620792) : ℚ) := by
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

theorem recurrence4A1_coeff_131 :
    remainder4Coefficient1.coeff 131 =
      ((163717474058853935565 * 10 ^ 70 +
        2930890359741328010950289532536588709928185436563016394233749140495239) : ℚ) := by
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

theorem recurrence4A1_coeff_132 :
    remainder4Coefficient1.coeff 132 =
      -((1222419576429299706640 * 10 ^ 70 +
        3612371111511094629799379338206645615436927272493208661872931051962118) : ℚ) := by
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

theorem recurrence4A1_coeff_133 :
    remainder4Coefficient1.coeff 133 =
      ((676784738286958581649 * 10 ^ 70 +
        2035317322802052752325313727035170951525340107950187505688299383718608) : ℚ) := by
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

theorem recurrence4A1_coeff_134 :
    remainder4Coefficient1.coeff 134 =
      -((228583884729503516716 * 10 ^ 70 +
        8551452840567247344059108348509846028997973496103964767947358443652028) : ℚ) := by
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

theorem recurrence4A1_coeff_135 :
    remainder4Coefficient1.coeff 135 =
      ((32772791354265001697 * 10 ^ 70 +
        8449572806391556799593543301072963707228764297186407603064753050221904) : ℚ) := by
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

theorem recurrence4A1_coeff_136 :
    remainder4Coefficient1.coeff 136 =
      ((21914082473784597656 * 10 ^ 70 +
        1004735794613487125993345078472062497958015992851956245846972403780009) : ℚ) := by
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

theorem recurrence4A1_coeff_137 :
    remainder4Coefficient1.coeff 137 =
      -((24356917850632510890 * 10 ^ 70 +
        8872980824934004892937432554154653036098288340067886403395805419004235) : ℚ) := by
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

theorem recurrence4A1_coeff_138 :
    remainder4Coefficient1.coeff 138 =
      ((15180916494215646783 * 10 ^ 70 +
        4674940901122527131805783850359230719647754674294673227354298758172644) : ℚ) := by
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

theorem recurrence4A1_coeff_139 :
    remainder4Coefficient1.coeff 139 =
      -((7354309902376419625 * 10 ^ 70 +
        6104538642216805174855224425481376040814389597686109518541596779949748) : ℚ) := by
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

theorem recurrence4A1_coeff_140 :
    remainder4Coefficient1.coeff 140 =
      ((2904802332343163224 * 10 ^ 70 +
        5724100789233402272077878879282076021101711907007051183280621146311499) : ℚ) := by
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

theorem recurrence4A1_coeff_141 :
    remainder4Coefficient1.coeff 141 =
      -((882049484753851365 * 10 ^ 70 +
        7771778701144288519400850385896283348493685271198884246794532396310447) : ℚ) := by
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

theorem recurrence4A1_coeff_142 :
    remainder4Coefficient1.coeff 142 =
      ((136202684006136914 * 10 ^ 70 +
        5950761817927908891475153236522072081752557034231226703980108451173122) : ℚ) := by
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

theorem recurrence4A1_coeff_143 :
    remainder4Coefficient1.coeff 143 =
      ((63833987296685336 * 10 ^ 70 +
        9927896457014352553163178843160351426361393905523467070925818387006941) : ℚ) := by
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

theorem recurrence4A1_coeff_144 :
    remainder4Coefficient1.coeff 144 =
      -((77706310746925818 * 10 ^ 70 +
        9403633184424262988037681780551087286842522895153329351979884176406813) : ℚ) := by
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

theorem recurrence4A1_coeff_145 :
    remainder4Coefficient1.coeff 145 =
      ((49827838581298692 * 10 ^ 70 +
        6820615413253005385631516989043117066448838542126675817693829149112231) : ℚ) := by
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

theorem recurrence4A1_coeff_146 :
    remainder4Coefficient1.coeff 146 =
      -((24999987339023179 * 10 ^ 70 +
        2423386418842515798974386550642008525120457015155510342182912110759533) : ℚ) := by
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

theorem recurrence4A1_coeff_147 :
    remainder4Coefficient1.coeff 147 =
      ((10637997518973879 * 10 ^ 70 +
        9544210930931038741759333294278856596471174565216928960131597073670883) : ℚ) := by
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

theorem recurrence4A1_coeff_148 :
    remainder4Coefficient1.coeff 148 =
      -((3930940963288629 * 10 ^ 70 +
        6315553273394981414344342170176498584790782399370749008786690806299115) : ℚ) := by
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

theorem recurrence4A1_coeff_149 :
    remainder4Coefficient1.coeff 149 =
      ((1262336562008912 * 10 ^ 70 +
        5683846670951538592040879112609354557220521235993047661661001967014925) : ℚ) := by
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

theorem recurrence4A1_coeff_150 :
    remainder4Coefficient1.coeff 150 =
      -((346002961033324 * 10 ^ 70 +
        9623280924069551168423292386399703000518454170479798932605259239853739) : ℚ) := by
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

theorem recurrence4A1_coeff_151 :
    remainder4Coefficient1.coeff 151 =
      ((76940976875028 * 10 ^ 70 +
        1250381447313599468863811659386560414723345165060194381638294428035178) : ℚ) := by
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

theorem recurrence4A1_coeff_152 :
    remainder4Coefficient1.coeff 152 =
      -((11798116595990 * 10 ^ 70 +
        1266487681441359892239350143809719252996705777684469693086800698811714) : ℚ) := by
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

theorem recurrence4A1_coeff_153 :
    remainder4Coefficient1.coeff 153 =
      ((134764028710 * 10 ^ 70 +
        3749399824005250007318494405695332273715697464435832669940297220384767) : ℚ) := by
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

theorem recurrence4A1_coeff_154 :
    remainder4Coefficient1.coeff 154 =
      ((702660606139 * 10 ^ 70 +
        8810161088365813323921298661676538910394339064465744026681226658424695) : ℚ) := by
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

theorem recurrence4A1_coeff_155 :
    remainder4Coefficient1.coeff 155 =
      -((302289043288 * 10 ^ 70 +
        9290464488781490312876576753564812781320527228443094476621409514519136) : ℚ) := by
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

theorem recurrence4A1_coeff_156 :
    remainder4Coefficient1.coeff 156 =
      ((81076818564 * 10 ^ 70 +
        4552835858960223320939486592500333487733099804370226498268268865857444) : ℚ) := by
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

theorem recurrence4A1_coeff_157 :
    remainder4Coefficient1.coeff 157 =
      -((15064863955 * 10 ^ 70 +
        3542516191515398184950568326064434999459840987436394851510740073126693) : ℚ) := by
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

theorem recurrence4A1_coeff_158 :
    remainder4Coefficient1.coeff 158 =
      ((1577033140 * 10 ^ 70 +
        3575342430895437961905750881845820513057422334386125077139738584521346) : ℚ) := by
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

theorem recurrence4A1_coeff_159 :
    remainder4Coefficient1.coeff 159 =
      ((103143849 * 10 ^ 70 +
        9419190608672874908783382977396589869424766742615775100022364462177475) : ℚ) := by
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

theorem recurrence4A1_coeff_160 :
    remainder4Coefficient1.coeff 160 =
      -((88848845 * 10 ^ 70 +
        3598737416694792367378225998460057463258942004187451125805195248369565) : ℚ) := by
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

theorem recurrence4A1_coeff_161 :
    remainder4Coefficient1.coeff 161 =
      ((21270475 * 10 ^ 70 +
        6537571917646621422696742507746692908399014372752078350832949817247759) : ℚ) := by
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

theorem recurrence4A1_coeff_162 :
    remainder4Coefficient1.coeff 162 =
      -((2804518 * 10 ^ 70 +
        3635839490541588126639601185006555879722503605206376046986677170440905) : ℚ) := by
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

theorem recurrence4A1_coeff_163 :
    remainder4Coefficient1.coeff 163 =
      ((90136 * 10 ^ 70 +
        2894240406696292517930480562922572098781818044089546111066844659963741) : ℚ) := by
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

theorem recurrence4A1_coeff_164 :
    remainder4Coefficient1.coeff 164 =
      ((48665 * 10 ^ 70 +
        4674396098259235177996779972908935063818266904937086611840757378704573) : ℚ) := by
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

theorem recurrence4A1_coeff_165 :
    remainder4Coefficient1.coeff 165 =
      -((11801 * 10 ^ 70 +
        4729953012360969545582488938406817229717684913149581805680487802635014) : ℚ) := by
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

theorem recurrence4A1_coeff_166 :
    remainder4Coefficient1.coeff 166 =
      ((1250 * 10 ^ 70 +
        7903442222304732803123971906028783063848574119434822864816834563953003) : ℚ) := by
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

theorem recurrence4A1_coeff_167 :
    remainder4Coefficient1.coeff 167 =
      -((14 * 10 ^ 70 +
        9989615836734697970532791043680633945266608971793423361466969110295794) : ℚ) := by
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

theorem recurrence4A1_coeff_168 :
    remainder4Coefficient1.coeff 168 =
      -((14 * 10 ^ 70 +
        8696398539325476469068356168921780691864510622423485343401920923605166) : ℚ) := by
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

theorem recurrence4A1_coeff_169 :
    remainder4Coefficient1.coeff 169 =
      ((2 * 10 ^ 70 +
        0237063316334925680608760927303605068267938560261997819558586394122914) : ℚ) := by
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

theorem recurrence4A1_coeff_170 :
    remainder4Coefficient1.coeff 170 =
      (-748371003927271741154170478339583777836960419996028824929270989581123 : ℚ) := by
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

theorem recurrence4A1_coeff_171 :
    remainder4Coefficient1.coeff 171 =
      (-85500969710033529515701255008079454173238356005406635218287093039812 : ℚ) := by
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

theorem recurrence4A1_coeff_172 :
    remainder4Coefficient1.coeff 172 =
      (9805356358872421213404169395195216896652001757665991741785888748610 : ℚ) := by
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

theorem recurrence4A1_coeff_173 :
    remainder4Coefficient1.coeff 173 =
      (-61345332488416245192841569760865389874036903242755294008937358735 : ℚ) := by
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

theorem recurrence4A1_coeff_174 :
    remainder4Coefficient1.coeff 174 =
      (-30602577928356269945403679237996685764814476605133233014722791183 : ℚ) := by
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

theorem recurrence4A1_coeff_175 :
    remainder4Coefficient1.coeff 175 =
      (323186898189767301851367256237775098177011900046387817145431534 : ℚ) := by
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

theorem recurrence4A1_coeff_176 :
    remainder4Coefficient1.coeff 176 =
      (57076164149317311983241554774282234744487139323987989294860309 : ℚ) := by
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

theorem recurrence4A1_coeff_177 :
    remainder4Coefficient1.coeff 177 =
      (1329663713510284822304878170309472305717733391736680340167785 : ℚ) := by
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

theorem recurrence4A1_coeff_178 :
    remainder4Coefficient1.coeff 178 =
      (13522759127750948405565665267486800697891120261481180520272 : ℚ) := by
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

theorem recurrence4A1_coeff_179 :
    remainder4Coefficient1.coeff 179 =
      (68440232685480362737473256330659552453146279574330053768 : ℚ) := by
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

theorem recurrence4A1_coeff_180 :
    remainder4Coefficient1.coeff 180 =
      (156301300456882419884388060396740496525691255162599401 : ℚ) := by
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

theorem recurrence4A1_coeff_181 :
    remainder4Coefficient1.coeff 181 =
      (20821378000265036417859664107395263307004515217945 : ℚ) := by
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

theorem recurrence4A1_coeff_182 :
    remainder4Coefficient1.coeff 182 =
      (-561782912259307626492836017518121175468993499202 : ℚ) := by
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

theorem recurrence4A1_coeff_183 :
    remainder4Coefficient1.coeff 183 =
      (-908825169258193200572233082016061743080333582 : ℚ) := by
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

theorem recurrence4A1_coeff_184 :
    remainder4Coefficient1.coeff 184 =
      (-492227487195799594960341191069630546220098 : ℚ) := by
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

theorem recurrence4A1_coeff_185 :
    remainder4Coefficient1.coeff 185 =
      (-90673694400791428354037928543020554710 : ℚ) := by
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

theorem recurrence4A1_coeff_186 :
    remainder4Coefficient1.coeff 186 =
      (-4894913024786264472437929522098555 : ℚ) := by
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

theorem recurrence4A1_coeff_187 :
    remainder4Coefficient1.coeff 187 =
      (-60464546983171638597828541088 : ℚ) := by
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

theorem recurrence4A1_coeff_188 :
    remainder4Coefficient1.coeff 188 =
      (-115387634732139429500246 : ℚ) := by
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

theorem recurrence4A1_coeff_189 :
    remainder4Coefficient1.coeff 189 =
      (-16865704796555725 : ℚ) := by
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

theorem recurrence4A1_coeff_190 :
    remainder4Coefficient1.coeff 190 =
      (-47165519 : ℚ) := by
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
