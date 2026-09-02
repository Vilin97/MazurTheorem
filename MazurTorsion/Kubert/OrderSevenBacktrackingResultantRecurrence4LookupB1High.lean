/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: B1 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B1_coeff_87 :
    remainder5Coefficient1.coeff 87 =
      ((42839007845953718425051554233140004 * 10 ^ 70 +
        4000891652161884007413133708700914307171062905947268861350381323239623) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_88 :
    remainder5Coefficient1.coeff 88 =
      -((26347348719335356743096958232304006 * 10 ^ 70 +
        9869795524663525862371823519130890024837033548112820730623474991281817) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_89 :
    remainder5Coefficient1.coeff 89 =
      ((13227925474849931328017757221163467 * 10 ^ 70 +
        7190070254520754692880872740709696400577048690749505892168630079768137) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_90 :
    remainder5Coefficient1.coeff 90 =
      -((3823748322791275440787283252596325 * 10 ^ 70 +
        7979961760357323486608416389551190343610287422461817167226895314288050) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_91 :
    remainder5Coefficient1.coeff 91 =
      -((2092651215307467090772540150205516 * 10 ^ 70 +
        8892593156431188083619327785300680224684410708916461220070762936449495) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_92 :
    remainder5Coefficient1.coeff 92 =
      ((5135895308140557995993057129313593 * 10 ^ 70 +
        1507885789132704296859638651751727764057958376934182959301738207606292) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_93 :
    remainder5Coefficient1.coeff 93 =
      -((6096264634356419999647266276946530 * 10 ^ 70 +
        6229215988842645300595735255867518084478704812447465122128823954726072) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_94 :
    remainder5Coefficient1.coeff 94 =
      ((5755607067977522609506785525060425 * 10 ^ 70 +
        2121506588875691747206523055248598001725590616376615038355876443731821) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_95 :
    remainder5Coefficient1.coeff 95 =
      -((4763839522346748729584724997726222 * 10 ^ 70 +
        0199866860377249128900360922029005365527357536009728237730994344313097) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_96 :
    remainder5Coefficient1.coeff 96 =
      ((3583773497537844040893065686315608 * 10 ^ 70 +
        5579588631567809015649436123228056726199833970661846461852670010375388) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_97 :
    remainder5Coefficient1.coeff 97 =
      -((2492323182975411566005296195368831 * 10 ^ 70 +
        1420018716281245364538196866961519802276404100023958965606439339223176) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_98 :
    remainder5Coefficient1.coeff 98 =
      ((1616470289857352286345873429262351 * 10 ^ 70 +
        9579240606309515110024491589865290828602661540989619202886138797935750) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_99 :
    remainder5Coefficient1.coeff 99 =
      -((982137816105600940577965581201774 * 10 ^ 70 +
        5461875218876559758948240211283272433453443152895014547564702118817621) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_100 :
    remainder5Coefficient1.coeff 100 =
      ((559911461864409683996212115592349 * 10 ^ 70 +
        6933220615768728573297656255082509305515444525714923599754373086420728) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_101 :
    remainder5Coefficient1.coeff 101 =
      -((299248139198978770193567265404244 * 10 ^ 70 +
        3081503527308789979863092008930769219288691177282747295711060058763041) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_102 :
    remainder5Coefficient1.coeff 102 =
      ((149368682576888996996090723466455 * 10 ^ 70 +
        9913076209647682289119340331428889256969357740379501061398412854150419) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_103 :
    remainder5Coefficient1.coeff 103 =
      -((69053028406976709362983128195956 * 10 ^ 70 +
        9625253075786037046722724948486593598297961709987341217107597165473120) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_104 :
    remainder5Coefficient1.coeff 104 =
      ((29064985992321243181066303456755 * 10 ^ 70 +
        3328209709502324780490103615199190206772255660935836379976624453765427) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_105 :
    remainder5Coefficient1.coeff 105 =
      -((10720482581971926612840807569943 * 10 ^ 70 +
        0616176840152778606366033588873468334445065440880249438075178100829597) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_106 :
    remainder5Coefficient1.coeff 106 =
      ((3108384093738435260595649241869 * 10 ^ 70 +
        5077943994043250896964493536951672666158510958897530500818647634446188) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_107 :
    remainder5Coefficient1.coeff 107 =
      -((372893031342273612518010815822 * 10 ^ 70 +
        5334407526052332657147930456916933080914732176821530147827505098205331) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_108 :
    remainder5Coefficient1.coeff 108 =
      -((372481948314550209092489907465 * 10 ^ 70 +
        2058606192905109909625777717955985958668657814228882955069959899669759) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_109 :
    remainder5Coefficient1.coeff 109 =
      ((424034552492407705907495462384 * 10 ^ 70 +
        8449840890526830234049260027188414350340163246907653914240479487062204) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_110 :
    remainder5Coefficient1.coeff 110 =
      -((300628886481166292197737980717 * 10 ^ 70 +
        1151672790811578063992275833255836566334766347612942049549288340423104) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_111 :
    remainder5Coefficient1.coeff 111 =
      ((176887319085179249032655390930 * 10 ^ 70 +
        4857728604099297447982982458672091971526907220536566921307797967872452) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_112 :
    remainder5Coefficient1.coeff 112 =
      -((92682059645979436696142953133 * 10 ^ 70 +
        5018273547232135877015342253760284185588034464598054779045100382091035) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_113 :
    remainder5Coefficient1.coeff 113 =
      ((44361348695037996783886329090 * 10 ^ 70 +
        2878849587599526799643497423600022286193853325937221511086246490908225) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_114 :
    remainder5Coefficient1.coeff 114 =
      -((19564852870708177009107801236 * 10 ^ 70 +
        8484741819857120111796040381550527504295834048030077934862095625330347) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_115 :
    remainder5Coefficient1.coeff 115 =
      ((7943531233637823869061583606 * 10 ^ 70 +
        3044784763851632000944032892636905445624752885351929616236763685876759) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_116 :
    remainder5Coefficient1.coeff 116 =
      -((2940866841856704166266224455 * 10 ^ 70 +
        6929597112196412182312141540922827829629335165595163427799598090404702) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_117 :
    remainder5Coefficient1.coeff 117 =
      ((970873444813667815780152148 * 10 ^ 70 +
        2827212312820593873810838829419242938494066502735250124213456086392838) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_118 :
    remainder5Coefficient1.coeff 118 =
      -((271388137560775949620265149 * 10 ^ 70 +
        0015156899234081557564590240210104656211478606552421631888451560768802) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_119 :
    remainder5Coefficient1.coeff 119 =
      ((54675883029817776384557955 * 10 ^ 70 +
        6296589481409596988099099684772901724688806829636564863558226957973504) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_120 :
    remainder5Coefficient1.coeff 120 =
      -((821357840003261720866526 * 10 ^ 70 +
        3753831835815979129825456126977310019446997306194193259632685952841573) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_121 :
    remainder5Coefficient1.coeff 121 =
      -((6654058423898957783751707 * 10 ^ 70 +
        3810895534386276741438208000255510205000868417604672093008592107405963) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_122 :
    remainder5Coefficient1.coeff 122 =
      ((4565380707861872267949858 * 10 ^ 70 +
        9196995840994583967359069059180531522457731903189871498630999587188470) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_123 :
    remainder5Coefficient1.coeff 123 =
      -((2211919528947627747551324 * 10 ^ 70 +
        3725816622739297367205701956812738517102959793295946238884436997203660) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_124 :
    remainder5Coefficient1.coeff 124 =
      ((920866695799986620069206 * 10 ^ 70 +
        8122133255521843397458969565549416620699218667403610189494287379704353) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_125 :
    remainder5Coefficient1.coeff 125 =
      -((356888769656560599503190 * 10 ^ 70 +
        2445673700390938049684495047330244354532569450990283148506298340904139) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_126 :
    remainder5Coefficient1.coeff 126 =
      ((135328515465305404844059 * 10 ^ 70 +
        7169538683533538952863890350505341095442444311893217858940083600115356) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_127 :
    remainder5Coefficient1.coeff 127 =
      -((51105436436530587327124 * 10 ^ 70 +
        4970201429772845504886653883609991515033812962224022733029180620542280) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_128 :
    remainder5Coefficient1.coeff 128 =
      ((18724522924764368019831 * 10 ^ 70 +
        1861291247175064706077620950639205990935729075217609689616901392987641) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_129 :
    remainder5Coefficient1.coeff 129 =
      -((6216603415618809070554 * 10 ^ 70 +
        9490777440719767998140419079678390027566678235152851737418010751752813) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_130 :
    remainder5Coefficient1.coeff 130 =
      ((1647619764840444874522 * 10 ^ 70 +
        8931028135508640422119462195451291482765769639528814374066385531337289) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_131 :
    remainder5Coefficient1.coeff 131 =
      -((223057891902494616899 * 10 ^ 70 +
        4844119841455309114286528009536039107603706425377492925866115857178094) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_132 :
    remainder5Coefficient1.coeff 132 =
      -((82678103487240988285 * 10 ^ 70 +
        0425215879500558015990202775431304684914566134154706726255550900741895) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_133 :
    remainder5Coefficient1.coeff 133 =
      ((79338898000673021292 * 10 ^ 70 +
        6007436398625790081814026989282072660549464867251585149272902786851301) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_134 :
    remainder5Coefficient1.coeff 134 =
      -((35735303254734803292 * 10 ^ 70 +
        5678085571914256210574942272807176777242788823855151899829506921487155) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_135 :
    remainder5Coefficient1.coeff 135 =
      ((10524624162576581317 * 10 ^ 70 +
        8363821263024617882960977132697141843836451375973542887212021311698958) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_136 :
    remainder5Coefficient1.coeff 136 =
      -((1706981875558846956 * 10 ^ 70 +
        8109700613910549206269329367717555337269819206360089497554834846500269) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_137 :
    remainder5Coefficient1.coeff 137 =
      -((141214937184320669 * 10 ^ 70 +
        1704752716359652143431188249428619966907401447423958383282514469429899) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_138 :
    remainder5Coefficient1.coeff 138 =
      ((172008813180505805 * 10 ^ 70 +
        6926942797246013510239280722728189394486598332099139845353927822301830) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_139 :
    remainder5Coefficient1.coeff 139 =
      -((31456977061084661 * 10 ^ 70 +
        3577681356811676193722656661063374646887680269900933350978982922260017) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_140 :
    remainder5Coefficient1.coeff 140 =
      -((17836168224905651 * 10 ^ 70 +
        0256538288433172620311208747558241046427208352880575704020714225865698) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_141 :
    remainder5Coefficient1.coeff 141 =
      ((17590538337641690 * 10 ^ 70 +
        6878421933606487646987908208739914473620068254347964314449417879038479) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_142 :
    remainder5Coefficient1.coeff 142 =
      -((8904793049613992 * 10 ^ 70 +
        5942229548663423304273769086715329922891628565443715506239308695401982) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_143 :
    remainder5Coefficient1.coeff 143 =
      ((3426194784195303 * 10 ^ 70 +
        0132783883263089412079667430183689591252370068022080453442023744099401) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_144 :
    remainder5Coefficient1.coeff 144 =
      -((1114605734660233 * 10 ^ 70 +
        7932946423651466465950289554745322695521047064667561872726714668697676) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_145 :
    remainder5Coefficient1.coeff 145 =
      ((320358833283393 * 10 ^ 70 +
        2136125227567575460269316171621932024069857163167682690802930185775755) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_146 :
    remainder5Coefficient1.coeff 146 =
      -((82086180396764 * 10 ^ 70 +
        8993578323488848430623627419661028981808713280898219819864039351411744) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_147 :
    remainder5Coefficient1.coeff 147 =
      ((18402426013506 * 10 ^ 70 +
        9036654175884344631353369053144373052319448979270525673104783998609611) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_148 :
    remainder5Coefficient1.coeff 148 =
      -((3455579783778 * 10 ^ 70 +
        6644339617277587886239089348584610252259148324937535206582921634787906) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_149 :
    remainder5Coefficient1.coeff 149 =
      ((499739527343 * 10 ^ 70 +
        3289175931372346322438317158013085196164910164030010086405408888087190) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_150 :
    remainder5Coefficient1.coeff 150 =
      -((43325449024 * 10 ^ 70 +
        1461793963560044500634737587992254263498987197557460266765459139968846) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_151 :
    remainder5Coefficient1.coeff 151 =
      -((1737443471 * 10 ^ 70 +
        6553617271990044249606160487901360117923157818324213698182219658746789) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_152 :
    remainder5Coefficient1.coeff 152 =
      ((1437919785 * 10 ^ 70 +
        8271253558070668762929755683357335944481885148643634006405012288146369) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_153 :
    remainder5Coefficient1.coeff 153 =
      -((278191423 * 10 ^ 70 +
        3791984630331748072416157530893765507759472931848760588294940174807181) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_154 :
    remainder5Coefficient1.coeff 154 =
      ((28468552 * 10 ^ 70 +
        0476186376648561314130211292983830267522805773582305285357374920960672) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_155 :
    remainder5Coefficient1.coeff 155 =
      -((485094 * 10 ^ 70 +
        1269474103411838445771996007883105807322425776374788640735334272347304) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_156 :
    remainder5Coefficient1.coeff 156 =
      -((359166 * 10 ^ 70 +
        7300519127655402501758383911121049453839011447209853632586129035250260) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_157 :
    remainder5Coefficient1.coeff 157 =
      ((65727 * 10 ^ 70 +
        8211462078610627065347187724276408368593159301963314587539767947042018) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_158 :
    remainder5Coefficient1.coeff 158 =
      -((6143 * 10 ^ 70 +
        0263223075940519293889782831041249055642184364914070608368586021888868) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_159 :
    remainder5Coefficient1.coeff 159 =
      ((326 * 10 ^ 70 +
        7261716847778926231991659695017613502367898343260089978526901646483867) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_160 :
    remainder5Coefficient1.coeff 160 =
      -((8 * 10 ^ 70 +
        5747868943945826915372523681170973081191518009064376643969509715898455) : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_161 :
    remainder5Coefficient1.coeff 161 =
      (619785625014372052648882749922458291617368129731485676449528146389072 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_162 :
    remainder5Coefficient1.coeff 162 =
      (3147260282602372168102515351903578452751791286206699836852692191260 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_163 :
    remainder5Coefficient1.coeff 163 =
      (-24767509396697137867220169832073751654442983999545131868185853598 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_164 :
    remainder5Coefficient1.coeff 164 =
      (-13677059129789495345638018514424249736353267306432162990858049 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_165 :
    remainder5Coefficient1.coeff 165 =
      (213507850295400383688227399543110435103192017123040434305686 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_166 :
    remainder5Coefficient1.coeff 166 =
      (-299584627052588805575145885832374709254270483914108571974 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_167 :
    remainder5Coefficient1.coeff 167 =
      (120093051196868283782346331419687858723446830934786213 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_168 :
    remainder5Coefficient1.coeff 168 =
      (-12696495038384809863515558313789423382498064285533 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_169 :
    remainder5Coefficient1.coeff 169 =
      (288064487042104605586738245232158273778979161 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_170 :
    remainder5Coefficient1.coeff 170 =
      (-1008955353374942246866447112470457874528 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_171 :
    remainder5Coefficient1.coeff 171 =
      (314411069059314601433269245417210 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B1_coeff_172 :
    remainder5Coefficient1.coeff 172 =
      (-3059748947618181153106641 : ℚ) := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
    remainder5Coefficient1Chunk21
    remainder5Coefficient1Chunk20
    remainder5Coefficient1Chunk19
    remainder5Coefficient1Chunk18
    remainder5Coefficient1Chunk17
    remainder5Coefficient1Chunk16
    remainder5Coefficient1Chunk15
    remainder5Coefficient1Chunk14
    remainder5Coefficient1Chunk13
    remainder5Coefficient1Chunk12
    remainder5Coefficient1Chunk11
    remainder5Coefficient1Chunk10
    remainder5Coefficient1Chunk9
    remainder5Coefficient1Chunk8
    remainder5Coefficient1Chunk7
    remainder5Coefficient1Chunk6
    remainder5Coefficient1Chunk5
    remainder5Coefficient1Chunk4
    remainder5Coefficient1Chunk3
    remainder5Coefficient1Chunk2
    remainder5Coefficient1Chunk1
    remainder5Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
