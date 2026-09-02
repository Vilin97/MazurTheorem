/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B5 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B5_coeff_68 :
    remainder3Coefficient5.coeff 68 =
      ((1573 * 10 ^ 70 +
        3700482159318132242512486410154453982346751587044020014681765236104936) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_69 :
    remainder3Coefficient5.coeff 69 =
      -((7704 * 10 ^ 70 +
        0918225517736074921729336195990513293135974166709962259944549347487984) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_70 :
    remainder3Coefficient5.coeff 70 =
      ((21548 * 10 ^ 70 +
        9784207940916533650299384876288246083729670829769966431539795282755301) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_71 :
    remainder3Coefficient5.coeff 71 =
      -((37778 * 10 ^ 70 +
        1753888803961828638061639688835594512078997877013100237833213875331715) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_72 :
    remainder3Coefficient5.coeff 72 =
      ((14469 * 10 ^ 70 +
        3952666072833585053620515821037495162493008316823504075366429204108104) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_73 :
    remainder3Coefficient5.coeff 73 =
      ((189550 * 10 ^ 70 +
        8554447424250237432462766301765926181207829128055282173822134556985390) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_74 :
    remainder3Coefficient5.coeff 74 =
      -((923653 * 10 ^ 70 +
        5594132348555596946779758091358231885991776368090587872494569704894555) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_75 :
    remainder3Coefficient5.coeff 75 =
      ((2891307 * 10 ^ 70 +
        5527356861206989739822304185594896592679563225301983049716920497522603) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_76 :
    remainder3Coefficient5.coeff 76 =
      -((7282798 * 10 ^ 70 +
        2308281931102051921601933607417406329156971195387916888822612581704519) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_77 :
    remainder3Coefficient5.coeff 77 =
      ((15796790 * 10 ^ 70 +
        9333484461609288275868338609808176164588548581655633392941335843756709) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_78 :
    remainder3Coefficient5.coeff 78 =
      -((30430443 * 10 ^ 70 +
        1198938751297424810222037624245617522712593614063490138278830609064811) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_79 :
    remainder3Coefficient5.coeff 79 =
      ((52961212 * 10 ^ 70 +
        3679280822372791683194641512267340837658158128418351041129922782048672) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_80 :
    remainder3Coefficient5.coeff 80 =
      -((84171041 * 10 ^ 70 +
        7408893468985812214369360201503454660116734631626444100440639462004271) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_81 :
    remainder3Coefficient5.coeff 81 =
      ((123040369 * 10 ^ 70 +
        9005659483630457618521670262184337185591494109073399139827395928714682) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_82 :
    remainder3Coefficient5.coeff 82 =
      -((166273088 * 10 ^ 70 +
        2017418057918669283278748618087014388397199910139714258714508328729345) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_83 :
    remainder3Coefficient5.coeff 83 =
      ((208496561 * 10 ^ 70 +
        8315258459843686050587028944636622744493983962353207759297044654731947) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_84 :
    remainder3Coefficient5.coeff 84 =
      -((243264732 * 10 ^ 70 +
        6235158778861948905430387116985610128303329311138506996275486962607249) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_85 :
    remainder3Coefficient5.coeff 85 =
      ((264644716 * 10 ^ 70 +
        6741888933563934245131887161077794221571807873883191441673518770514292) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_86 :
    remainder3Coefficient5.coeff 86 =
      -((268858287 * 10 ^ 70 +
        8365336436617406242871454627367694745114585140934013065063317671139375) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_87 :
    remainder3Coefficient5.coeff 87 =
      ((255359355 * 10 ^ 70 +
        7271417913201208446836563835930399275607651619991705100169760218752352) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_88 :
    remainder3Coefficient5.coeff 88 =
      -((226930445 * 10 ^ 70 +
        8244851130786977824229705264836156732253056194702450059501876420201137) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_89 :
    remainder3Coefficient5.coeff 89 =
      ((188784429 * 10 ^ 70 +
        7009957210035837767091600120116933918934224364197779982762460968274730) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_90 :
    remainder3Coefficient5.coeff 90 =
      -((147056074 * 10 ^ 70 +
        9271792529933718642297334643268309425912084999014088297796059317143268) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_91 :
    remainder3Coefficient5.coeff 91 =
      ((107264601 * 10 ^ 70 +
        5655485347770105478432796670080315351963895547759087326290334576030275) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_92 :
    remainder3Coefficient5.coeff 92 =
      -((73250322 * 10 ^ 70 +
        8668572862156810803118007404263776587791988126342028672689814708556496) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_93 :
    remainder3Coefficient5.coeff 93 =
      ((46814430 * 10 ^ 70 +
        0853714753179464768165001736359478988720474738074794201969067930200703) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_94 :
    remainder3Coefficient5.coeff 94 =
      -((27984736 * 10 ^ 70 +
        1235686798847775630656184850506128403611491407807494217458046530359994) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_95 :
    remainder3Coefficient5.coeff 95 =
      ((15635270 * 10 ^ 70 +
        4291582908774896798775330773343512151522814191987918443839200574530752) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_96 :
    remainder3Coefficient5.coeff 96 =
      -((8156796 * 10 ^ 70 +
        4059342537181242914268387620031594439668585633103548300433367776799500) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_97 :
    remainder3Coefficient5.coeff 97 =
      ((3968845 * 10 ^ 70 +
        0707802158972314189699432560347948576501612799974069615748044579376778) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_98 :
    remainder3Coefficient5.coeff 98 =
      -((1798653 * 10 ^ 70 +
        2606676608036032930939094674071980371221241581198247246483649023772656) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_99 :
    remainder3Coefficient5.coeff 99 =
      ((758018 * 10 ^ 70 +
        4208916519539297790360378321882817195130328393419482122791868070465564) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_100 :
    remainder3Coefficient5.coeff 100 =
      -((296527 * 10 ^ 70 +
        2352933744063046617640492315934479033772964798254129430881919971030965) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_101 :
    remainder3Coefficient5.coeff 101 =
      ((107445 * 10 ^ 70 +
        4443066940163824257190740599399667653184295345415616823262510873205420) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_102 :
    remainder3Coefficient5.coeff 102 =
      -((35975 * 10 ^ 70 +
        3689819533977161037169955334229921734293980497730097550408841912945356) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_103 :
    remainder3Coefficient5.coeff 103 =
      ((11100 * 10 ^ 70 +
        0304750588690367789764447195187821765514094402108803291725926867574462) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_104 :
    remainder3Coefficient5.coeff 104 =
      -((3146 * 10 ^ 70 +
        1878559035609974432185665843772417900361319406666511490799428414130423) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_105 :
    remainder3Coefficient5.coeff 105 =
      ((816 * 10 ^ 70 +
        2689132900902153483871891507015679161297263692329257292945453729701981) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_106 :
    remainder3Coefficient5.coeff 106 =
      -((193 * 10 ^ 70 +
        0596903859232854114376492422850788611645700447386490662054897860910174) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_107 :
    remainder3Coefficient5.coeff 107 =
      ((41 * 10 ^ 70 +
        4301773830745419847878688478118867785217992374857152748342667625328316) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_108 :
    remainder3Coefficient5.coeff 108 =
      -((8 * 10 ^ 70 +
        0232712501281461530959948749617306803171906720627872012789886366106333) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_109 :
    remainder3Coefficient5.coeff 109 =
      ((1 * 10 ^ 70 +
        3933501439803518606305450146542102579122155314673201932427275093563651) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_110 :
    remainder3Coefficient5.coeff 110 =
      (-2154010580000914123888347706398050309774017660112198043582971557811006 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_111 :
    remainder3Coefficient5.coeff 111 =
      (293867853613697882417068445880469772403917429438929376490465112531229 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_112 :
    remainder3Coefficient5.coeff 112 =
      (-35018937038253135983096510644117003315940010844022081388059837272272 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_113 :
    remainder3Coefficient5.coeff 113 =
      (3600251316487800894275753333865655352187404784049787781823472171617 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_114 :
    remainder3Coefficient5.coeff 114 =
      (-314569908194423288328232713754290979147036329351124493885887477841 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_115 :
    remainder3Coefficient5.coeff 115 =
      (22930458519256445288231122943193823159909427427981409944781646074 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_116 :
    remainder3Coefficient5.coeff 116 =
      (-1362504344401340245160496691822587524683394673409576352415777549 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_117 :
    remainder3Coefficient5.coeff 117 =
      (64061390604558097883906764110598623800098919211954763283360665 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_118 :
    remainder3Coefficient5.coeff 118 =
      (-2292100627717888929660294276473888128612784009271797951977446 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_119 :
    remainder3Coefficient5.coeff 119 =
      (59151732100970484544108579724157902403400413763886616722712 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_120 :
    remainder3Coefficient5.coeff 120 =
      (-1016073560684526630577199370871922826342038529185970779716 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_121 :
    remainder3Coefficient5.coeff 121 =
      (10012740810256628612796853277483596506283317629267265714 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_122 :
    remainder3Coefficient5.coeff 122 =
      (-33354150504035218502672229077114828172928999151260057 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_123 :
    remainder3Coefficient5.coeff 123 =
      (-255742389286012772217283101849178090848564383478337 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_124 :
    remainder3Coefficient5.coeff 124 =
      (2285350403425215580504322667170907334123440058042 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_125 :
    remainder3Coefficient5.coeff 125 =
      (-2818287159834181677550113595790244618964107953 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_126 :
    remainder3Coefficient5.coeff 126 =
      (-19577197265577220913540397294542570172671329 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_127 :
    remainder3Coefficient5.coeff 127 =
      (68539716393261301098654953524650645861846 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_128 :
    remainder3Coefficient5.coeff 128 =
      (-80955427547538972733980674317060011479 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_129 :
    remainder3Coefficient5.coeff 129 =
      (37352905326245285965819736386876315 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_130 :
    remainder3Coefficient5.coeff 130 =
      (-5905487124530116060313320642201 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_131 :
    remainder3Coefficient5.coeff 131 =
      (249741379239703289263231179 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_132 :
    remainder3Coefficient5.coeff 132 =
      (-1912620390008597624124 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_133 :
    remainder3Coefficient5.coeff 133 =
      (1363823716622532 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_134 :
    remainder3Coefficient5.coeff 134 =
      (-9250229 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
