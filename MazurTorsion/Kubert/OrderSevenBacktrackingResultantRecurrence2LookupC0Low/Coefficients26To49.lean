/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C0 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C0_coeff_26 :
    remainder4Coefficient0.coeff 26 =
      (5358353641923289810316231454695640774731160930358869641301 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_27 :
    remainder4Coefficient0.coeff 27 =
      (-151733892613902320668731059276185396977874583181787529963366 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_28 :
    remainder4Coefficient0.coeff 28 =
      (3916261660788291569420069376764028379928785109835567828887690 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_29 :
    remainder4Coefficient0.coeff 29 =
      (-92448566200735918254424866746257832196092338994497115278176440 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_30 :
    remainder4Coefficient0.coeff 30 =
      (2002493030313663849759458446818828012981658913199308038612727636 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_31 :
    remainder4Coefficient0.coeff 31 =
      (-39920648526267385629952858400090707042200265355834615164512062208 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_32 :
    remainder4Coefficient0.coeff 32 =
      (734533177819509477287413271955281502005821078427064188360344442371 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_33 :
    remainder4Coefficient0.coeff 33 =
      (-12507452692977962651544595122820773459955498832237098200234945555742 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_34 :
    remainder4Coefficient0.coeff 34 =
      (197586420462991385248909542772129415135930036618213305292649025647133 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_35 :
    remainder4Coefficient0.coeff 35 =
      (-2902680805118970352871139647271194747604401551075543746504464144683328 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_36 :
    remainder4Coefficient0.coeff 36 =
      ((3 * 10 ^ 70 +
        9742882462546483249549056718894116011316711210031170589579524649197846) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_37 :
    remainder4Coefficient0.coeff 37 =
      -((50 * 10 ^ 70 +
        8213543483660942809957690511042854497063475878832254864470856856441634) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_38 :
    remainder4Coefficient0.coeff 38 =
      ((608 * 10 ^ 70 +
        1596189531773994598656774218130238755639278940312271766174398508850511) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_39 :
    remainder4Coefficient0.coeff 39 =
      -((6823 * 10 ^ 70 +
        1251170549194221430846048959370653224910873577491003681983242674804801) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_40 :
    remainder4Coefficient0.coeff 40 =
      ((71896 * 10 ^ 70 +
        6819966711527633191319997714427672769795222442919773561069858031147343) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_41 :
    remainder4Coefficient0.coeff 41 =
      -((712718 * 10 ^ 70 +
        0734788483776173122298590248485379690068318915160677312771485795258676) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_42 :
    remainder4Coefficient0.coeff 42 =
      ((6657247 * 10 ^ 70 +
        6318226452339400055634241503321154514772743610266037296127378929400351) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_43 :
    remainder4Coefficient0.coeff 43 =
      -((58679670 * 10 ^ 70 +
        1504962688268005975387631723641132508787499309238881208765493889823571) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_44 :
    remainder4Coefficient0.coeff 44 =
      ((488776435 * 10 ^ 70 +
        6956172415846479131359694355903840319106372781967595853558554161723593) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_45 :
    remainder4Coefficient0.coeff 45 =
      -((3852510585 * 10 ^ 70 +
        8048473692569738347169218738352833697880681990998305810053119145127830) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_46 :
    remainder4Coefficient0.coeff 46 =
      ((28769967559 * 10 ^ 70 +
        9817819811918013130383649950126923852107816831092272538441039427590772) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_47 :
    remainder4Coefficient0.coeff 47 =
      -((203807058938 * 10 ^ 70 +
        9069762039019664301648459371411587297439357768324093667918080645561781) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_48 :
    remainder4Coefficient0.coeff 48 =
      ((1371130542823 * 10 ^ 70 +
        1842150721098517967175393927491905839555583700223202166366631931175344) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_49 :
    remainder4Coefficient0.coeff 49 =
      -((8769768194628 * 10 ^ 70 +
        9105807251357786741769827395230528932397345372402484534391047643844940) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
