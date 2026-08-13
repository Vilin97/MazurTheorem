/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C1_coeff_1
  recurrence4C1_coeff_10
  recurrence4C1_coeff_100
  recurrence4C1_coeff_101
  recurrence4C1_coeff_102
  recurrence4C1_coeff_103
  recurrence4C1_coeff_104
  recurrence4C1_coeff_105
  recurrence4C1_coeff_106
  recurrence4C1_coeff_107
  recurrence4C1_coeff_108
  recurrence4C1_coeff_109
  recurrence4C1_coeff_11
  recurrence4C1_coeff_110
  recurrence4C1_coeff_111
  recurrence4C1_coeff_112
  recurrence4C1_coeff_113
  recurrence4C1_coeff_114
  recurrence4C1_coeff_115
  recurrence4C1_coeff_116
  recurrence4C1_coeff_117
  recurrence4C1_coeff_118
  recurrence4C1_coeff_119
  recurrence4C1_coeff_12
  recurrence4C1_coeff_120
  recurrence4C1_coeff_121
  recurrence4C1_coeff_122
  recurrence4C1_coeff_123
  recurrence4C1_coeff_124
  recurrence4C1_coeff_125
  recurrence4C1_coeff_126
  recurrence4C1_coeff_127
  recurrence4C1_coeff_128
  recurrence4C1_coeff_129
  recurrence4C1_coeff_13
  recurrence4C1_coeff_130
  recurrence4C1_coeff_131
  recurrence4C1_coeff_132
  recurrence4C1_coeff_133
  recurrence4C1_coeff_134
  recurrence4C1_coeff_135
  recurrence4C1_coeff_136
  recurrence4C1_coeff_137
  recurrence4C1_coeff_138
  recurrence4C1_coeff_139
  recurrence4C1_coeff_14
  recurrence4C1_coeff_140
  recurrence4C1_coeff_141
  recurrence4C1_coeff_142
  recurrence4C1_coeff_143
  recurrence4C1_coeff_144
  recurrence4C1_coeff_145
  recurrence4C1_coeff_146
  recurrence4C1_coeff_147
  recurrence4C1_coeff_148
  recurrence4C1_coeff_149
  recurrence4C1_coeff_15
  recurrence4C1_coeff_16
  recurrence4C1_coeff_17
  recurrence4C1_coeff_18
  recurrence4C1_coeff_19
  recurrence4C1_coeff_2
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21

attribute [local simp]
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_3
  recurrence4C1_coeff_30
  recurrence4C1_coeff_31
  recurrence4C1_coeff_32
  recurrence4C1_coeff_33
  recurrence4C1_coeff_34
  recurrence4C1_coeff_35
  recurrence4C1_coeff_36
  recurrence4C1_coeff_37
  recurrence4C1_coeff_38
  recurrence4C1_coeff_39
  recurrence4C1_coeff_4
  recurrence4C1_coeff_40
  recurrence4C1_coeff_41
  recurrence4C1_coeff_42
  recurrence4C1_coeff_43
  recurrence4C1_coeff_44
  recurrence4C1_coeff_45
  recurrence4C1_coeff_46
  recurrence4C1_coeff_47
  recurrence4C1_coeff_48
  recurrence4C1_coeff_49
  recurrence4C1_coeff_5
  recurrence4C1_coeff_50
  recurrence4C1_coeff_51
  recurrence4C1_coeff_52
  recurrence4C1_coeff_53
  recurrence4C1_coeff_54
  recurrence4C1_coeff_55
  recurrence4C1_coeff_56
  recurrence4C1_coeff_57
  recurrence4C1_coeff_58
  recurrence4C1_coeff_59
  recurrence4C1_coeff_6
  recurrence4C1_coeff_60
  recurrence4C1_coeff_61
  recurrence4C1_coeff_62
  recurrence4C1_coeff_63
  recurrence4C1_coeff_64
  recurrence4C1_coeff_65
  recurrence4C1_coeff_66
  recurrence4C1_coeff_67
  recurrence4C1_coeff_68
  recurrence4C1_coeff_69
  recurrence4C1_coeff_7
  recurrence4C1_coeff_70
  recurrence4C1_coeff_71
  recurrence4C1_coeff_72
  recurrence4C1_coeff_73
  recurrence4C1_coeff_74
  recurrence4C1_coeff_75
  recurrence4C1_coeff_76
  recurrence4C1_coeff_77
  recurrence4C1_coeff_78
  recurrence4C1_coeff_79
  recurrence4C1_coeff_8

attribute [local simp]
  recurrence4C1_coeff_80
  recurrence4C1_coeff_81
  recurrence4C1_coeff_82
  recurrence4C1_coeff_83
  recurrence4C1_coeff_84
  recurrence4C1_coeff_85
  recurrence4C1_coeff_86
  recurrence4C1_coeff_87
  recurrence4C1_coeff_88
  recurrence4C1_coeff_89
  recurrence4C1_coeff_9
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
  recurrence4ExceptionalProduct_coeff_0
  recurrence4ExceptionalProduct_coeff_1
  recurrence4ExceptionalProduct_coeff_10
  recurrence4ExceptionalProduct_coeff_100
  recurrence4ExceptionalProduct_coeff_101
  recurrence4ExceptionalProduct_coeff_102
  recurrence4ExceptionalProduct_coeff_103
  recurrence4ExceptionalProduct_coeff_104
  recurrence4ExceptionalProduct_coeff_105
  recurrence4ExceptionalProduct_coeff_106
  recurrence4ExceptionalProduct_coeff_107
  recurrence4ExceptionalProduct_coeff_108
  recurrence4ExceptionalProduct_coeff_109
  recurrence4ExceptionalProduct_coeff_11
  recurrence4ExceptionalProduct_coeff_110
  recurrence4ExceptionalProduct_coeff_111
  recurrence4ExceptionalProduct_coeff_112
  recurrence4ExceptionalProduct_coeff_113
  recurrence4ExceptionalProduct_coeff_114
  recurrence4ExceptionalProduct_coeff_115
  recurrence4ExceptionalProduct_coeff_116
  recurrence4ExceptionalProduct_coeff_117
  recurrence4ExceptionalProduct_coeff_118
  recurrence4ExceptionalProduct_coeff_119
  recurrence4ExceptionalProduct_coeff_12
  recurrence4ExceptionalProduct_coeff_120
  recurrence4ExceptionalProduct_coeff_121
  recurrence4ExceptionalProduct_coeff_122
  recurrence4ExceptionalProduct_coeff_123
  recurrence4ExceptionalProduct_coeff_124
  recurrence4ExceptionalProduct_coeff_125
  recurrence4ExceptionalProduct_coeff_126
  recurrence4ExceptionalProduct_coeff_127
  recurrence4ExceptionalProduct_coeff_128
  recurrence4ExceptionalProduct_coeff_129
  recurrence4ExceptionalProduct_coeff_13
  recurrence4ExceptionalProduct_coeff_130
  recurrence4ExceptionalProduct_coeff_131
  recurrence4ExceptionalProduct_coeff_132
  recurrence4ExceptionalProduct_coeff_133
  recurrence4ExceptionalProduct_coeff_134
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139
  recurrence4ExceptionalProduct_coeff_14
  recurrence4ExceptionalProduct_coeff_140
  recurrence4ExceptionalProduct_coeff_141
  recurrence4ExceptionalProduct_coeff_142
  recurrence4ExceptionalProduct_coeff_143
  recurrence4ExceptionalProduct_coeff_144
  recurrence4ExceptionalProduct_coeff_145
  recurrence4ExceptionalProduct_coeff_146
  recurrence4ExceptionalProduct_coeff_147
  recurrence4ExceptionalProduct_coeff_148
  recurrence4ExceptionalProduct_coeff_149
  recurrence4ExceptionalProduct_coeff_15
  recurrence4ExceptionalProduct_coeff_150
  recurrence4ExceptionalProduct_coeff_151
  recurrence4ExceptionalProduct_coeff_152
  recurrence4ExceptionalProduct_coeff_153
  recurrence4ExceptionalProduct_coeff_154
  recurrence4ExceptionalProduct_coeff_155
  recurrence4ExceptionalProduct_coeff_156
  recurrence4ExceptionalProduct_coeff_157
  recurrence4ExceptionalProduct_coeff_158
  recurrence4ExceptionalProduct_coeff_159
  recurrence4ExceptionalProduct_coeff_16
  recurrence4ExceptionalProduct_coeff_17
  recurrence4ExceptionalProduct_coeff_18
  recurrence4ExceptionalProduct_coeff_19
  recurrence4ExceptionalProduct_coeff_2
  recurrence4ExceptionalProduct_coeff_20
  recurrence4ExceptionalProduct_coeff_21
  recurrence4ExceptionalProduct_coeff_22
  recurrence4ExceptionalProduct_coeff_23
  recurrence4ExceptionalProduct_coeff_24
  recurrence4ExceptionalProduct_coeff_25
  recurrence4ExceptionalProduct_coeff_26
  recurrence4ExceptionalProduct_coeff_27
  recurrence4ExceptionalProduct_coeff_28
  recurrence4ExceptionalProduct_coeff_29
  recurrence4ExceptionalProduct_coeff_3
  recurrence4ExceptionalProduct_coeff_30
  recurrence4ExceptionalProduct_coeff_31
  recurrence4ExceptionalProduct_coeff_32
  recurrence4ExceptionalProduct_coeff_33
  recurrence4ExceptionalProduct_coeff_34
  recurrence4ExceptionalProduct_coeff_35
  recurrence4ExceptionalProduct_coeff_36
  recurrence4ExceptionalProduct_coeff_37
  recurrence4ExceptionalProduct_coeff_38
  recurrence4ExceptionalProduct_coeff_39
  recurrence4ExceptionalProduct_coeff_4
  recurrence4ExceptionalProduct_coeff_40
  recurrence4ExceptionalProduct_coeff_41
  recurrence4ExceptionalProduct_coeff_42
  recurrence4ExceptionalProduct_coeff_43
  recurrence4ExceptionalProduct_coeff_44
  recurrence4ExceptionalProduct_coeff_45
  recurrence4ExceptionalProduct_coeff_46
  recurrence4ExceptionalProduct_coeff_47
  recurrence4ExceptionalProduct_coeff_48
  recurrence4ExceptionalProduct_coeff_49
  recurrence4ExceptionalProduct_coeff_5
  recurrence4ExceptionalProduct_coeff_50

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_51
  recurrence4ExceptionalProduct_coeff_52
  recurrence4ExceptionalProduct_coeff_53
  recurrence4ExceptionalProduct_coeff_54
  recurrence4ExceptionalProduct_coeff_55
  recurrence4ExceptionalProduct_coeff_56
  recurrence4ExceptionalProduct_coeff_57
  recurrence4ExceptionalProduct_coeff_58
  recurrence4ExceptionalProduct_coeff_59
  recurrence4ExceptionalProduct_coeff_6
  recurrence4ExceptionalProduct_coeff_60
  recurrence4ExceptionalProduct_coeff_61
  recurrence4ExceptionalProduct_coeff_62
  recurrence4ExceptionalProduct_coeff_63
  recurrence4ExceptionalProduct_coeff_64
  recurrence4ExceptionalProduct_coeff_65
  recurrence4ExceptionalProduct_coeff_66
  recurrence4ExceptionalProduct_coeff_67
  recurrence4ExceptionalProduct_coeff_68
  recurrence4ExceptionalProduct_coeff_69
  recurrence4ExceptionalProduct_coeff_7
  recurrence4ExceptionalProduct_coeff_70
  recurrence4ExceptionalProduct_coeff_71
  recurrence4ExceptionalProduct_coeff_72
  recurrence4ExceptionalProduct_coeff_73
  recurrence4ExceptionalProduct_coeff_74
  recurrence4ExceptionalProduct_coeff_75
  recurrence4ExceptionalProduct_coeff_76
  recurrence4ExceptionalProduct_coeff_77
  recurrence4ExceptionalProduct_coeff_78
  recurrence4ExceptionalProduct_coeff_79
  recurrence4ExceptionalProduct_coeff_8
  recurrence4ExceptionalProduct_coeff_80
  recurrence4ExceptionalProduct_coeff_81
  recurrence4ExceptionalProduct_coeff_82
  recurrence4ExceptionalProduct_coeff_83
  recurrence4ExceptionalProduct_coeff_84
  recurrence4ExceptionalProduct_coeff_85
  recurrence4ExceptionalProduct_coeff_86
  recurrence4ExceptionalProduct_coeff_87
  recurrence4ExceptionalProduct_coeff_88
  recurrence4ExceptionalProduct_coeff_89
  recurrence4ExceptionalProduct_coeff_9
  recurrence4ExceptionalProduct_coeff_90
  recurrence4ExceptionalProduct_coeff_91
  recurrence4ExceptionalProduct_coeff_92
  recurrence4ExceptionalProduct_coeff_93
  recurrence4ExceptionalProduct_coeff_94
  recurrence4ExceptionalProduct_coeff_95
  recurrence4ExceptionalProduct_coeff_96
  recurrence4ExceptionalProduct_coeff_97
  recurrence4ExceptionalProduct_coeff_98
  recurrence4ExceptionalProduct_coeff_99

private theorem recurrence4Scalar1Exceptional_coeff_135_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (135 + x) *
        remainder6Coefficient1.coeff (135 - (135 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 135 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (135 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (135 - (135 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_135 :
    recurrence4Scalar1Exceptional.coeff 135 =
      -((((99979536271787860524422371142372699539872608738317 * 10 ^ 70 +
        1036655315811401215397693848271711824135876191263051699856704979207520) * 10 ^ 70 +
        0435825294070237027247160156502276655629337756839955921719803684348344) * 10 ^ 70 +
        9804391300131829608027429225334197917733604812881614647765874367099966) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (135 - x)) = _
  rw [show 136 = 0 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_135_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_136_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (136 + x) *
        remainder6Coefficient1.coeff (136 - (136 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 136 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (136 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (136 - (136 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_136 :
    recurrence4Scalar1Exceptional.coeff 136 =
      -((((1282425037190555471623442160596608591352281357485510 * 10 ^ 70 +
        7271367180538222065018407659441017439640034410312090019993909442709344) * 10 ^ 70 +
        3852545393502621809784599138352592536896214442420114977285762970506088) * 10 ^ 70 +
        4798882639861793101610344021211388533088720283734813208560477767514075) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (136 - x)) = _
  rw [show 137 = 0 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_136_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_137_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (137 + x) *
        remainder6Coefficient1.coeff (137 - (137 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 137 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (137 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (137 - (137 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_137 :
    recurrence4Scalar1Exceptional.coeff 137 =
      ((((17962715843175647551693779215116977891386947900209191 * 10 ^ 70 +
        2617536036689386497116351488412492689516415935651719385209774687536725) * 10 ^ 70 +
        7345328727465827932498071574131796303310847370629294223187257357525129) * 10 ^ 70 +
        9404153584035870136883302426170555444107016011538700306224172471952031) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (137 - x)) = _
  rw [show 138 = 0 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_137_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_138_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (138 + x) *
        remainder6Coefficient1.coeff (138 - (138 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 138 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (138 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (138 - (138 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_138 :
    recurrence4Scalar1Exceptional.coeff 138 =
      -((((157150852446745688129329538502436187789520924480396507 * 10 ^ 70 +
        0223132870287434110791199288817142914576029674392050273742695019899524) * 10 ^ 70 +
        4923068437196529922287402460519366467661828689260094543732913615479189) * 10 ^ 70 +
        5208075377510486039716987617054723817072062494056003206379735922583918) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (138 - x)) = _
  rw [show 139 = 0 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_138_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (139 + x) *
        remainder6Coefficient1.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 139 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (139 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (139 - (139 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_139 :
    recurrence4Scalar1Exceptional.coeff 139 =
      ((((1140634346900688173165459478204920121400751008795392905 * 10 ^ 70 +
        4462795304552584775804451824343793398223921801311455466686414626787545) * 10 ^ 70 +
        0156273590839277967791346571426452057355781745024176606630935481130779) * 10 ^ 70 +
        6292228603397399128605935598564061890761952882815072556517265066941814) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (139 - x)) = _
  rw [show 140 = 0 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_139_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (140 + x) *
        remainder6Coefficient1.coeff (140 - (140 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 140 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (140 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (140 - (140 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_140 :
    recurrence4Scalar1Exceptional.coeff 140 =
      -((((7371265252994471995777842973365886193524996391831234866 * 10 ^ 70 +
        8245801406569633277543872822642042267522775562905016189764392132276644) * 10 ^ 70 +
        4767234652695766613891279495997691752917640018551608112843116600009811) * 10 ^ 70 +
        6262090385356154464424437297238604212355897153355960207291515996965462) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (140 - x)) = _
  rw [show 141 = 0 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_140_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (141 + x) *
        remainder6Coefficient1.coeff (141 - (141 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 141 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (141 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (141 - (141 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_141 :
    recurrence4Scalar1Exceptional.coeff 141 =
      ((((43532952463073656352384638670535574393241115390402258320 * 10 ^ 70 +
        4309243801454787443153696780741882080904317478192819734232554292928950) * 10 ^ 70 +
        4648092093885179100960777240329657570473012039963710309274957695621570) * 10 ^ 70 +
        6634714137262753708302233831619766423791621928323157787254540318350456) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (141 - x)) = _
  rw [show 142 = 0 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_141_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (142 + x) *
        remainder6Coefficient1.coeff (142 - (142 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 142 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (142 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (142 - (142 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_142 :
    recurrence4Scalar1Exceptional.coeff 142 =
      -((((237015504611310398822616910511929745138965237847538274277 * 10 ^ 70 +
        8553455215384547877368720997561345398035944551765174314813603187946508) * 10 ^ 70 +
        2998439413586360566393362244675617855572181108051462381431481606230611) * 10 ^ 70 +
        9441715266081179509707029614757336543785574378485556242565463716855735) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (142 - x)) = _
  rw [show 143 = 0 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_142_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (143 + x) *
        remainder6Coefficient1.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 143 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (143 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (143 - (143 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_143 :
    recurrence4Scalar1Exceptional.coeff 143 =
      ((((1186722809394812736173823713823188326681431565502476915045 * 10 ^ 70 +
        8583423586768751612372808990240445486255889025149462495005734890267283) * 10 ^ 70 +
        2052452506144004868458727146351580138102004231857757326547722097807305) * 10 ^ 70 +
        2827502174098333495718070588667367440752415855335301479093308199466333) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (143 - x)) = _
  rw [show 144 = 0 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_143_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (144 + x) *
        remainder6Coefficient1.coeff (144 - (144 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 144 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (144 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (144 - (144 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_144 :
    recurrence4Scalar1Exceptional.coeff 144 =
      -((((5378438054849300415384889403863657070535818441120536672839 * 10 ^ 70 +
        6855995456791194977598153581217506300785303534819485586927978610131206) * 10 ^ 70 +
        3260847334594515058836976636626191663690931555572608122265481419148329) * 10 ^ 70 +
        7379659374534084170081650114726136105982538560899462013812662451776036) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (144 - x)) = _
  rw [show 145 = 0 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_144_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (145 + x) *
        remainder6Coefficient1.coeff (145 - (145 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 145 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (145 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (145 - (145 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_145 :
    recurrence4Scalar1Exceptional.coeff 145 =
      ((((21119263299428291536139589689462425931293552227053156492639 * 10 ^ 70 +
        7600905463774078236881228845237066871253332700244357120467000169933425) * 10 ^ 70 +
        6940966749350211185401141445870149833206533712367406919419627603789841) * 10 ^ 70 +
        6068160302004028719871120191617022323530734761519488912009480284713352) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (145 - x)) = _
  rw [show 146 = 0 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_145_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (146 + x) *
        remainder6Coefficient1.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 146 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (146 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (146 - (146 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_146 :
    recurrence4Scalar1Exceptional.coeff 146 =
      -((((62355283065940758021752740717151987475474171012415478656199 * 10 ^ 70 +
        5576293102249682755810007604081678599421541936346602662802732846318554) * 10 ^ 70 +
        3506710330963837081922554171248611573158332900596684811437148443605375) * 10 ^ 70 +
        2422691660111849282062584358141022193413968189273701590373123243861814) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (146 - x)) = _
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_146_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (147 + x) *
        remainder6Coefficient1.coeff (147 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 147 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (147 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (147 - (147 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_147 :
    recurrence4Scalar1Exceptional.coeff 147 =
      ((((34328365733309064616579188573176520365896319267424100503108 * 10 ^ 70 +
        6528842318192892644395071027262126286506762857535370210054572534364395) * 10 ^ 70 +
        1480605426023201941750384314844255450117879066116698022730327495438646) * 10 ^ 70 +
        1824821195400532672218949065192617665347801958151868701270263437088206) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (147 - x)) = _
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_147_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (148 + x) *
        remainder6Coefficient1.coeff (148 - (148 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 148 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (148 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (148 - (148 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_148 :
    recurrence4Scalar1Exceptional.coeff 148 =
      ((((1435617824278093101915309091813767825229142323142696773765225 * 10 ^ 70 +
        8893309552541309359372943742058541406009092410241894266961540501059427) * 10 ^ 70 +
        3818421600826203247631783940385191110054877191246661275807694490853147) * 10 ^ 70 +
        8464407589476251380003759965861115477140550005722045877216097305848379) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (148 - x)) = _
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_148_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (149 + x) *
        remainder6Coefficient1.coeff (149 - (149 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 149 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (149 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (149 - (149 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_149 :
    recurrence4Scalar1Exceptional.coeff 149 =
      -((((15765816224086570205089023553514313062457642994811353076697973 * 10 ^ 70 +
        5407284644937354674252276283536732446389323520103865112849044023799979) * 10 ^ 70 +
        7613154605929046141876503947561134473664697394457713605874277453594466) * 10 ^ 70 +
        5091435669344561277012363257712009122032763954132016661174822703301120) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (149 - x)) = _
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_149_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (150 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (150 + x) *
        remainder6Coefficient1.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 150 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (150 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (150 - (150 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_150 :
    recurrence4Scalar1Exceptional.coeff 150 =
      ((((121504642005489335709470239956838393360007486648926893634743722 * 10 ^ 70 +
        5587086733942778060843613052267083237627690730860868662026781729568504) * 10 ^ 70 +
        4020953631978592890887094978420488045738373415721291035616320596501532) * 10 ^ 70 +
        6645554543749792201795689673235734735737033247001613349121221847559163) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (150 - x)) = _
  rw [show 151 = 1 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_150_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (151 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (151 + x) *
        remainder6Coefficient1.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 151 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (151 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (151 - (151 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_151 :
    recurrence4Scalar1Exceptional.coeff 151 =
      -((((804792101141946188129646808439367161205111222929281088659411534 * 10 ^ 70 +
        4256236036872346961378337548456098810671137742794298545435459771514842) * 10 ^ 70 +
        4348086018607836063469928537072344816385224192137528339374449153588481) * 10 ^ 70 +
        5133868191274334846842797242049618730153595068779955578770966459009116) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (151 - x)) = _
  rw [show 152 = 2 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_151_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (152 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (152 + x) *
        remainder6Coefficient1.coeff (152 - (152 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 152 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (152 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (152 - (152 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_152 :
    recurrence4Scalar1Exceptional.coeff 152 =
      ((((4865205121591743143098366071791843169060500541202247239203987956 * 10 ^ 70 +
        3399778087508616827821922859574518598231554064388672729603596376706867) * 10 ^ 70 +
        1485558481196690105115637931524326396709623845119914977143986914163744) * 10 ^ 70 +
        8866965722780542304541723666443942166586687707742952152833003599482718) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (152 - x)) = _
  rw [show 153 = 3 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_152_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (153 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (153 + x) *
        remainder6Coefficient1.coeff (153 - (153 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 153 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (153 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (153 - (153 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_153 :
    recurrence4Scalar1Exceptional.coeff 153 =
      -((((27562093847918901633552220768171711148090432731796984027204809427 * 10 ^ 70 +
        2210178516996361841206128345879317580066805703679470330368067608204082) * 10 ^ 70 +
        5338629579852955810455620691745743248824821980991519979461065980178959) * 10 ^ 70 +
        6269048105618944326573641435122302182670269367267430495632611454228316) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (153 - x)) = _
  rw [show 154 = 4 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_153_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (154 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (154 + x) *
        remainder6Coefficient1.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 154 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (154 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (154 - (154 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_154 :
    recurrence4Scalar1Exceptional.coeff 154 =
      ((((148402894620124370442853597801874759545297241278674404142522457813 * 10 ^ 70 +
        8412018236585500778203132298646026277940876898494517314084653566197883) * 10 ^ 70 +
        9838170621037911290984762786058295151629953184609773353509054593882798) * 10 ^ 70 +
        9323864032011724525492651037859213782371155762014026955350566877776932) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (154 - x)) = _
  rw [show 155 = 5 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_154_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (155 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (155 + x) *
        remainder6Coefficient1.coeff (155 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 155 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (155 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (155 - (155 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_155 :
    recurrence4Scalar1Exceptional.coeff 155 =
      -((((765925013099367045002368000620731003601096624218374647631539089455 * 10 ^ 70 +
        4207248865670761920410435201059127929882732834617720688560297305679809) * 10 ^ 70 +
        7327432896660970444065303057191334572255809256382474320992869322758356) * 10 ^ 70 +
        4723080736080561036532265851587278386795471454801275228974643889196231) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (155 - x)) = _
  rw [show 156 = 6 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_155_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (156 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (156 + x) *
        remainder6Coefficient1.coeff (156 - (156 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 156 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (156 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (156 - (156 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_156 :
    recurrence4Scalar1Exceptional.coeff 156 =
      ((((3810365210365080466886745278451623624612409039256792258673474942947 * 10 ^ 70 +
        2217809494068921731465146159257953992532470790946032857277739231263823) * 10 ^ 70 +
        3555919980708162316746350987825514113301544362297599225348311220918156) * 10 ^ 70 +
        1723214179585080913172092167948653301620896452939075176525676791802777) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (156 - x)) = _
  rw [show 157 = 7 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_156_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (157 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (157 + x) *
        remainder6Coefficient1.coeff (157 - (157 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 157 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (157 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (157 - (157 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_157 :
    recurrence4Scalar1Exceptional.coeff 157 =
      -((((18343102694224978564568467738304985777609778459652345841585964482007 * 10 ^ 70 +
        3562957849595887604608865573666351182175657848535825943417421502938935) * 10 ^ 70 +
        9371871289758654358285908753452330394195012515312719703424588697202600) * 10 ^ 70 +
        2319840275811685049515207249682978478039458914727633976596514829088930) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (157 - x)) = _
  rw [show 158 = 8 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_157_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (158 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (158 + x) *
        remainder6Coefficient1.coeff (158 - (158 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 158 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (158 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (158 - (158 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_158 :
    recurrence4Scalar1Exceptional.coeff 158 =
      ((((85691882589311803681469828877748868451897537917943249559795582486703 * 10 ^ 70 +
        2801812362248179755800934574794202111869433610298061817615062970245957) * 10 ^ 70 +
        2906015450149601917526979676525722713326366562886967153191763295399884) * 10 ^ 70 +
        5413158577102656135176915572973622209150461087882393818418894282933837) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (158 - x)) = _
  rw [show 159 = 9 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_158_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (159 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (159 + x) *
        remainder6Coefficient1.coeff (159 - (159 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 159 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (159 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (159 - (159 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_159 :
    recurrence4Scalar1Exceptional.coeff 159 =
      -((((389317770599707014603658159197538089667094701019729211358288456470268 * 10 ^ 70 +
        4851445431221776952358781354666889677634855997454761067970172576943343) * 10 ^ 70 +
        1157265052042885091384294274231308006178434400980007302317967254543254) * 10 ^ 70 +
        1630935544456592320109794728522824058355308688994438599893894088587897) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (159 - x)) = _
  rw [show 160 = 10 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_159_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (160 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (160 + x) *
        remainder6Coefficient1.coeff (160 - (160 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 160 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (160 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (160 - (160 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_160 :
    recurrence4Scalar1Exceptional.coeff 160 =
      ((((1723055466808578683875011932880412869384909124624580713890137868754521 * 10 ^ 70 +
        9717851091396894447876647084647528098208865013017110651003684244382590) * 10 ^ 70 +
        2974548258554826909583850106701539142428861493058764063366771102462204) * 10 ^ 70 +
        2861359619665126645057575039006180430063864728429764792689133586505819) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (160 - x)) = _
  rw [show 161 = 11 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_160_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
