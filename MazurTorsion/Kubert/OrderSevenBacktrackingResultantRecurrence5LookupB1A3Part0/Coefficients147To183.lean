/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B1A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B1_coeff_0
  recurrence5B1_coeff_1
  recurrence5B1_coeff_2
  recurrence5B1_coeff_3
  recurrence5B1_coeff_4
  recurrence5B1_coeff_5
  recurrence5B1_coeff_6
  recurrence5B1_coeff_7
  recurrence5B1_coeff_8
  recurrence5B1_coeff_9
  recurrence5B1_coeff_10
  recurrence5B1_coeff_11
  recurrence5B1_coeff_12
  recurrence5B1_coeff_13
  recurrence5B1_coeff_14
  recurrence5B1_coeff_15
  recurrence5B1_coeff_16
  recurrence5B1_coeff_17
  recurrence5B1_coeff_18
  recurrence5B1_coeff_19
  recurrence5B1_coeff_20
  recurrence5B1_coeff_21
  recurrence5B1_coeff_22
  recurrence5B1_coeff_23
  recurrence5B1_coeff_24
  recurrence5B1_coeff_25
  recurrence5B1_coeff_26
  recurrence5B1_coeff_27
  recurrence5B1_coeff_28
  recurrence5B1_coeff_29
  recurrence5B1_coeff_30
  recurrence5B1_coeff_31
  recurrence5B1_coeff_32
  recurrence5B1_coeff_33
  recurrence5B1_coeff_34
  recurrence5B1_coeff_35
  recurrence5B1_coeff_36
  recurrence5B1_coeff_37
  recurrence5B1_coeff_38
  recurrence5B1_coeff_39
  recurrence5B1_coeff_40
  recurrence5B1_coeff_41
  recurrence5B1_coeff_42
  recurrence5B1_coeff_43
  recurrence5B1_coeff_44
  recurrence5B1_coeff_45
  recurrence5B1_coeff_46
  recurrence5B1_coeff_47
  recurrence5B1_coeff_48
  recurrence5B1_coeff_49
  recurrence5B1_coeff_50
  recurrence5B1_coeff_51
  recurrence5B1_coeff_52
  recurrence5B1_coeff_53
  recurrence5B1_coeff_54
  recurrence5B1_coeff_55
  recurrence5B1_coeff_56
  recurrence5B1_coeff_57
  recurrence5B1_coeff_58
  recurrence5B1_coeff_59
  recurrence5B1_coeff_60
  recurrence5B1_coeff_61
  recurrence5B1_coeff_62
  recurrence5B1_coeff_63

attribute [local simp]
  recurrence5B1_coeff_64
  recurrence5B1_coeff_65
  recurrence5B1_coeff_66
  recurrence5B1_coeff_67
  recurrence5B1_coeff_68
  recurrence5B1_coeff_69
  recurrence5B1_coeff_70
  recurrence5B1_coeff_71
  recurrence5B1_coeff_72
  recurrence5B1_coeff_73
  recurrence5B1_coeff_74
  recurrence5B1_coeff_75
  recurrence5B1_coeff_76
  recurrence5B1_coeff_77
  recurrence5B1_coeff_78
  recurrence5B1_coeff_79
  recurrence5B1_coeff_80
  recurrence5B1_coeff_81
  recurrence5B1_coeff_82
  recurrence5B1_coeff_83
  recurrence5B1_coeff_84
  recurrence5B1_coeff_85
  recurrence5B1_coeff_86
  recurrence5B1_coeff_87
  recurrence5B1_coeff_88
  recurrence5B1_coeff_89
  recurrence5B1_coeff_90
  recurrence5B1_coeff_91
  recurrence5B1_coeff_92
  recurrence5B1_coeff_93
  recurrence5B1_coeff_94
  recurrence5B1_coeff_95
  recurrence5B1_coeff_96
  recurrence5B1_coeff_97
  recurrence5B1_coeff_98
  recurrence5B1_coeff_99
  recurrence5B1_coeff_100
  recurrence5B1_coeff_101
  recurrence5B1_coeff_102
  recurrence5B1_coeff_103
  recurrence5B1_coeff_104
  recurrence5B1_coeff_105
  recurrence5B1_coeff_106
  recurrence5B1_coeff_107
  recurrence5B1_coeff_108
  recurrence5B1_coeff_109
  recurrence5B1_coeff_110
  recurrence5B1_coeff_111
  recurrence5B1_coeff_112
  recurrence5B1_coeff_113
  recurrence5B1_coeff_114
  recurrence5B1_coeff_115
  recurrence5B1_coeff_116
  recurrence5B1_coeff_117
  recurrence5B1_coeff_118
  recurrence5B1_coeff_119
  recurrence5B1_coeff_120
  recurrence5B1_coeff_121
  recurrence5B1_coeff_122
  recurrence5B1_coeff_123
  recurrence5B1_coeff_124
  recurrence5B1_coeff_125
  recurrence5B1_coeff_126
  recurrence5B1_coeff_127

attribute [local simp]
  recurrence5B1_coeff_128
  recurrence5B1_coeff_129
  recurrence5B1_coeff_130
  recurrence5B1_coeff_131
  recurrence5B1_coeff_132
  recurrence5B1_coeff_133
  recurrence5B1_coeff_134
  recurrence5B1_coeff_135
  recurrence5B1_coeff_136
  recurrence5B1_coeff_137
  recurrence5B1_coeff_138
  recurrence5B1_coeff_139
  recurrence5B1_coeff_140
  recurrence5B1_coeff_141
  recurrence5B1_coeff_142
  recurrence5B1_coeff_143
  recurrence5B1_coeff_144
  recurrence5B1_coeff_145
  recurrence5B1_coeff_146
  recurrence5B1_coeff_147
  recurrence5B1_coeff_148
  recurrence5B1_coeff_149
  recurrence5A3_coeff_0
  recurrence5A3_coeff_1
  recurrence5A3_coeff_2
  recurrence5A3_coeff_3
  recurrence5A3_coeff_4
  recurrence5A3_coeff_5
  recurrence5A3_coeff_6
  recurrence5A3_coeff_7
  recurrence5A3_coeff_8
  recurrence5A3_coeff_9
  recurrence5A3_coeff_10
  recurrence5A3_coeff_11
  recurrence5A3_coeff_12
  recurrence5A3_coeff_13
  recurrence5A3_coeff_14
  recurrence5A3_coeff_15
  recurrence5A3_coeff_16
  recurrence5A3_coeff_17
  recurrence5A3_coeff_18
  recurrence5A3_coeff_19
  recurrence5A3_coeff_20
  recurrence5A3_coeff_21
  recurrence5A3_coeff_22
  recurrence5A3_coeff_23
  recurrence5A3_coeff_24
  recurrence5A3_coeff_25
  recurrence5A3_coeff_26
  recurrence5A3_coeff_27
  recurrence5A3_coeff_28
  recurrence5A3_coeff_29
  recurrence5A3_coeff_30
  recurrence5A3_coeff_31
  recurrence5A3_coeff_32
  recurrence5A3_coeff_33
  recurrence5A3_coeff_34
  recurrence5A3_coeff_35
  recurrence5A3_coeff_36
  recurrence5A3_coeff_37
  recurrence5A3_coeff_38
  recurrence5A3_coeff_39
  recurrence5A3_coeff_40
  recurrence5A3_coeff_41

attribute [local simp]
  recurrence5A3_coeff_42
  recurrence5A3_coeff_43
  recurrence5A3_coeff_44
  recurrence5A3_coeff_45
  recurrence5A3_coeff_46
  recurrence5A3_coeff_47
  recurrence5A3_coeff_48
  recurrence5A3_coeff_49
  recurrence5A3_coeff_50
  recurrence5A3_coeff_51
  recurrence5A3_coeff_52
  recurrence5A3_coeff_53
  recurrence5A3_coeff_54
  recurrence5A3_coeff_55
  recurrence5A3_coeff_56
  recurrence5A3_coeff_57
  recurrence5A3_coeff_58
  recurrence5A3_coeff_59
  recurrence5A3_coeff_60
  recurrence5A3_coeff_61
  recurrence5A3_coeff_62
  recurrence5A3_coeff_63
  recurrence5A3_coeff_64
  recurrence5A3_coeff_65
  recurrence5A3_coeff_66
  recurrence5A3_coeff_67
  recurrence5A3_coeff_68
  recurrence5A3_coeff_69
  recurrence5A3_coeff_70
  recurrence5A3_coeff_71
  recurrence5A3_coeff_72
  recurrence5A3_coeff_73
  recurrence5A3_coeff_74
  recurrence5A3_coeff_75
  recurrence5A3_coeff_76
  recurrence5A3_coeff_77
  recurrence5A3_coeff_78
  recurrence5A3_coeff_79
  recurrence5A3_coeff_80
  recurrence5A3_coeff_81
  recurrence5A3_coeff_82
  recurrence5A3_coeff_83
  recurrence5A3_coeff_84
  recurrence5A3_coeff_85
  recurrence5A3_coeff_86
  recurrence5A3_coeff_87
  recurrence5A3_coeff_88
  recurrence5A3_coeff_89
  recurrence5A3_coeff_90
  recurrence5A3_coeff_91
  recurrence5A3_coeff_92
  recurrence5A3_coeff_93
  recurrence5A3_coeff_94
  recurrence5A3_coeff_95
  recurrence5A3_coeff_96
  recurrence5A3_coeff_97
  recurrence5A3_coeff_98
  recurrence5A3_coeff_99
  recurrence5A3_coeff_100
  recurrence5A3_coeff_101
  recurrence5A3_coeff_102
  recurrence5A3_coeff_103
  recurrence5A3_coeff_104
  recurrence5A3_coeff_105

attribute [local simp]
  recurrence5A3_coeff_106
  recurrence5A3_coeff_107
  recurrence5A3_coeff_108
  recurrence5A3_coeff_109
  recurrence5A3_coeff_110
  recurrence5A3_coeff_111
  recurrence5A3_coeff_112
  recurrence5A3_coeff_113
  recurrence5A3_coeff_114
  recurrence5A3_coeff_115
  recurrence5A3_coeff_116
  recurrence5A3_coeff_117
  recurrence5A3_coeff_118
  recurrence5A3_coeff_119
  recurrence5A3_coeff_120
  recurrence5A3_coeff_121
  recurrence5A3_coeff_122
  recurrence5A3_coeff_123
  recurrence5A3_coeff_124
  recurrence5A3_coeff_125
  recurrence5A3_coeff_126
  recurrence5A3_coeff_127
  recurrence5A3_coeff_128
  recurrence5A3_coeff_129
  recurrence5A3_coeff_130
  recurrence5A3_coeff_131
  recurrence5A3_coeff_132
  recurrence5A3_coeff_133
  recurrence5A3_coeff_134
  recurrence5A3_coeff_135
  recurrence5A3_coeff_136
  recurrence5A3_coeff_137
  recurrence5A3_coeff_138
  recurrence5A3_coeff_139
  recurrence5A3_coeff_140
  recurrence5A3_coeff_141
  recurrence5A3_coeff_142
  recurrence5A3_coeff_143
  recurrence5A3_coeff_144
  recurrence5A3_coeff_145
  recurrence5A3_coeff_146
  recurrence5A3_coeff_147
  recurrence5A3_coeff_148
  recurrence5A3_coeff_149
  recurrence5A3_coeff_150
  recurrence5A3_coeff_151
  recurrence5A3_coeff_152
  recurrence5A3_coeff_153
  recurrence5A3_coeff_154
  recurrence5A3_coeff_155
  recurrence5A3_coeff_156
  recurrence5A3_coeff_157
  recurrence5A3_coeff_158
  recurrence5A3_coeff_159
  recurrence5A3_coeff_160
  recurrence5A3_coeff_161
  recurrence5A3_coeff_162
  recurrence5A3_coeff_163
  recurrence5A3_coeff_164

theorem recurrence5B1A3_coeff_147 :
    recurrence5B1A3.coeff 147 =
      -((((1696334771169582388970 * 10 ^ 70 +
        1966026530578096573451621291948217449677941882332284933278381720933130) * 10 ^ 70 +
        9243919591624522445580297336580824866442768952776025888404564519382810) * 10 ^ 70 +
        9462935794965288793910172592023300830673960421196233754928336225981228) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5B1A3_coeff_148 :
    recurrence5B1A3.coeff 148 =
      ((((1168738582272903478090 * 10 ^ 70 +
        4652498502575117371892790951102417018151937681722567847710231298491101) * 10 ^ 70 +
        9006151521380294967408270614872638372373519581328691047634978911051955) * 10 ^ 70 +
        8591221023173859750127283027460963237822607476740971460408882332226757) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5B1A3_coeff_149 :
    recurrence5B1A3.coeff 149 =
      -((((667745789158280733079 * 10 ^ 70 +
        3214060340802266070701496802160247571364853455464027256043551797141089) * 10 ^ 70 +
        6870054493125727036454062553539548247515300326034213902479843825932138) * 10 ^ 70 +
        8573393631876245165870861095721574398632896078157222728545886830199530) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_150 :
    recurrence5B1A3.coeff 150 =
      ((((222491767065150853213 * 10 ^ 70 +
        7433526164715881836425481711855752321169238824993227978851826925340228) * 10 ^ 70 +
        2347948838405077003763798443733052704654820113221596141113061392619105) * 10 ^ 70 +
        2952213231712987160497582705408228128811855809544970054022812561043945) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (151 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_151 :
    recurrence5B1A3.coeff 151 =
      ((((145908669090124038113 * 10 ^ 70 +
        5970908065571126360572764504094977811149645032015104822179628147971453) * 10 ^ 70 +
        2480192702142150412749746872785485102190834908996534419830091531414907) * 10 ^ 70 +
        0333719159030366615699859868176812053175282329293768689653285538341811) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 22 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (152 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_152 :
    recurrence5B1A3.coeff 152 =
      -((((425775527349951458324 * 10 ^ 70 +
        6358425841630066315278722020211999438419970278666582857040469899499354) * 10 ^ 70 +
        5072592202740952110764364146408480174089781778945791130812223269524299) * 10 ^ 70 +
        9673966935149128498335961638391970632043486279093571444665296879784842) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 22 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (153 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_153 :
    recurrence5B1A3.coeff 153 =
      ((((614883452156075799937 * 10 ^ 70 +
        9398135728751386699866175149109371537924321999907717596576265664578659) * 10 ^ 70 +
        1637906134231124866479415928118226874003020777776239487027054277135409) * 10 ^ 70 +
        6254504433847372819872356563925617161225889353401283076060376980483011) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 22 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (154 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_154 :
    recurrence5B1A3.coeff 154 =
      -((((719255060513491107871 * 10 ^ 70 +
        2389719419005281065856239249134001475643454084254298106159077603325420) * 10 ^ 70 +
        9218884039327324530563919817867172038464076117911831102339476485932659) * 10 ^ 70 +
        2665584547015237070743463030860490621844719576368013869651260482952730) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 22 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (155 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_155 :
    recurrence5B1A3.coeff 155 =
      ((((751084228375487791305 * 10 ^ 70 +
        9011498167860773310004964736274429325868434380614985260593559121800905) * 10 ^ 70 +
        2380519232283868851914245678465605652246085217526612709544424801628184) * 10 ^ 70 +
        5469875499205797880248043314673424806338879656222403446999581258019867) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 22 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (156 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_156 :
    recurrence5B1A3.coeff 156 =
      -((((726240085150188712872 * 10 ^ 70 +
        3991691443568615061502021127059869137001675634208635855506600276932344) * 10 ^ 70 +
        6557656147404013369324630030653781649321319557903618255556149539610778) * 10 ^ 70 +
        1556284314681060731246840049573484381314270461804295200261805048345989) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 22 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (157 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_157 :
    recurrence5B1A3.coeff 157 =
      ((((661796488893218280043 * 10 ^ 70 +
        1396324522462921219672092708802797185775409697608741607611196129735669) * 10 ^ 70 +
        8230529849609594992647473275964751527395495550593060106479295799197227) * 10 ^ 70 +
        5737630650028324087983977052411017188976799914925712628154566773680396) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 22 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (158 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_158 :
    recurrence5B1A3.coeff 158 =
      -((((573943276210988164074 * 10 ^ 70 +
        6182988196831383784374148395060424751188244984246485590614258377119519) * 10 ^ 70 +
        7769457905895964135595380146453528199063180510358881068586575947260364) * 10 ^ 70 +
        4276478694713123552812136533339183782416512264686163194997183826510509) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 22 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (159 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_159 :
    recurrence5B1A3.coeff 159 =
      ((((476498139052099747503 * 10 ^ 70 +
        3494268883820268266805654773414180117239509610715107911814812909623334) * 10 ^ 70 +
        0868268572571494099121381200096677561537728864304149620803908646939134) * 10 ^ 70 +
        1186834055792559106479006163571029331888718533794683854948754034905868) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 22 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (160 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_160 :
    recurrence5B1A3.coeff 160 =
      -((((380089717897558270606 * 10 ^ 70 +
        7632347964880164255713327865192823216747563703851520986583628338053947) * 10 ^ 70 +
        9016918485689347319597849567370702979536108397151088853368977261349476) * 10 ^ 70 +
        7371035274421870772219125856428446134039085483830602367214131974068994) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 22 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (161 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_161 :
    recurrence5B1A3.coeff 161 =
      ((((291955944290318127098 * 10 ^ 70 +
        5394157582988855622576655271557070315286006780967944791681705673182163) * 10 ^ 70 +
        2155776874800761886822490988114916381566872294069518533872914791708190) * 10 ^ 70 +
        7210717800464807780054467317772783320179780284782782554613945236305634) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 22 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (162 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_162 :
    recurrence5B1A3.coeff 162 =
      -((((216217083886216883956 * 10 ^ 70 +
        5034357348527587712625015063895370320824540104877221235491540237977581) * 10 ^ 70 +
        7937744945856398661413699810496564890192663608033861983540946264676217) * 10 ^ 70 +
        3542625931512077386080401223916046287766088711136231573377420163436068) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 22 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (163 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_163 :
    recurrence5B1A3.coeff 163 =
      ((((154446369778793258927 * 10 ^ 70 +
        7351373931789465024056698572353461199789165641295607711140300340663371) * 10 ^ 70 +
        9661364819084474714079451408463582246125871637281584815493638487702544) * 10 ^ 70 +
        4128200332183129480673074327376661343706200952583880133263502160094750) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 22 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (164 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_164 :
    recurrence5B1A3.coeff 164 =
      -((((106366570454688563347 * 10 ^ 70 +
        5698293929213996300484367426723104942838548204851772364971360518155550) * 10 ^ 70 +
        8611268992181425359351051877689806279990144504931986894823843447029871) * 10 ^ 70 +
        2657275583000049560639707240840007657154320103459100339923480282903700) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 22 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (165 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_165 :
    recurrence5B1A3.coeff 165 =
      ((((70534935404509769926 * 10 ^ 70 +
        1749895733086566628265290315516218443315853930973680941365008424942930) * 10 ^ 70 +
        6591945885417979450971907174119883696267035527681145180509881439739126) * 10 ^ 70 +
        7858522256241062776196946741807583654141401222756148217125482908354514) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 1 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 21 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (166 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_166 :
    recurrence5B1A3.coeff 166 =
      -((((44926210233912653911 * 10 ^ 70 +
        9840661468183852006150807815696686400450959436286740302934304189149670) * 10 ^ 70 +
        1761356867441426632938082420263056568648742595609678500997248977314923) * 10 ^ 70 +
        2978077536204277768556638380230954868539603492017820171307715783823358) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 2 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 20 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (167 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_167 :
    recurrence5B1A3.coeff 167 =
      ((((27370428250093689509 * 10 ^ 70 +
        1608651914686331557036879568458539328994735311846150107942992372518036) * 10 ^ 70 +
        5517716327525965657831326146956438287036820955523847886240795651638580) * 10 ^ 70 +
        1708666270000865775280294685576589071720191948405787102976616848461338) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 3 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 19 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (168 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_168 :
    recurrence5B1A3.coeff 168 =
      -((((15840082331275603799 * 10 ^ 70 +
        9872307400694260491256304426707859541706391688038259092766230497936479) * 10 ^ 70 +
        5791372681228879572074905851629197423899096113612695289867901167511259) * 10 ^ 70 +
        4324677928446408580524356779250480507413461374945374100575761443558926) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 4 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 18 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (169 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_169 :
    recurrence5B1A3.coeff 169 =
      ((((8606170082079437933 * 10 ^ 70 +
        3456246498257957630862838972674033801129346905514590285625252801721087) * 10 ^ 70 +
        3424233254357222853931394507379714640206859597058242116129871821507498) * 10 ^ 70 +
        8278770303821290148331950985078398138426612705936625778236328639090094) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 5 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 17 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (170 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_170 :
    recurrence5B1A3.coeff 170 =
      -((((4294696525852669412 * 10 ^ 70 +
        3895683051944630971329282520832571340751774248176622833576294714129955) * 10 ^ 70 +
        2653497232849493457378734232815736547587375924444993648268696293033913) * 10 ^ 70 +
        5545311679296657711080613386354551622771113346173596901236924181578010) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 6 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (171 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_171 :
    recurrence5B1A3.coeff 171 =
      ((((1877253568224390693 * 10 ^ 70 +
        7097489974733632601368165383952883373347652617317285196734059922877655) * 10 ^ 70 +
        6872348725957690625088558456983313975924057031144519437389703915845077) * 10 ^ 70 +
        3220309396611500067276999633931969818601457174919472165142423472239822) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 7 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (172 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_172 :
    recurrence5B1A3.coeff 172 =
      -((((624962138034567365 * 10 ^ 70 +
        6523496045510611751089839921680772869577669896601639291968178209937424) * 10 ^ 70 +
        1617382231159466913269842933720140283829326233787704829345643731958339) * 10 ^ 70 +
        3071194281482349709968690435120853787999462997791511720808929477595937) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 8 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 14 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (173 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_173 :
    recurrence5B1A3.coeff 173 =
      ((((47806583694716461 * 10 ^ 70 +
        4101286304064084668604474230954252447940909047329276137574682303306118) * 10 ^ 70 +
        9315906507721099002595145055740300672106861695265211850755028653904327) * 10 ^ 70 +
        2545487616381492592279272223795313612136682069397858960694769597355316) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 9 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 13 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (174 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_174 :
    recurrence5B1A3.coeff 174 =
      ((((166231855393716302 * 10 ^ 70 +
        4847061613652383040251795294299872242187071493992639217243177129583952) * 10 ^ 70 +
        3792308684789185265201505496250395578258440316472453918879757538797872) * 10 ^ 70 +
        0032929638595729566087026585223128966917274080736213004137658785502095) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 10 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (175 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_175 :
    recurrence5B1A3.coeff 175 =
      -((((204320984450881800 * 10 ^ 70 +
        7512537374960658187825489096316496989314346642467256506512553697880710) * 10 ^ 70 +
        4036886693725967690613692755660899955575118813424913126166268587833810) * 10 ^ 70 +
        8864353592758423667910713477532379400877785382246912314225359597952425) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 11 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 11 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (176 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_176 :
    recurrence5B1A3.coeff 176 =
      ((((171025722892021524 * 10 ^ 70 +
        4418287877948373971152407410066648837140512080349524326168787379866815) * 10 ^ 70 +
        6999756914202845919743247017022644902005203839746671733566736299227582) * 10 ^ 70 +
        0389498369819292272338479136246812400741268079885464536826176516545971) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 12 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 10 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (177 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_177 :
    recurrence5B1A3.coeff 177 =
      -((((119491122106760021 * 10 ^ 70 +
        6640513418778050195603354980581318254690198505448474605337578363901212) * 10 ^ 70 +
        3177375871659159030087392460376395903307638154094828498210695906143177) * 10 ^ 70 +
        2739598967587491399846186603447433510405029246230593573474975820513458) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 13 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 9 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (178 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_178 :
    recurrence5B1A3.coeff 178 =
      ((((72994432450766246 * 10 ^ 70 +
        8904225233977728789133613688292263713080568538560266850174750648321187) * 10 ^ 70 +
        5373258735275803595441948130937862022713725271008014183668840894719760) * 10 ^ 70 +
        6432493069213463487257484545887129531816407622891299580938006036084376) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 14 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 8 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (179 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_179 :
    recurrence5B1A3.coeff 179 =
      -((((38915046181994298 * 10 ^ 70 +
        1402521324058696133797529588269382942447737648972394433601727488937925) * 10 ^ 70 +
        8922854938573624905768807965824657272043836119013347151476990088213290) * 10 ^ 70 +
        7159561123992166917075321795065841284260228275541837103564814613097471) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 15 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 7 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (180 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_180 :
    recurrence5B1A3.coeff 180 =
      ((((17186329052556079 * 10 ^ 70 +
        8182021616738886491312416010810247420382433759052379907703427578942976) * 10 ^ 70 +
        1401741935189178577431366110690351700975185362388852135057204001960827) * 10 ^ 70 +
        9195942560022634829991675123276423404097903297244974040805990456224379) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 16 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 6 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (181 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_181 :
    recurrence5B1A3.coeff 181 =
      -((((5004230123704493 * 10 ^ 70 +
        0709285160979995156419520967892630457404284118640480321006067692240713) * 10 ^ 70 +
        5169017695777774407697638103964894474880141041402397003499809131642179) * 10 ^ 70 +
        2351210960488379455186457147570775557769851236925913272887524755494965) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 17 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 5 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (182 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_182 :
    recurrence5B1A3.coeff 182 =
      -((((829851837774744 * 10 ^ 70 +
        9741666212108834321057213380816392540075525918898340238650269807429474) * 10 ^ 70 +
        5961694463209292250426915267926457719844974809419111689341784213302360) * 10 ^ 70 +
        4593146947769372167375428600382945536833927555348874183818215131436595) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 18 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 4 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (183 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_183 :
    recurrence5B1A3.coeff 183 =
      ((((2946538079547601 * 10 ^ 70 +
        8571534215730870232310464961064504973214675850090951616991956185971015) * 10 ^ 70 +
        2985100818364682212738159700122739745880382183531244112036685069510034) * 10 ^ 70 +
        5527011092804275071142197311768689933015754779663205909949488528567114) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 19 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 3 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
