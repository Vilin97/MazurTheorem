/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_1
  recurrence4B1_coeff_10
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_11
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_12
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_13
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_14
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_15
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156

attribute [local simp]
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_16
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_17
  recurrence4B1_coeff_170
  recurrence4B1_coeff_18
  recurrence4B1_coeff_19
  recurrence4B1_coeff_2
  recurrence4B1_coeff_20
  recurrence4B1_coeff_21
  recurrence4B1_coeff_22
  recurrence4B1_coeff_23
  recurrence4B1_coeff_24
  recurrence4B1_coeff_25
  recurrence4B1_coeff_26
  recurrence4B1_coeff_27
  recurrence4B1_coeff_28
  recurrence4B1_coeff_29
  recurrence4B1_coeff_3
  recurrence4B1_coeff_30
  recurrence4B1_coeff_31
  recurrence4B1_coeff_32
  recurrence4B1_coeff_33
  recurrence4B1_coeff_34
  recurrence4B1_coeff_35
  recurrence4B1_coeff_36
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_4
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_5
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60

attribute [local simp]
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_7
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_8
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_9
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
  recurrence4B3A4_coeff_0
  recurrence4B3A4_coeff_1
  recurrence4B3A4_coeff_10
  recurrence4B3A4_coeff_100
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_11
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117

attribute [local simp]
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_12
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_13
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_14
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_15
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_16
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_17
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_19
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
  recurrence4B3A4_coeff_21
  recurrence4B3A4_coeff_22

attribute [local simp]
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_24
  recurrence4B3A4_coeff_25
  recurrence4B3A4_coeff_26
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_28
  recurrence4B3A4_coeff_29
  recurrence4B3A4_coeff_3
  recurrence4B3A4_coeff_30
  recurrence4B3A4_coeff_31
  recurrence4B3A4_coeff_32
  recurrence4B3A4_coeff_33
  recurrence4B3A4_coeff_34
  recurrence4B3A4_coeff_35
  recurrence4B3A4_coeff_36
  recurrence4B3A4_coeff_37
  recurrence4B3A4_coeff_38
  recurrence4B3A4_coeff_39
  recurrence4B3A4_coeff_4
  recurrence4B3A4_coeff_40
  recurrence4B3A4_coeff_41
  recurrence4B3A4_coeff_42
  recurrence4B3A4_coeff_43
  recurrence4B3A4_coeff_44
  recurrence4B3A4_coeff_45
  recurrence4B3A4_coeff_46
  recurrence4B3A4_coeff_47
  recurrence4B3A4_coeff_48
  recurrence4B3A4_coeff_49
  recurrence4B3A4_coeff_5
  recurrence4B3A4_coeff_50
  recurrence4B3A4_coeff_51
  recurrence4B3A4_coeff_52
  recurrence4B3A4_coeff_53
  recurrence4B3A4_coeff_54
  recurrence4B3A4_coeff_55
  recurrence4B3A4_coeff_56
  recurrence4B3A4_coeff_57
  recurrence4B3A4_coeff_58
  recurrence4B3A4_coeff_59
  recurrence4B3A4_coeff_6
  recurrence4B3A4_coeff_60
  recurrence4B3A4_coeff_61
  recurrence4B3A4_coeff_62
  recurrence4B3A4_coeff_63
  recurrence4B3A4_coeff_64
  recurrence4B3A4_coeff_65
  recurrence4B3A4_coeff_66
  recurrence4B3A4_coeff_67
  recurrence4B3A4_coeff_68
  recurrence4B3A4_coeff_69
  recurrence4B3A4_coeff_7
  recurrence4B3A4_coeff_70
  recurrence4B3A4_coeff_71
  recurrence4B3A4_coeff_72
  recurrence4B3A4_coeff_73
  recurrence4B3A4_coeff_74
  recurrence4B3A4_coeff_75
  recurrence4B3A4_coeff_76
  recurrence4B3A4_coeff_77
  recurrence4B3A4_coeff_78
  recurrence4B3A4_coeff_79
  recurrence4B3A4_coeff_8
  recurrence4B3A4_coeff_80

attribute [local simp]
  recurrence4B3A4_coeff_81
  recurrence4B3A4_coeff_82
  recurrence4B3A4_coeff_83
  recurrence4B3A4_coeff_84
  recurrence4B3A4_coeff_85
  recurrence4B3A4_coeff_86
  recurrence4B3A4_coeff_87
  recurrence4B3A4_coeff_88
  recurrence4B3A4_coeff_89
  recurrence4B3A4_coeff_9
  recurrence4B3A4_coeff_90
  recurrence4B3A4_coeff_91
  recurrence4B3A4_coeff_92
  recurrence4B3A4_coeff_93
  recurrence4B3A4_coeff_94
  recurrence4B3A4_coeff_95
  recurrence4B3A4_coeff_96
  recurrence4B3A4_coeff_97
  recurrence4B3A4_coeff_98
  recurrence4B3A4_coeff_99

private theorem recurrence4Scalar2First_coeff_97_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (97 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (97 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_97 :
    recurrence4Scalar2First.coeff 97 =
      -((((793002079636751589880 * 10 ^ 70 +
        6226446904921482154246441899495286479106337874660871925804306854040425) * 10 ^ 70 +
        7141171002155770739689637384211797635117412991256930406664520075406350) * 10 ^ 70 +
        6854889498314410385649581734132301162371098115047284827221918243304771) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (97 - x)) = _
  rw [show 98 = 1 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_97_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_98_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (98 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (98 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_98 :
    recurrence4Scalar2First.coeff 98 =
      ((((11164273970878402524102 * 10 ^ 70 +
        1921769159879135742846409374729525683742156495400060057683438851734969) * 10 ^ 70 +
        2561095813780822410357362660601712033658358592030541906691878646357771) * 10 ^ 70 +
        4439725743766677657019645824216376072632135681155024722224716085194001) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (98 - x)) = _
  rw [show 99 = 1 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_98_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_99_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (99 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (99 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_99 :
    recurrence4Scalar2First.coeff 99 =
      -((((151308054254171207330272 * 10 ^ 70 +
        5743014546228431946532467207034704007057827875259380366797099863814550) * 10 ^ 70 +
        6222135319923453222336748945017186473850027991187954048371597693852024) * 10 ^ 70 +
        7101066678318082924919656850522718922017864669743348273972754936198731) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (99 - x)) = _
  rw [show 100 = 1 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_99_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_100_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (100 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (100 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_100 :
    recurrence4Scalar2First.coeff 100 =
      ((((1978604970356656715082848 * 10 ^ 70 +
        3814168001645782444988866185798336529651899364130275214700515883102186) * 10 ^ 70 +
        0101137424090048117889448761201428823905439464520090965152272486801686) * 10 ^ 70 +
        2588730837042123496508862624335158424317299514475709808418130028328877) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (100 - x)) = _
  rw [show 101 = 1 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_100_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_101_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (101 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (101 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_101 :
    recurrence4Scalar2First.coeff 101 =
      -((((25009811111052228783191030 * 10 ^ 70 +
        0028480890408609195817497510150233314474522960262145579887866761961108) * 10 ^ 70 +
        4960206990619198657657612444406061679585120009362620964827769355197630) * 10 ^ 70 +
        8443036182621360320675184678113760270605250627886643035781687735949362) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (101 - x)) = _
  rw [show 102 = 1 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_101_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_102_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (102 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (102 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_102 :
    recurrence4Scalar2First.coeff 102 =
      ((((306028081568229815756907603 * 10 ^ 70 +
        5657248494790005871967944382883896211961067226350030295108821261338590) * 10 ^ 70 +
        8079565969275609274871480803748483851671261019816031423120819839583660) * 10 ^ 70 +
        9004033063424695728942866484412847651617948786605707214564154180416974) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (102 - x)) = _
  rw [show 103 = 1 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_102_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (103 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_103 :
    recurrence4Scalar2First.coeff 103 =
      -((((3629539404924567344489184055 * 10 ^ 70 +
        8974521800616857378585176412793624010361239371606687169333584689607225) * 10 ^ 70 +
        3906163819205710540671904691603011696877615522248755571552522050759146) * 10 ^ 70 +
        3161698367540579725860692798226409921511581985999324554321750398064423) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (103 - x)) = _
  rw [show 104 = 1 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_103_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (104 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_104 :
    recurrence4Scalar2First.coeff 104 =
      ((((41767776708383139998818475053 * 10 ^ 70 +
        9471375059285673927374330589794691751186595392193242032021216327376997) * 10 ^ 70 +
        1967797138278335725673561970800682404762561888296784206781395713092387) * 10 ^ 70 +
        6191272195407570574926585048567572263466336673162025703040063648669727) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (104 - x)) = _
  rw [show 105 = 1 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_104_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (105 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_105 :
    recurrence4Scalar2First.coeff 105 =
      -((((466798692824878348366852732033 * 10 ^ 70 +
        6360348727229808144705470410196859144928546506756649157885865909579006) * 10 ^ 70 +
        9094853635803137563062610068197486971237055401367023429327029452417969) * 10 ^ 70 +
        9936426270323296108281877275411803372402697034190152834866642648974282) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (105 - x)) = _
  rw [show 106 = 1 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_105_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (106 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_106 :
    recurrence4Scalar2First.coeff 106 =
      ((((5070687082214435352188156503249 * 10 ^ 70 +
        5116425822926958983275431222810887065996559177550649614254978192236133) * 10 ^ 70 +
        5615615100078493727473127382787633821964418522677998260927838848536187) * 10 ^ 70 +
        2617860655406078224230199240956421701699128968195799016559651454059012) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (106 - x)) = _
  rw [show 107 = 1 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_106_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (107 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_107 :
    recurrence4Scalar2First.coeff 107 =
      -((((53575303667442805796331375514617 * 10 ^ 70 +
        9865485424475993500360564104988513540312380913612598852742288873282571) * 10 ^ 70 +
        4773545145308252854790677592241194606318811338116492340745250098783153) * 10 ^ 70 +
        0553841898319413381590593361974504544587162747397013742140604765797690) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (107 - x)) = _
  rw [show 108 = 1 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_107_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (108 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_108 :
    recurrence4Scalar2First.coeff 108 =
      ((((550938790015510281724155928536395 * 10 ^ 70 +
        6379231919475036893729747999612005204493127984574936085613518170982824) * 10 ^ 70 +
        9710720105353791826562678013526679947321981994871406439367227305142875) * 10 ^ 70 +
        8146735515933922090601447427016086922078783545014097616805816688073747) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (108 - x)) = _
  rw [show 109 = 1 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_108_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (109 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_109 :
    recurrence4Scalar2First.coeff 109 =
      -((((5517434129952467743848996869119072 * 10 ^ 70 +
        6986813225781040218815809940773831709098750799109388254217294830070963) * 10 ^ 70 +
        0535002345244826402998495229610255098842530682132452643234168150058877) * 10 ^ 70 +
        1699075320530413516098114882903946904960411464961719505396523684908328) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (109 - x)) = _
  rw [show 110 = 1 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_109_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (110 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_110 :
    recurrence4Scalar2First.coeff 110 =
      ((((53839192640011075703156528932112171 * 10 ^ 70 +
        1300280763332949319277807017101971818867630810235477645244526616807159) * 10 ^ 70 +
        6535362418241488410629751154042531081843233509682426846114158594989247) * 10 ^ 70 +
        8936625251888109251006176113341983284641941962348302963591650382211301) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (110 - x)) = _
  rw [show 111 = 1 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_110_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (111 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_111 :
    recurrence4Scalar2First.coeff 111 =
      -((((512155208759918027906941103513909716 * 10 ^ 70 +
        6454465553577528908526734040525881320027010638336460470882251275269379) * 10 ^ 70 +
        3177581982057558163997789924931038458929425313426456824675970646110204) * 10 ^ 70 +
        2482824558546644326344460274256900576309925091388348242133481105764277) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (111 - x)) = _
  rw [show 112 = 1 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_111_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (112 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_112 :
    recurrence4Scalar2First.coeff 112 =
      ((((4751652961854533575847637468301158515 * 10 ^ 70 +
        4501466192172408468620688165712376849501938260079374608010753169902702) * 10 ^ 70 +
        6747172158203600053861699421895654123411051647496834110675545980228640) * 10 ^ 70 +
        7547922677970313959416000351058155257564505867225974876251933956538763) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (112 - x)) = _
  rw [show 113 = 1 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_112_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (113 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_113 :
    recurrence4Scalar2First.coeff 113 =
      -((((43014288004510307670418219616728530443 * 10 ^ 70 +
        8606276728599619522540940243448843979908544957176296208048110506205922) * 10 ^ 70 +
        3185998111579768139768572400922895920118645911601804368755079049885662) * 10 ^ 70 +
        8654810483318236092009901810341687346221600818235845892949677630625182) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (113 - x)) = _
  rw [show 114 = 1 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_113_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (114 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_114 :
    recurrence4Scalar2First.coeff 114 =
      ((((380083228766319827272342637618852446349 * 10 ^ 70 +
        7957298824505523798519969014035016835306620868680226217147203569474556) * 10 ^ 70 +
        4440864405504117200759706746172918833609068018688088639075937935170440) * 10 ^ 70 +
        9557695961958347299102558910751121873472346013654059084044230005555294) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (114 - x)) = _
  rw [show 115 = 1 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_114_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (115 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_115 :
    recurrence4Scalar2First.coeff 115 =
      -((((3279482372270865503740212175211301606536 * 10 ^ 70 +
        6823401925598304644335716898629413646561331150801781675745039157540927) * 10 ^ 70 +
        0027385259463964976659736175260340516460529750072829839934451802169482) * 10 ^ 70 +
        7515485291531929275594691830472308501888759903320781185817975283227207) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (115 - x)) = _
  rw [show 116 = 1 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_115_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (116 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_116 :
    recurrence4Scalar2First.coeff 116 =
      ((((27640509303993290184067007620558686727634 * 10 ^ 70 +
        6002831394901258825309478708006179017632084825161044121037214561259719) * 10 ^ 70 +
        4252180409485042606450455121651338717330068967800440454283934715620242) * 10 ^ 70 +
        2499775454375745495658316505128555954885022130720100685257662645362300) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (116 - x)) = _
  rw [show 117 = 1 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar2First_coeff_116_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (117 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_117 :
    recurrence4Scalar2First.coeff 117 =
      -((((227638798662496372143824359626763728730367 * 10 ^ 70 +
        4223287312499776397837419784200683932280678417584586522976604296586912) * 10 ^ 70 +
        7276203685413630562746141776355988644177881847662330870344130355857436) * 10 ^ 70 +
        1246576338056323358504955843261671600376520188789341387604681074257527) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (117 - x)) = _
  rw [show 118 = 1 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar2First_coeff_117_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (118 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_118 :
    recurrence4Scalar2First.coeff 118 =
      ((((1832500366179318300894875569787411690800673 * 10 ^ 70 +
        0656618228847497190475259836876301391893904728052728849956784631199168) * 10 ^ 70 +
        5179594927571751124049740272992257864861271690562299377461982929396778) * 10 ^ 70 +
        7481386604935521915189942023474567538290047936379490207743432902904665) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (118 - x)) = _
  rw [show 119 = 1 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  rw [recurrence4Scalar2First_coeff_118_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (119 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_119 :
    recurrence4Scalar2First.coeff 119 =
      -((((14423505644739122673251302835568060959482968 * 10 ^ 70 +
        2192623148635371372784625229273836037287306292823716924139054392424493) * 10 ^ 70 +
        4368719574329232693698468927330509579617032410187981696171761537267577) * 10 ^ 70 +
        2201844691037362372600496949423968856117885389698958461087270561333056) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (119 - x)) = _
  rw [show 120 = 1 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_119_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (120 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_120 :
    recurrence4Scalar2First.coeff 120 =
      ((((111032980958396456718229287344956724038802617 * 10 ^ 70 +
        4536964986726047158054179813773534499727342612080614986739350442997932) * 10 ^ 70 +
        5644081409639561767583683743863623379406385702088471809796037373537988) * 10 ^ 70 +
        2247799284370231683115967481118763367804711068469714993402754368672520) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (120 - x)) = _
  rw [show 121 = 1 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_120_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (121 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_121 :
    recurrence4Scalar2First.coeff 121 =
      -((((836194973345270414596752357437001786473306752 * 10 ^ 70 +
        5742718769263194876626164117936885316541365717244021173075036027400310) * 10 ^ 70 +
        4082203680384724872901475884635853422005049350459211364196490994903847) * 10 ^ 70 +
        7102586033154938012887580537661278663302075754752346709855875308376583) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (121 - x)) = _
  rw [show 122 = 1 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_121_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (122 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_122 :
    recurrence4Scalar2First.coeff 122 =
      ((((6162436300665298414933358003318706547799071911 * 10 ^ 70 +
        0958915335221186282981270647007241621436021906913997715104407043059085) * 10 ^ 70 +
        6715941884270263927272804575350000986951936596293311746955570654146164) * 10 ^ 70 +
        7596491814881642844144086273556135565548114961292862653207578448558930) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (122 - x)) = _
  rw [show 123 = 1 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_122_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (123 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_123 :
    recurrence4Scalar2First.coeff 123 =
      -((((44452583723260221616531704658261803350476805995 * 10 ^ 70 +
        6312084708390738860497410515832823514880839013777815236193685142073180) * 10 ^ 70 +
        9417743259962563962974055656938793108559045754976474722481058230283693) * 10 ^ 70 +
        4341736800113611833633508903134172361569775458693570325179636836709526) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (123 - x)) = _
  rw [show 124 = 1 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_123_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (124 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_124 :
    recurrence4Scalar2First.coeff 124 =
      ((((313940476497281691617482364392623943830638781683 * 10 ^ 70 +
        7876925828739994806013583604438750558061142719600913964252772610095356) * 10 ^ 70 +
        3356382867540870497669522043641068344106508281391744983758480915579173) * 10 ^ 70 +
        5787876913321114998273886227330324252355540552867785668029903404144362) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (124 - x)) = _
  rw [show 125 = 1 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_124_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (125 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_125 :
    recurrence4Scalar2First.coeff 125 =
      -((((2171228104549292761457640894452265310819507532537 * 10 ^ 70 +
        8298725122642024022172816262521075293963522935937172314479629044028307) * 10 ^ 70 +
        9705891930972056078021510641743272189341548678071504453759517802874989) * 10 ^ 70 +
        5038863787171140624065700833663033062362026161781364970280736733815562) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (125 - x)) = _
  rw [show 126 = 1 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_125_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (126 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_126 :
    recurrence4Scalar2First.coeff 126 =
      ((((14708548593952892688182925718433744392328080377304 * 10 ^ 70 +
        8380171270853059882544667009197285407197800971952386585550740935164793) * 10 ^ 70 +
        0633011169954210512926774486926619311593451873901871833338875271333553) * 10 ^ 70 +
        4623610952744324467739170592950502266132910396686618181640253212224192) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (126 - x)) = _
  rw [show 127 = 1 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_126_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (127 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_127 :
    recurrence4Scalar2First.coeff 127 =
      -((((97619223485029929144740021790225189675296752263142 * 10 ^ 70 +
        1841446227946086234546296025715877917047969936571122297459328300088248) * 10 ^ 70 +
        0220739026259856018930579989196142059625898594329760396533217998970784) * 10 ^ 70 +
        7885729085437381765326813996005555496003583389418329988285202716125649) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (127 - x)) = _
  rw [show 128 = 1 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_127_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (128 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_128 :
    recurrence4Scalar2First.coeff 128 =
      ((((634883033694283842744973292531394938054807029222850 * 10 ^ 70 +
        4964855201696430211823243280347740443019519271170580982578740970293013) * 10 ^ 70 +
        0863505840861485352504259608200133316111233624386603533257324140800133) * 10 ^ 70 +
        8418016911015437071772754897171099767481038874674680401365311606511960) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (128 - x)) = _
  rw [show 129 = 1 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_128_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (129 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_129 :
    recurrence4Scalar2First.coeff 129 =
      -((((4047003310093983672198701491894589628715421853284332 * 10 ^ 70 +
        0188206742192678479119755150956844415120525338356987687978941316360225) * 10 ^ 70 +
        0139829979381376187559357222238239480818443653012405770096874144718959) * 10 ^ 70 +
        5174661622291250387268070909832835105316209590345460952495231555415682) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (129 - x)) = _
  rw [show 130 = 1 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_129_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (130 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_130 :
    recurrence4Scalar2First.coeff 130 =
      ((((25289520559213851905682441535049970912584801560364978 * 10 ^ 70 +
        1972131869418955341368714177087158706133126039801970574387444230441752) * 10 ^ 70 +
        7276151006559253998684080495550065464133826057374368519827539505253727) * 10 ^ 70 +
        7758488534966238526541329495457550675498086482476700165502496455021148) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (130 - x)) = _
  rw [show 131 = 1 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_130_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (131 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_131 :
    recurrence4Scalar2First.coeff 131 =
      -((((154952228859783351879638014195994713256399153526952415 * 10 ^ 70 +
        4731894644611948038431658108202174650296533244947269889151161985301128) * 10 ^ 70 +
        9208963794609308104215473683925468257118576507176022130589930315450046) * 10 ^ 70 +
        3875005583284796125950427242035735821257431841326828318590674026917375) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (131 - x)) = _
  rw [show 132 = 1 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_131_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (132 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_132 :
    recurrence4Scalar2First.coeff 132 =
      ((((931077120897260846760369980279347068685350624354172526 * 10 ^ 70 +
        2846443707838045269225266384458180639937023981235616673940599613871363) * 10 ^ 70 +
        1728936072130642332394193820449401999871828794073603913944001927981523) * 10 ^ 70 +
        6883815667361098006609472407045865209214118023459571623631492384269024) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (132 - x)) = _
  rw [show 133 = 1 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_132_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (133 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_133 :
    recurrence4Scalar2First.coeff 133 =
      -((((5487594463700305956490617437546322021709208934805893394 * 10 ^ 70 +
        1574945112663054724364136989651274226477704484918188532283261061082692) * 10 ^ 70 +
        1079216917411747016369990829510240795588150723634299048263523356228330) * 10 ^ 70 +
        8002481367685814488295967792267615993116577133896759200348832273921117) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (133 - x)) = _
  rw [show 134 = 1 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_133_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (134 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_134 :
    recurrence4Scalar2First.coeff 134 =
      ((((31729444393711154060335902250989777163795506580744006932 * 10 ^ 70 +
        8789745041461197944927477647304204811962087156596944138286289673662909) * 10 ^ 70 +
        7262921013253163253407819825859768878556803235969372530647890654675817) * 10 ^ 70 +
        0413510834644384320450876390966784362102682308125478715063478903900280) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (134 - x)) = _
  rw [show 135 = 1 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_134_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
