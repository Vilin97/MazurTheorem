/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2ExceptionalProduct_coeff_0
  recurrence2ExceptionalProduct_coeff_1
  recurrence2ExceptionalProduct_coeff_2
  recurrence2ExceptionalProduct_coeff_3
  recurrence2ExceptionalProduct_coeff_4
  recurrence2ExceptionalProduct_coeff_5
  recurrence2ExceptionalProduct_coeff_6
  recurrence2ExceptionalProduct_coeff_7
  recurrence2ExceptionalProduct_coeff_8
  recurrence2ExceptionalProduct_coeff_9
  recurrence2ExceptionalProduct_coeff_10
  recurrence2ExceptionalProduct_coeff_11
  recurrence2ExceptionalProduct_coeff_12
  recurrence2ExceptionalProduct_coeff_13
  recurrence2ExceptionalProduct_coeff_14
  recurrence2ExceptionalProduct_coeff_15
  recurrence2ExceptionalProduct_coeff_16
  recurrence2ExceptionalProduct_coeff_17
  recurrence2ExceptionalProduct_coeff_18
  recurrence2ExceptionalProduct_coeff_19
  recurrence2ExceptionalProduct_coeff_20
  recurrence2ExceptionalProduct_coeff_21
  recurrence2ExceptionalProduct_coeff_22
  recurrence2ExceptionalProduct_coeff_23
  recurrence2ExceptionalProduct_coeff_24
  recurrence2ExceptionalProduct_coeff_25
  recurrence2ExceptionalProduct_coeff_26
  recurrence2ExceptionalProduct_coeff_27
  recurrence2ExceptionalProduct_coeff_28
  recurrence2ExceptionalProduct_coeff_29
  recurrence2ExceptionalProduct_coeff_30
  recurrence2ExceptionalProduct_coeff_31
  recurrence2ExceptionalProduct_coeff_32
  recurrence2ExceptionalProduct_coeff_33
  recurrence2ExceptionalProduct_coeff_34
  recurrence2ExceptionalProduct_coeff_35
  recurrence2ExceptionalProduct_coeff_36
  recurrence2ExceptionalProduct_coeff_37
  recurrence2ExceptionalProduct_coeff_38
  recurrence2ExceptionalProduct_coeff_39
  recurrence2ExceptionalProduct_coeff_40
  recurrence2ExceptionalProduct_coeff_41
  recurrence2ExceptionalProduct_coeff_42
  recurrence2ExceptionalProduct_coeff_43
  recurrence2ExceptionalProduct_coeff_44
  recurrence2ExceptionalProduct_coeff_45
  recurrence2ExceptionalProduct_coeff_46
  recurrence2ExceptionalProduct_coeff_47
  recurrence2ExceptionalProduct_coeff_48
  recurrence2ExceptionalProduct_coeff_49
  recurrence2ExceptionalProduct_coeff_50
  recurrence2ExceptionalProduct_coeff_51
  recurrence2ExceptionalProduct_coeff_52
  recurrence2ExceptionalProduct_coeff_53
  recurrence2ExceptionalProduct_coeff_54
  recurrence2ExceptionalProduct_coeff_55
  recurrence2ExceptionalProduct_coeff_56
  recurrence2ExceptionalProduct_coeff_57
  recurrence2ExceptionalProduct_coeff_58
  recurrence2ExceptionalProduct_coeff_59
  recurrence2ExceptionalProduct_coeff_60
  recurrence2ExceptionalProduct_coeff_61
  recurrence2ExceptionalProduct_coeff_62
  recurrence2ExceptionalProduct_coeff_63
  recurrence2ExceptionalProduct_coeff_64
  recurrence2ExceptionalProduct_coeff_65
  recurrence2ExceptionalProduct_coeff_66
  recurrence2ExceptionalProduct_coeff_67
  recurrence2ExceptionalProduct_coeff_68
  recurrence2ExceptionalProduct_coeff_69
  recurrence2ExceptionalProduct_coeff_70
  recurrence2ExceptionalProduct_coeff_71
  recurrence2ExceptionalProduct_coeff_72
  recurrence2ExceptionalProduct_coeff_73
  recurrence2ExceptionalProduct_coeff_74
  recurrence2ExceptionalProduct_coeff_75
  recurrence2ExceptionalProduct_coeff_76
  recurrence2ExceptionalProduct_coeff_77
  recurrence2ExceptionalProduct_coeff_78
  recurrence2ExceptionalProduct_coeff_79
  recurrence2ExceptionalProduct_coeff_80
  recurrence2ExceptionalProduct_coeff_81
  recurrence2ExceptionalProduct_coeff_82
  recurrence2ExceptionalProduct_coeff_83
  recurrence2ExceptionalProduct_coeff_84
  recurrence2ExceptionalProduct_coeff_85
  recurrence2ExceptionalProduct_coeff_86
  recurrence2ExceptionalProduct_coeff_87
  recurrence2ExceptionalProduct_coeff_88
  recurrence2ExceptionalProduct_coeff_89
  recurrence2ExceptionalProduct_coeff_90
  recurrence2ExceptionalProduct_coeff_91
  recurrence2ExceptionalProduct_coeff_92
  recurrence2ExceptionalProduct_coeff_93
  recurrence2ExceptionalProduct_coeff_94
  recurrence2ExceptionalProduct_coeff_95
  recurrence2ExceptionalProduct_coeff_96
  recurrence2ExceptionalProduct_coeff_97
  recurrence2ExceptionalProduct_coeff_98
  recurrence2ExceptionalProduct_coeff_99
  recurrence2ExceptionalProduct_coeff_100
  recurrence2ExceptionalProduct_coeff_101
  recurrence2ExceptionalProduct_coeff_102
  recurrence2ExceptionalProduct_coeff_103
  recurrence2ExceptionalProduct_coeff_104
  recurrence2ExceptionalProduct_coeff_105
  recurrence2ExceptionalProduct_coeff_106
  recurrence2ExceptionalProduct_coeff_107
  recurrence2ExceptionalProduct_coeff_108
  recurrence2ExceptionalProduct_coeff_109
  recurrence2ExceptionalProduct_coeff_110
  recurrence2ExceptionalProduct_coeff_111
  recurrence2ExceptionalProduct_coeff_112
  recurrence2ExceptionalProduct_coeff_113
  recurrence2ExceptionalProduct_coeff_114
  recurrence2ExceptionalProduct_coeff_115
  recurrence2ExceptionalProduct_coeff_116
  recurrence2ExceptionalProduct_coeff_117
  recurrence2ExceptionalProduct_coeff_118
  recurrence2ExceptionalProduct_coeff_119
  recurrence2ExceptionalProduct_coeff_120
  recurrence2ExceptionalProduct_coeff_121
  recurrence2ExceptionalProduct_coeff_122
  recurrence2ExceptionalProduct_coeff_123
  recurrence2ExceptionalProduct_coeff_124
  recurrence2ExceptionalProduct_coeff_125
  recurrence2ExceptionalProduct_coeff_126
  recurrence2ExceptionalProduct_coeff_127
  recurrence2ExceptionalProduct_coeff_128
  recurrence2ExceptionalProduct_coeff_129
  recurrence2ExceptionalProduct_coeff_130
  recurrence2ExceptionalProduct_coeff_131
  recurrence2ExceptionalProduct_coeff_132
  recurrence2ExceptionalProduct_coeff_133
  recurrence2ExceptionalProduct_coeff_134
  recurrence2ExceptionalProduct_coeff_135
  recurrence2ExceptionalProduct_coeff_136
  recurrence2ExceptionalProduct_coeff_137
  recurrence2ExceptionalProduct_coeff_138
  recurrence2ExceptionalProduct_coeff_139
  recurrence2ExceptionalProduct_coeff_140
  recurrence2ExceptionalProduct_coeff_141
  recurrence2ExceptionalProduct_coeff_142
  recurrence2ExceptionalProduct_coeff_143
  recurrence2ExceptionalProduct_coeff_144
  recurrence2ExceptionalProduct_coeff_145
  recurrence2ExceptionalProduct_coeff_146
  recurrence2ExceptionalProduct_coeff_147
  recurrence2ExceptionalProduct_coeff_148
  recurrence2ExceptionalProduct_coeff_149
  recurrence2ExceptionalProduct_coeff_150
  recurrence2ExceptionalProduct_coeff_151
  recurrence2ExceptionalProduct_coeff_152
  recurrence2ExceptionalProduct_coeff_153
  recurrence2ExceptionalProduct_coeff_154
  recurrence2ExceptionalProduct_coeff_155
  recurrence2ExceptionalProduct_coeff_156
  recurrence2ExceptionalProduct_coeff_157
  recurrence2ExceptionalProduct_coeff_158
  recurrence2ExceptionalProduct_coeff_159
  recurrence2ExceptionalProduct_coeff_160
  recurrence2ExceptionalProduct_coeff_161
  recurrence2ExceptionalProduct_coeff_162
  recurrence2ExceptionalProduct_coeff_163
  recurrence2ExceptionalProduct_coeff_164
  recurrence2ExceptionalProduct_coeff_165
  recurrence2ExceptionalProduct_coeff_166
  recurrence2ExceptionalProduct_coeff_167
  recurrence2ExceptionalProduct_coeff_168
  recurrence2ExceptionalProduct_coeff_169
  recurrence2ExceptionalProduct_coeff_170
  recurrence2ExceptionalProduct_coeff_171
  recurrence2ExceptionalProduct_coeff_172
  recurrence2ExceptionalProduct_coeff_173
  recurrence2ExceptionalProduct_coeff_174
  recurrence2ExceptionalProduct_coeff_175
  recurrence2ExceptionalProduct_coeff_176
  recurrence2ExceptionalProduct_coeff_177
  recurrence2ExceptionalProduct_coeff_178
  recurrence2ExceptionalProduct_coeff_179
  recurrence2ExceptionalProduct_coeff_180
  recurrence2ExceptionalProduct_coeff_181
  recurrence2ExceptionalProduct_coeff_182
  recurrence2ExceptionalProduct_coeff_183
  recurrence2ExceptionalProduct_coeff_184
  recurrence2ExceptionalProduct_coeff_185
  recurrence2ExceptionalProduct_coeff_186
  recurrence2ExceptionalProduct_coeff_187
  recurrence2ExceptionalProduct_coeff_188
  recurrence2ExceptionalProduct_coeff_189
  recurrence2ExceptionalProduct_coeff_190
  recurrence2ExceptionalProduct_coeff_191
  recurrence2ExceptionalProduct_coeff_192
  recurrence2ExceptionalProduct_coeff_193
  recurrence2C3_coeff_0
  recurrence2C3_coeff_1
  recurrence2C3_coeff_2
  recurrence2C3_coeff_3
  recurrence2C3_coeff_4
  recurrence2C3_coeff_5
  recurrence2C3_coeff_6
  recurrence2C3_coeff_7
  recurrence2C3_coeff_8
  recurrence2C3_coeff_9
  recurrence2C3_coeff_10
  recurrence2C3_coeff_11
  recurrence2C3_coeff_12
  recurrence2C3_coeff_13
  recurrence2C3_coeff_14
  recurrence2C3_coeff_15
  recurrence2C3_coeff_16
  recurrence2C3_coeff_17
  recurrence2C3_coeff_18
  recurrence2C3_coeff_19
  recurrence2C3_coeff_20
  recurrence2C3_coeff_21
  recurrence2C3_coeff_22
  recurrence2C3_coeff_23
  recurrence2C3_coeff_24
  recurrence2C3_coeff_25
  recurrence2C3_coeff_26
  recurrence2C3_coeff_27
  recurrence2C3_coeff_28
  recurrence2C3_coeff_29
  recurrence2C3_coeff_30
  recurrence2C3_coeff_31
  recurrence2C3_coeff_32
  recurrence2C3_coeff_33
  recurrence2C3_coeff_34
  recurrence2C3_coeff_35
  recurrence2C3_coeff_36
  recurrence2C3_coeff_37
  recurrence2C3_coeff_38
  recurrence2C3_coeff_39
  recurrence2C3_coeff_40
  recurrence2C3_coeff_41
  recurrence2C3_coeff_42
  recurrence2C3_coeff_43
  recurrence2C3_coeff_44
  recurrence2C3_coeff_45
  recurrence2C3_coeff_46
  recurrence2C3_coeff_47
  recurrence2C3_coeff_48
  recurrence2C3_coeff_49
  recurrence2C3_coeff_50
  recurrence2C3_coeff_51
  recurrence2C3_coeff_52
  recurrence2C3_coeff_53
  recurrence2C3_coeff_54
  recurrence2C3_coeff_55
  recurrence2C3_coeff_56
  recurrence2C3_coeff_57
  recurrence2C3_coeff_58
  recurrence2C3_coeff_59
  recurrence2C3_coeff_60
  recurrence2C3_coeff_61
  recurrence2C3_coeff_62
  recurrence2C3_coeff_63
  recurrence2C3_coeff_64
  recurrence2C3_coeff_65
  recurrence2C3_coeff_66
  recurrence2C3_coeff_67
  recurrence2C3_coeff_68
  recurrence2C3_coeff_69
  recurrence2C3_coeff_70
  recurrence2C3_coeff_71
  recurrence2C3_coeff_72
  recurrence2C3_coeff_73
  recurrence2C3_coeff_74
  recurrence2C3_coeff_75
  recurrence2C3_coeff_76
  recurrence2C3_coeff_77
  recurrence2C3_coeff_78
  recurrence2C3_coeff_79
  recurrence2C3_coeff_80
  recurrence2C3_coeff_81
  recurrence2C3_coeff_82
  recurrence2C3_coeff_83
  recurrence2C3_coeff_84
  recurrence2C3_coeff_85
  recurrence2C3_coeff_86
  recurrence2C3_coeff_87
  recurrence2C3_coeff_88
  recurrence2C3_coeff_89
  recurrence2C3_coeff_90
  recurrence2C3_coeff_91
  recurrence2C3_coeff_92
  recurrence2C3_coeff_93
  recurrence2C3_coeff_94
  recurrence2C3_coeff_95
  recurrence2C3_coeff_96
  recurrence2C3_coeff_97
  recurrence2C3_coeff_98
  recurrence2C3_coeff_99
  recurrence2C3_coeff_100
  recurrence2C3_coeff_101
  recurrence2C3_coeff_102
  recurrence2C3_coeff_103
  recurrence2C3_coeff_104
  recurrence2C3_coeff_105
  recurrence2C3_coeff_106
  recurrence2C3_coeff_107
  recurrence2C3_coeff_108
  recurrence2C3_coeff_109
  recurrence2C3_coeff_110
  recurrence2C3_coeff_111
  recurrence2C3_coeff_112
  recurrence2C3_coeff_113
  recurrence2C3_coeff_114
  recurrence2C3_coeff_115
  recurrence2C3_coeff_116
  recurrence2C3_coeff_117
  recurrence2C3_coeff_118
  recurrence2C3_coeff_119
  recurrence2C3_coeff_120
  recurrence2C3_coeff_121
  recurrence2C3_coeff_122
  recurrence2C3_coeff_123
  recurrence2C3_coeff_124
  recurrence2C3_coeff_125
  recurrence2C3_coeff_126
  recurrence2C3_coeff_127
  recurrence2C3_coeff_128
  recurrence2C3_coeff_129
  recurrence2C3_coeff_130
  recurrence2C3_coeff_131
  recurrence2C3_coeff_132
  recurrence2C3_coeff_133
  recurrence2C3_coeff_134
  recurrence2C3_coeff_135
  recurrence2C3_coeff_136
  recurrence2C3_coeff_137
  recurrence2C3_coeff_138
  recurrence2C3_coeff_139
  recurrence2C3_coeff_140
  recurrence2C3_coeff_141
  recurrence2C3_coeff_142
  recurrence2C3_coeff_143
  recurrence2C3_coeff_144
  recurrence2C3_coeff_145
  recurrence2C3_coeff_146
  recurrence2C3_coeff_147
  recurrence2C3_coeff_148
  recurrence2C3_coeff_149
  recurrence2C3_coeff_150
  recurrence2C3_coeff_151
  recurrence2C3_coeff_152
  recurrence2C3_coeff_153
  recurrence2C3_coeff_154
  recurrence2C3_coeff_155
  recurrence2C3_coeff_156
  recurrence2C3_coeff_157
  recurrence2C3_coeff_158
  recurrence2C3_coeff_159
  recurrence2C3_coeff_160
  recurrence2C3_coeff_161
  recurrence2C3_coeff_162
  recurrence2C3_coeff_163
  recurrence2C3_coeff_164
  recurrence2C3_coeff_165
  recurrence2C3_coeff_166
  recurrence2C3_coeff_167
  recurrence2C3_coeff_168
  recurrence2C3_coeff_169
  recurrence2C3_coeff_170
  recurrence2C3_coeff_171
  recurrence2C3_coeff_172
  recurrence2C3_coeff_173
  recurrence2C3_coeff_174
  recurrence2C3_coeff_175
  recurrence2C3_coeff_176
  recurrence2C3_coeff_177
  recurrence2C3_coeff_178
  recurrence2C3_coeff_179
  recurrence2C3_coeff_180
  recurrence2C3_coeff_181
  recurrence2C3_coeff_182

private theorem recurrence2Scalar3Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (231 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_231 :
    recurrence2Scalar3Exceptional.coeff 231 =
      (((12957158075663960194200655702434773035177256410387717411022 * 10 ^ 70 +
        9655032796159165635654766297170458392788150935988452571311541631915701) * 10 ^ 70 +
        2077655828254162430764270247922285350974599881089465685090124091384085) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 49 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 17 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (232 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_232 :
    recurrence2Scalar3Exceptional.coeff 232 =
      (((2224019137007319522126086341697327339042235107858205999736 * 10 ^ 70 +
        0586746372493717633022541609600136316225811005366102459891736366527847) * 10 ^ 70 +
        7469299044689618145485223902460947610185133016491097730680420472165299) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 50 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 16 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (233 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_233 :
    recurrence2Scalar3Exceptional.coeff 233 =
      -(((9356815670274335496880946201465161693926779918718387413495 * 10 ^ 70 +
        9765191792840187349735496804199809263599633791617992848376996131832868) * 10 ^ 70 +
        7427844212445746890947444703546136030294244145451018535368465464181749) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 51 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 15 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (234 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_234 :
    recurrence2Scalar3Exceptional.coeff 234 =
      (((11105152343626154668045888774375321300956600145965534893986 * 10 ^ 70 +
        2250818916725213695628128427486505227771011797582140903556110616180129) * 10 ^ 70 +
        9290150480274792020267839016193356034464011094533215390451307660279276) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 52 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 14 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (235 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_235 :
    recurrence2Scalar3Exceptional.coeff 235 =
      -(((9860173595990458143173182506872034452476137251360596358241 * 10 ^ 70 +
        0188841321093815122605597055409418336979163916072609011048014260261227) * 10 ^ 70 +
        9675589986441578905830508204059937434902105800394811196310216027615491) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 53 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 13 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (236 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_236 :
    recurrence2Scalar3Exceptional.coeff 236 =
      (((7410966626328815223509944617131441708448292492839557825405 * 10 ^ 70 +
        7040494963897801866620539416552227447095831880466125138056809195517200) * 10 ^ 70 +
        3574285541250808888587354553367972740244451193354698490224702325990100) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 54 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 12 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (237 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_237 :
    recurrence2Scalar3Exceptional.coeff 237 =
      -(((4878326235987292619531224938942710714070893764497675898663 * 10 ^ 70 +
        7090042421035727935908720771314538001239479611175468193342196722925417) * 10 ^ 70 +
        7775650309650609594788201999155011080190746432945506105245869561705373) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 55 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 11 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (238 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_238 :
    recurrence2Scalar3Exceptional.coeff 238 =
      (((2816238961166758967911856083502705730543824223892373065097 * 10 ^ 70 +
        4088058255452708664896806041171209164103600245690212958141882660265038) * 10 ^ 70 +
        4774884009985873896417861684612239299719510228139492417588583834228058) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 56 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 10 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (239 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_239 :
    recurrence2Scalar3Exceptional.coeff 239 =
      -(((1384736432242239428054842961091859187483851124289373532333 * 10 ^ 70 +
        9995219006846068915691811084302865748823339062727460932420015932784035) * 10 ^ 70 +
        7422780779353285188424150619493131028357776479165793169378362265502958) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 57 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 9 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (240 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_240 :
    recurrence2Scalar3Exceptional.coeff 240 =
      (((522381708162302907850482450629921399932114228093917011016 * 10 ^ 70 +
        6572738653441974839879978861153066923322199361227854136311233651540778) * 10 ^ 70 +
        6538793663035042241722485710099465172604962276178322322265879985424031) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 58 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 8 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (241 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_241 :
    recurrence2Scalar3Exceptional.coeff 241 =
      -(((79295232486217077589317082407215067683073883710740732854 * 10 ^ 70 +
        2436741099732080718685593285713485544840561197482231428654241982726441) * 10 ^ 70 +
        0353976610064903818598285788095217796977213346793520962443956140764339) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 59 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 7 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (242 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_242 :
    recurrence2Scalar3Exceptional.coeff 242 =
      -(((100289344383751128713864617161448814315573168443310813465 * 10 ^ 70 +
        4304815453609453516655995565600580822064215843331468018710342864840807) * 10 ^ 70 +
        5922954222489996351060547602861054011279211277594589230687921081108507) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 60 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 6 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (243 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_243 :
    recurrence2Scalar3Exceptional.coeff 243 =
      (((139171282482993687715507559274493978595627818616944638940 * 10 ^ 70 +
        9874812294118946048617418029431427901023825783692633545194526605344396) * 10 ^ 70 +
        8140308493189715193492366102171908332898009617425225829555307397948161) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 61 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 5 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (244 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_244 :
    recurrence2Scalar3Exceptional.coeff 244 =
      -(((117900048618193484901483453358293991809591480209934271774 * 10 ^ 70 +
        2699688023177504178160525092030739429657822905456219584349275810586901) * 10 ^ 70 +
        3556267283031590338154421304714362264046627457304356066026789629420845) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 62 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 4 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (245 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_245 :
    recurrence2Scalar3Exceptional.coeff 245 =
      (((80982394731794698860555308145301562760685944398100540962 * 10 ^ 70 +
        8157892269386699396849412547297378346372792753933482525895568534585158) * 10 ^ 70 +
        4939115561310296072344458194992436297860881576056119723242633762721960) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 63 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 3 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (246 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_246 :
    recurrence2Scalar3Exceptional.coeff 246 =
      -(((48233804573770303145734944093112835354328753191664593277 * 10 ^ 70 +
        4410559790119041216932526715406538375906668615559081785010055730022638) * 10 ^ 70 +
        1469065141314339345450891657195056003799769266464013180672253541188244) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 64 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 2 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (247 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_247 :
    recurrence2Scalar3Exceptional.coeff 247 =
      (((25405861019127677275238671800048889634368734347941046043 * 10 ^ 70 +
        8542973252132911220663606268423032099660332128221984959455739497396186) * 10 ^ 70 +
        5108556031718656131782626007536855541828769899813570979700111633849359) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 65 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 1 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (248 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_248 :
    recurrence2Scalar3Exceptional.coeff 248 =
      -(((11793042466377658825544099950917618001796188684318108329 * 10 ^ 70 +
        7582001559468195832033263325682549718082408422125742863074706611619696) * 10 ^ 70 +
        2744782306454290698241620425453400866619130199789593337406739672162065) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 66 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (249 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_249 :
    recurrence2Scalar3Exceptional.coeff 249 =
      (((4682331102484454763868582250290960337968564619937820245 * 10 ^ 70 +
        1167561196790125069050177233956792136657560630457051237777025769261167) * 10 ^ 70 +
        1492086758212303970419727224723110795209029384255760572923792336453742) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 67 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 31 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (250 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_250 :
    recurrence2Scalar3Exceptional.coeff 250 =
      -(((1442480701673880241765693588652322439534419879521200960 * 10 ^ 70 +
        0537889954576602993128111781957572000030261237740681178039739929848126) * 10 ^ 70 +
        5670969460707095572314772254918662919605033939999277664807352416619746) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 68 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 30 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (251 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_251 :
    recurrence2Scalar3Exceptional.coeff 251 =
      (((201287531205853770649235532353396230888976004895467392 * 10 ^ 70 +
        9048871306540834329347061156573503581711341932789848160362316015884495) * 10 ^ 70 +
        3779049286635973577598564534464908852014480642397441072187100487467491) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 69 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 29 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (252 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_252 :
    recurrence2Scalar3Exceptional.coeff 252 =
      (((149978173085476751588289920302515041538963788334592357 * 10 ^ 70 +
        0996875448061073096184530191630647820842339309982172600123971770975864) * 10 ^ 70 +
        2398754446758113380514128179360185592525548620855510737686976751792167) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 70 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 28 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (253 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_253 :
    recurrence2Scalar3Exceptional.coeff 253 =
      -(((175001788676926896678071638684588452977185516001718886 * 10 ^ 70 +
        3545406785781641460682957526243772679794918349073417364528547523652014) * 10 ^ 70 +
        7095612946404690741978300797455941835406110496518249533589230507567131) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 71 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 27 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (254 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_254 :
    recurrence2Scalar3Exceptional.coeff 254 =
      (((117755291597731359401463120722276571251344861881567581 * 10 ^ 70 +
        6338473832289138737561577667976643371562638828660341866958756103731559) * 10 ^ 70 +
        2121764129984372474811028855554007110220402904271372205686227183328099) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 72 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 26 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (255 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_255 :
    recurrence2Scalar3Exceptional.coeff 255 =
      -(((62889207455403801776776645308637491741399850682126519 * 10 ^ 70 +
        9806999769913343586224013817253981672524859239174318131792126133568920) * 10 ^ 70 +
        6762271174156720806288613789788429660319697367700850684688893309587854) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 73 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 25 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (256 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_256 :
    recurrence2Scalar3Exceptional.coeff 256 =
      (((28459680651774683243112492699947470410780718952025208 * 10 ^ 70 +
        2320727832169359459251356693625858979137081063135412877224027354415126) * 10 ^ 70 +
        8868926619848487547134354240487004319496491472816895027889432250787249) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 74 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 24 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (257 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_257 :
    recurrence2Scalar3Exceptional.coeff 257 =
      -(((10981355822420863484832390005185582540112696111148474 * 10 ^ 70 +
        2688509447714166877431956959878169314499527318124684133151281914323384) * 10 ^ 70 +
        7927670189583712008755033469896951921555387246229229005266217741708680) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 75 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 23 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (258 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_258 :
    recurrence2Scalar3Exceptional.coeff 258 =
      (((3467655162679000879683393917486636709355607315793633 * 10 ^ 70 +
        9062487264663038974960226505975044517593166719839081824146107655200838) * 10 ^ 70 +
        1201652053655212643920339767581492920297797120530413661580252412097977) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 76 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 22 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (259 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_259 :
    recurrence2Scalar3Exceptional.coeff 259 =
      -(((753021961240643154775853298816984738277832643698946 * 10 ^ 70 +
        2897830841203948010700417213316562060416675453185269327872472521146648) * 10 ^ 70 +
        8566654981905775203547749387610599210171111294088290905083357048583527) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 77 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 21 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (260 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_260 :
    recurrence2Scalar3Exceptional.coeff 260 =
      -(((13680124187573761531654813352501682809021210237681 * 10 ^ 70 +
        4752631357836435802955852138602027782994889993995727854744109742869400) * 10 ^ 70 +
        0605996386075663686827864976116847588487018712283148742524798277610504) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 78 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 20 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (261 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_261 :
    recurrence2Scalar3Exceptional.coeff 261 =
      (((130905704340158568957134224920511778054773199919525 * 10 ^ 70 +
        8730060586301257124552333488394311695384394277561190047936440862578240) * 10 ^ 70 +
        0802519577640067896326014217717002140821295082929539210465573911481028) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 79 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 19 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_262 :
    recurrence2Scalar3Exceptional.coeff 262 =
      -(((92030443608458536342994974377209726549420893154155 * 10 ^ 70 +
        9208445344927608664060677690423594389360640981173805863287358164671974) * 10 ^ 70 +
        6724121996936426927050653698463457196407847415024664247891973423093613) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 80 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 18 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient3.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C3_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient3.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Exceptional_coeff_263 :
    recurrence2Scalar3Exceptional.coeff 263 =
      (((45427548110480653247833547401705963309787422988877 * 10 ^ 70 +
        3926118190338373163206279105435205676317513435989647055722825154940343) * 10 ^ 70 +
        2667991416444846425981780377809379319513467617897739679541918598773458) : ℚ) := by
  unfold recurrence2Scalar3Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 81 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 17 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Exceptional_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
