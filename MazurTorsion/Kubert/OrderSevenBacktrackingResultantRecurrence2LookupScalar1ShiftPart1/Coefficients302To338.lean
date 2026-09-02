/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ShiftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B0_coeff_0
  recurrence2B0_coeff_1
  recurrence2B0_coeff_2
  recurrence2B0_coeff_3
  recurrence2B0_coeff_4
  recurrence2B0_coeff_5
  recurrence2B0_coeff_6
  recurrence2B0_coeff_7
  recurrence2B0_coeff_8
  recurrence2B0_coeff_9
  recurrence2B0_coeff_10
  recurrence2B0_coeff_11
  recurrence2B0_coeff_12
  recurrence2B0_coeff_13
  recurrence2B0_coeff_14
  recurrence2B0_coeff_15
  recurrence2B0_coeff_16
  recurrence2B0_coeff_17
  recurrence2B0_coeff_18
  recurrence2B0_coeff_19
  recurrence2B0_coeff_20
  recurrence2B0_coeff_21
  recurrence2B0_coeff_22
  recurrence2B0_coeff_23
  recurrence2B0_coeff_24
  recurrence2B0_coeff_25
  recurrence2B0_coeff_26
  recurrence2B0_coeff_27
  recurrence2B0_coeff_28
  recurrence2B0_coeff_29
  recurrence2B0_coeff_30
  recurrence2B0_coeff_31
  recurrence2B0_coeff_32
  recurrence2B0_coeff_33
  recurrence2B0_coeff_34
  recurrence2B0_coeff_35
  recurrence2B0_coeff_36
  recurrence2B0_coeff_37
  recurrence2B0_coeff_38
  recurrence2B0_coeff_39
  recurrence2B0_coeff_40
  recurrence2B0_coeff_41
  recurrence2B0_coeff_42
  recurrence2B0_coeff_43
  recurrence2B0_coeff_44
  recurrence2B0_coeff_45
  recurrence2B0_coeff_46
  recurrence2B0_coeff_47
  recurrence2B0_coeff_48
  recurrence2B0_coeff_49
  recurrence2B0_coeff_50
  recurrence2B0_coeff_51
  recurrence2B0_coeff_52
  recurrence2B0_coeff_53
  recurrence2B0_coeff_54
  recurrence2B0_coeff_55
  recurrence2B0_coeff_56
  recurrence2B0_coeff_57
  recurrence2B0_coeff_58
  recurrence2B0_coeff_59
  recurrence2B0_coeff_60
  recurrence2B0_coeff_61
  recurrence2B0_coeff_62
  recurrence2B0_coeff_63
  recurrence2B0_coeff_64
  recurrence2B0_coeff_65
  recurrence2B0_coeff_66
  recurrence2B0_coeff_67
  recurrence2B0_coeff_68
  recurrence2B0_coeff_69
  recurrence2B0_coeff_70
  recurrence2B0_coeff_71
  recurrence2B0_coeff_72
  recurrence2B0_coeff_73
  recurrence2B0_coeff_74
  recurrence2B0_coeff_75
  recurrence2B0_coeff_76
  recurrence2B0_coeff_77
  recurrence2B0_coeff_78
  recurrence2B0_coeff_79
  recurrence2B0_coeff_80
  recurrence2B0_coeff_81
  recurrence2B0_coeff_82
  recurrence2B0_coeff_83
  recurrence2B0_coeff_84
  recurrence2B0_coeff_85
  recurrence2B0_coeff_86
  recurrence2B0_coeff_87
  recurrence2B0_coeff_88
  recurrence2B0_coeff_89
  recurrence2B0_coeff_90
  recurrence2B0_coeff_91
  recurrence2B0_coeff_92
  recurrence2B0_coeff_93
  recurrence2B0_coeff_94
  recurrence2B0_coeff_95
  recurrence2B0_coeff_96
  recurrence2B0_coeff_97
  recurrence2B0_coeff_98
  recurrence2B0_coeff_99
  recurrence2B0_coeff_100
  recurrence2B0_coeff_101
  recurrence2B0_coeff_102
  recurrence2B0_coeff_103
  recurrence2B0_coeff_104
  recurrence2B0_coeff_105
  recurrence2B0_coeff_106
  recurrence2B0_coeff_107
  recurrence2B0_coeff_108
  recurrence2B0_coeff_109
  recurrence2B0_coeff_110
  recurrence2B0_coeff_111
  recurrence2B0_coeff_112
  recurrence2B0_coeff_113
  recurrence2B0_coeff_114
  recurrence2B0_coeff_115
  recurrence2B0_coeff_116
  recurrence2B0_coeff_117
  recurrence2B0_coeff_118
  recurrence2B0_coeff_119
  recurrence2B0_coeff_120
  recurrence2B0_coeff_121
  recurrence2B0_coeff_122
  recurrence2B0_coeff_123
  recurrence2B0_coeff_124
  recurrence2B0_coeff_125
  recurrence2B0_coeff_126
  recurrence2B0_coeff_127
  recurrence2B0_coeff_128
  recurrence2B0_coeff_129
  recurrence2B0_coeff_130
  recurrence2B0_coeff_131
  recurrence2B0_coeff_132
  recurrence2B0_coeff_133
  recurrence2B0_coeff_134
  recurrence2B0_coeff_135
  recurrence2B0_coeff_136
  recurrence2B0_coeff_137
  recurrence2B0_coeff_138
  recurrence2B0_coeff_139
  recurrence2B0_coeff_140
  recurrence2B0_coeff_141
  recurrence2B0_coeff_142
  recurrence2B0_coeff_143
  recurrence2B0_coeff_144
  recurrence2B0_coeff_145
  recurrence2B0_coeff_146
  recurrence2B0_coeff_147
  recurrence2B0_coeff_148
  recurrence2B0_coeff_149
  recurrence2B0_coeff_150
  recurrence2B0_coeff_151
  recurrence2B0_coeff_152
  recurrence2B0_coeff_153
  recurrence2B0_coeff_154
  recurrence2B5A6_coeff_0
  recurrence2B5A6_coeff_1
  recurrence2B5A6_coeff_2
  recurrence2B5A6_coeff_3
  recurrence2B5A6_coeff_4
  recurrence2B5A6_coeff_5
  recurrence2B5A6_coeff_6
  recurrence2B5A6_coeff_7
  recurrence2B5A6_coeff_8
  recurrence2B5A6_coeff_9
  recurrence2B5A6_coeff_10
  recurrence2B5A6_coeff_11
  recurrence2B5A6_coeff_12
  recurrence2B5A6_coeff_13
  recurrence2B5A6_coeff_14
  recurrence2B5A6_coeff_15
  recurrence2B5A6_coeff_16
  recurrence2B5A6_coeff_17
  recurrence2B5A6_coeff_18
  recurrence2B5A6_coeff_19
  recurrence2B5A6_coeff_20
  recurrence2B5A6_coeff_21
  recurrence2B5A6_coeff_22
  recurrence2B5A6_coeff_23
  recurrence2B5A6_coeff_24
  recurrence2B5A6_coeff_25
  recurrence2B5A6_coeff_26
  recurrence2B5A6_coeff_27
  recurrence2B5A6_coeff_28
  recurrence2B5A6_coeff_29
  recurrence2B5A6_coeff_30
  recurrence2B5A6_coeff_31
  recurrence2B5A6_coeff_32
  recurrence2B5A6_coeff_33
  recurrence2B5A6_coeff_34
  recurrence2B5A6_coeff_35
  recurrence2B5A6_coeff_36
  recurrence2B5A6_coeff_37
  recurrence2B5A6_coeff_38
  recurrence2B5A6_coeff_39
  recurrence2B5A6_coeff_40
  recurrence2B5A6_coeff_41
  recurrence2B5A6_coeff_42
  recurrence2B5A6_coeff_43
  recurrence2B5A6_coeff_44
  recurrence2B5A6_coeff_45
  recurrence2B5A6_coeff_46
  recurrence2B5A6_coeff_47
  recurrence2B5A6_coeff_48
  recurrence2B5A6_coeff_49
  recurrence2B5A6_coeff_50
  recurrence2B5A6_coeff_51
  recurrence2B5A6_coeff_52
  recurrence2B5A6_coeff_53
  recurrence2B5A6_coeff_54
  recurrence2B5A6_coeff_55
  recurrence2B5A6_coeff_56
  recurrence2B5A6_coeff_57
  recurrence2B5A6_coeff_58
  recurrence2B5A6_coeff_59
  recurrence2B5A6_coeff_60
  recurrence2B5A6_coeff_61
  recurrence2B5A6_coeff_62
  recurrence2B5A6_coeff_63
  recurrence2B5A6_coeff_64
  recurrence2B5A6_coeff_65
  recurrence2B5A6_coeff_66
  recurrence2B5A6_coeff_67
  recurrence2B5A6_coeff_68
  recurrence2B5A6_coeff_69
  recurrence2B5A6_coeff_70
  recurrence2B5A6_coeff_71
  recurrence2B5A6_coeff_72
  recurrence2B5A6_coeff_73
  recurrence2B5A6_coeff_74
  recurrence2B5A6_coeff_75
  recurrence2B5A6_coeff_76
  recurrence2B5A6_coeff_77
  recurrence2B5A6_coeff_78
  recurrence2B5A6_coeff_79
  recurrence2B5A6_coeff_80
  recurrence2B5A6_coeff_81
  recurrence2B5A6_coeff_82
  recurrence2B5A6_coeff_83
  recurrence2B5A6_coeff_84
  recurrence2B5A6_coeff_85
  recurrence2B5A6_coeff_86
  recurrence2B5A6_coeff_87
  recurrence2B5A6_coeff_88
  recurrence2B5A6_coeff_89
  recurrence2B5A6_coeff_90
  recurrence2B5A6_coeff_91
  recurrence2B5A6_coeff_92
  recurrence2B5A6_coeff_93
  recurrence2B5A6_coeff_94
  recurrence2B5A6_coeff_95
  recurrence2B5A6_coeff_96
  recurrence2B5A6_coeff_97
  recurrence2B5A6_coeff_98
  recurrence2B5A6_coeff_99
  recurrence2B5A6_coeff_100
  recurrence2B5A6_coeff_101
  recurrence2B5A6_coeff_102
  recurrence2B5A6_coeff_103
  recurrence2B5A6_coeff_104
  recurrence2B5A6_coeff_105
  recurrence2B5A6_coeff_106
  recurrence2B5A6_coeff_107
  recurrence2B5A6_coeff_108
  recurrence2B5A6_coeff_109
  recurrence2B5A6_coeff_110
  recurrence2B5A6_coeff_111
  recurrence2B5A6_coeff_112
  recurrence2B5A6_coeff_113
  recurrence2B5A6_coeff_114
  recurrence2B5A6_coeff_115
  recurrence2B5A6_coeff_116
  recurrence2B5A6_coeff_117
  recurrence2B5A6_coeff_118
  recurrence2B5A6_coeff_119
  recurrence2B5A6_coeff_120
  recurrence2B5A6_coeff_121
  recurrence2B5A6_coeff_122
  recurrence2B5A6_coeff_123
  recurrence2B5A6_coeff_124
  recurrence2B5A6_coeff_125
  recurrence2B5A6_coeff_126
  recurrence2B5A6_coeff_127
  recurrence2B5A6_coeff_128
  recurrence2B5A6_coeff_129
  recurrence2B5A6_coeff_130
  recurrence2B5A6_coeff_131
  recurrence2B5A6_coeff_132
  recurrence2B5A6_coeff_133
  recurrence2B5A6_coeff_134
  recurrence2B5A6_coeff_135
  recurrence2B5A6_coeff_136
  recurrence2B5A6_coeff_137
  recurrence2B5A6_coeff_138
  recurrence2B5A6_coeff_139
  recurrence2B5A6_coeff_140
  recurrence2B5A6_coeff_141
  recurrence2B5A6_coeff_142
  recurrence2B5A6_coeff_143
  recurrence2B5A6_coeff_144
  recurrence2B5A6_coeff_145
  recurrence2B5A6_coeff_146
  recurrence2B5A6_coeff_147
  recurrence2B5A6_coeff_148
  recurrence2B5A6_coeff_149
  recurrence2B5A6_coeff_150
  recurrence2B5A6_coeff_151
  recurrence2B5A6_coeff_152
  recurrence2B5A6_coeff_153
  recurrence2B5A6_coeff_154
  recurrence2B5A6_coeff_155
  recurrence2B5A6_coeff_156
  recurrence2B5A6_coeff_157
  recurrence2B5A6_coeff_158
  recurrence2B5A6_coeff_159
  recurrence2B5A6_coeff_160
  recurrence2B5A6_coeff_161
  recurrence2B5A6_coeff_162
  recurrence2B5A6_coeff_163
  recurrence2B5A6_coeff_164
  recurrence2B5A6_coeff_165
  recurrence2B5A6_coeff_166
  recurrence2B5A6_coeff_167
  recurrence2B5A6_coeff_168
  recurrence2B5A6_coeff_169
  recurrence2B5A6_coeff_170
  recurrence2B5A6_coeff_171
  recurrence2B5A6_coeff_172
  recurrence2B5A6_coeff_173
  recurrence2B5A6_coeff_174
  recurrence2B5A6_coeff_175
  recurrence2B5A6_coeff_176
  recurrence2B5A6_coeff_177
  recurrence2B5A6_coeff_178
  recurrence2B5A6_coeff_179
  recurrence2B5A6_coeff_180
  recurrence2B5A6_coeff_181
  recurrence2B5A6_coeff_182
  recurrence2B5A6_coeff_183
  recurrence2B5A6_coeff_184
  recurrence2B5A6_coeff_185
  recurrence2B5A6_coeff_186
  recurrence2B5A6_coeff_187
  recurrence2B5A6_coeff_188
  recurrence2B5A6_coeff_189
  recurrence2B5A6_coeff_190
  recurrence2B5A6_coeff_191
  recurrence2B5A6_coeff_192
  recurrence2B5A6_coeff_193
  recurrence2B5A6_coeff_194
  recurrence2B5A6_coeff_195
  recurrence2B5A6_coeff_196
  recurrence2B5A6_coeff_197
  recurrence2B5A6_coeff_198
  recurrence2B5A6_coeff_199
  recurrence2B5A6_coeff_200
  recurrence2B5A6_coeff_201
  recurrence2B5A6_coeff_202
  recurrence2B5A6_coeff_203
  recurrence2B5A6_coeff_204
  recurrence2B5A6_coeff_205
  recurrence2B5A6_coeff_206
  recurrence2B5A6_coeff_207
  recurrence2B5A6_coeff_208
  recurrence2B5A6_coeff_209
  recurrence2B5A6_coeff_210
  recurrence2B5A6_coeff_211
  recurrence2B5A6_coeff_212
  recurrence2B5A6_coeff_213
  recurrence2B5A6_coeff_214
  recurrence2B5A6_coeff_215
  recurrence2B5A6_coeff_216
  recurrence2B5A6_coeff_217
  recurrence2B5A6_coeff_218
  recurrence2B5A6_coeff_219
  recurrence2B5A6_coeff_220
  recurrence2B5A6_coeff_221
  recurrence2B5A6_coeff_222
  recurrence2B5A6_coeff_223
  recurrence2B5A6_coeff_224
  recurrence2B5A6_coeff_225
  recurrence2B5A6_coeff_226
  recurrence2B5A6_coeff_227
  recurrence2B5A6_coeff_228
  recurrence2B5A6_coeff_229

private theorem recurrence2Scalar1Shift_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (302 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_302 :
    recurrence2Scalar1Shift.coeff 302 =
      (((11768614193698311528134403182438696648358821370790966 * 10 ^ 70 +
        4770417993940612768324519981365764337527632920939574380700894415198094) * 10 ^ 70 +
        6106765592307693956030765044488659624065805667657992066274386234585626) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 73 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 18 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (303 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_303 :
    recurrence2Scalar1Shift.coeff 303 =
      (((465107340803703962570563186731469919100574370406288 * 10 ^ 70 +
        2805079594533635465507429060330563706477462558424602603436048115114193) * 10 ^ 70 +
        6344323988483337900545811990086698458323777873783562830369135983768533) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 74 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 17 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (304 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_304 :
    recurrence2Scalar1Shift.coeff 304 =
      -(((668042274050664535972283290080237798786147296656085 * 10 ^ 70 +
        5747514629319695963330959843330630666092025102960386594543959600756446) * 10 ^ 70 +
        1525709074749550721670437304598977122325687262542087434409054231354008) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 75 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 16 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (305 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_305 :
    recurrence2Scalar1Shift.coeff 305 =
      (((229485106711896216183207230144105176496357581387539 * 10 ^ 70 +
        1713264333560305676488027034235463898650141253482771221258244268882433) * 10 ^ 70 +
        7763367800475283362755847009203923826554690129789069672081546376463812) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 76 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 15 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (306 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_306 :
    recurrence2Scalar1Shift.coeff 306 =
      -(((57831479255666939235005363757725957567855487078439 * 10 ^ 70 +
        2253738984155829449509733300577851303607790742297620581205692427551402) * 10 ^ 70 +
        9957260764275471689303067790060909130189504914786708838890368610288565) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 77 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 14 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (307 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_307 :
    recurrence2Scalar1Shift.coeff 307 =
      (((12186347333044047729412995292842714970865600445245 * 10 ^ 70 +
        9490268038839200078288661343960865541509757291236841389776114320501032) * 10 ^ 70 +
        7039871288385634902408644249949946070512386144314412815855707232465487) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 78 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 13 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (308 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_308 :
    recurrence2Scalar1Shift.coeff 308 =
      -(((2231013517870218208436648741647452838816585225910 * 10 ^ 70 +
        9693553401855903926995899555681157624773765208192601553816860316308801) * 10 ^ 70 +
        3071916941543320843894425994327188385912127043354919460002713991808227) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 79 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (309 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_309 :
    recurrence2Scalar1Shift.coeff 309 =
      (((357875636814139279111330973776649441186752110910 * 10 ^ 70 +
        3636048190404150051902073441047475668533926645954519623137957404841847) * 10 ^ 70 +
        5139699151394950019287615750819412905619226035780215506900743732754594) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 80 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 11 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (310 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_310 :
    recurrence2Scalar1Shift.coeff 310 =
      -(((49708368549198023253243552112830073223183831162 * 10 ^ 70 +
        3551646349111922686402490372547626837156462731793072749629810889039100) * 10 ^ 70 +
        3588218813418715662511716037019667926488466722705003809306621005875646) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 81 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 10 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (311 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_311 :
    recurrence2Scalar1Shift.coeff 311 =
      (((5719958320353379572832362104056911457819354838 * 10 ^ 70 +
        4170865509269368021097514658327691885472177826510492976469460849199957) * 10 ^ 70 +
        7732074637414897178819147535692099993599521975255988157742928911003889) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 82 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 9 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (312 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_312 :
    recurrence2Scalar1Shift.coeff 312 =
      -(((467954262427806790775108091483839505744843276 * 10 ^ 70 +
        3351182241226921170997561062270667730126265309335730083668499039967528) * 10 ^ 70 +
        1540010383055051807720765087094718648846744198223739454606978364590683) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 83 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 8 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (313 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_313 :
    recurrence2Scalar1Shift.coeff 313 =
      (((3693387992360813562468793253713422383847100 * 10 ^ 70 +
        4521323087889814335394713440466227636635130635133380292762054584920183) * 10 ^ 70 +
        2879089806502897534865617704442804819568882812679751863520847331085467) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 84 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 7 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (314 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_314 :
    recurrence2Scalar1Shift.coeff 314 =
      (((8623399172883070306665617037414461484170725 * 10 ^ 70 +
        3129780912644575180342862174242501127043710344714122948051323673622796) * 10 ^ 70 +
        7486675361560932254887022068716983398123946702530766289775558445956070) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 85 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 6 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (315 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_315 :
    recurrence2Scalar1Shift.coeff 315 =
      -(((2296511777754335313980700361492590470566869 * 10 ^ 70 +
        4916696286587129413519275637971607454087150835614796147308408220964156) * 10 ^ 70 +
        5138520141784576847983709003572974872373928835461813804752165056717550) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 86 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 5 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (316 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_316 :
    recurrence2Scalar1Shift.coeff 316 =
      (((417484896367157600536149970914955346791181 * 10 ^ 70 +
        5380350995584689758395284819927467122111806047640406658522759763259156) * 10 ^ 70 +
        6312790417505149927176933567052948787880578461040821112519873162762848) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 87 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 4 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (317 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_317 :
    recurrence2Scalar1Shift.coeff 317 =
      -(((61790203652997031733362963593319708936715 * 10 ^ 70 +
        7993563452780448004024636930913552891978010111078595211139029794082893) * 10 ^ 70 +
        2365796985286768374694028628104342605024753083626785155084292175976270) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 88 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 3 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (318 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_318 :
    recurrence2Scalar1Shift.coeff 318 =
      (((7746139565487694409938008089488164996520 * 10 ^ 70 +
        9732553142790287899644664038217209223962512259654522921611730702202785) * 10 ^ 70 +
        1699019923358098310954982860790090213000551823730050050840526964632703) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 89 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 2 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (319 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_319 :
    recurrence2Scalar1Shift.coeff 319 =
      -(((815378370273035771260446925960952896613 * 10 ^ 70 +
        3151649160160215437204987729895423662315872889805709387805732376842980) * 10 ^ 70 +
        3285592021720524836294243417290243678879255955273567731526153245642184) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 90 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 1 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (320 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_320 :
    recurrence2Scalar1Shift.coeff 320 =
      (((67443192159925559473018396579858869656 * 10 ^ 70 +
        9810031142701004266396408077090874414326583585329014136550025228773937) * 10 ^ 70 +
        7600625895470180462893483761029284293678519130383704283675846279284098) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 91 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (321 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_321 :
    recurrence2Scalar1Shift.coeff 321 =
      -(((3270316914798826100324063961242514315 * 10 ^ 70 +
        3173373569650814152721186581118148536423199172343026983122596174686367) * 10 ^ 70 +
        9085222449157167965460270125835755791221241027046800971115200935543909) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 92 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 31 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (322 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_322 :
    recurrence2Scalar1Shift.coeff 322 =
      -(((176637564910902261462747712165350681 * 10 ^ 70 +
        4855004513400743469843763011357015152232273780875110906941846799665894) * 10 ^ 70 +
        4600883418067725492740117822072652627620170679811055344635767350628498) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 93 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 30 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (323 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_323 :
    recurrence2Scalar1Shift.coeff 323 =
      (((70192419085263582624498532813299296 * 10 ^ 70 +
        0528892017648337205903534069317617194026104757504218875843172054515437) * 10 ^ 70 +
        0445056065765345912660845778357863651986318790253273043123696338487011) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 94 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 29 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (324 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_324 :
    recurrence2Scalar1Shift.coeff 324 =
      -(((10668373544098375899839625656439698 * 10 ^ 70 +
        3748578686582470020943038909080209360642546689468407585036620560098500) * 10 ^ 70 +
        3791681502553438878559826421605416307911448776914140447122160382825099) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 95 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 28 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (325 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_325 :
    recurrence2Scalar1Shift.coeff 325 =
      (((1124099440754796484211895843248484 * 10 ^ 70 +
        3145186923045093450162397495592325732149798060046500916171498726540627) * 10 ^ 70 +
        7183036627962256754544872362612981890058105267918308992307286637901659) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 96 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 27 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (326 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_326 :
    recurrence2Scalar1Shift.coeff 326 =
      -(((84807941045910271828643130188580 * 10 ^ 70 +
        6997442848196178181194613000994634333625124719026651588895714691748090) * 10 ^ 70 +
        8654366146087414680142429314820698877044804079178897266465875325459574) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 97 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 26 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (327 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_327 :
    recurrence2Scalar1Shift.coeff 327 =
      (((3652235426064342630889491040344 * 10 ^ 70 +
        6254768468980151458278721301710405161803118140889917651202415076262731) * 10 ^ 70 +
        9114670958428618101421933453764961453656089057681590712536241284525992) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 98 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 25 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (328 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_328 :
    recurrence2Scalar1Shift.coeff 328 =
      (((107245001096026958790168525312 * 10 ^ 70 +
        4033352335774025712832240464065391861125830842629161429604675751143094) * 10 ^ 70 +
        5546390617823753811840913670370310144861620372282709974051991357035249) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 99 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 24 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (329 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_329 :
    recurrence2Scalar1Shift.coeff 329 =
      -(((38340820613786692340555054653 * 10 ^ 70 +
        1822740587308531354607225122318769030726035419902126112772787125702947) * 10 ^ 70 +
        4335885006247583375290560301992945360731280949166144750939430727661747) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 100 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 23 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (330 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_330 :
    recurrence2Scalar1Shift.coeff 330 =
      (((4077576829086977074039337868 * 10 ^ 70 +
        5940482206411529704506613902918031342858757107208225460955932481717767) * 10 ^ 70 +
        1907824327997637541973312154413123860976466765111962960125676469878513) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 101 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 22 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (331 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_331 :
    recurrence2Scalar1Shift.coeff 331 =
      -(((261715132600132464168060674 * 10 ^ 70 +
        4151548966727466985025715864836136592878315845281721893913216372027634) * 10 ^ 70 +
        4798334553046371915007964221379997093851842435760915139148964765494961) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 102 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 21 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (332 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_332 :
    recurrence2Scalar1Shift.coeff 332 =
      (((8285367335533400125936941 * 10 ^ 70 +
        1533578037788334904835009525186835867828054175521245178543472032100657) * 10 ^ 70 +
        0952205097361456256133662578375177235353658164284754727234564537265021) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 103 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 20 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (333 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_333 :
    recurrence2Scalar1Shift.coeff 333 =
      (((307374615118008732208087 * 10 ^ 70 +
        4372991205223182088101881331844023804279528277374360078665480328573982) * 10 ^ 70 +
        9300541454639394191895087756420622117603173794583348389729596987263808) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 104 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 19 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (334 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_334 :
    recurrence2Scalar1Shift.coeff 334 =
      -(((60482698547547812167595 * 10 ^ 70 +
        0785284221051345267275573694944245001251911635112581898037496494698212) * 10 ^ 70 +
        1557300439577039334387977420256405648145108558876361664047900375664748) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 105 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 18 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (335 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_335 :
    recurrence2Scalar1Shift.coeff 335 =
      (((4171151555955676068130 * 10 ^ 70 +
        5779484007426587195035775599101868922406275293492772392467707840452325) * 10 ^ 70 +
        4616945133163877179288857908369423881873509440449584648958503633012950) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 106 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 17 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (336 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_336 :
    recurrence2Scalar1Shift.coeff 336 =
      -(((153957333692994430399 * 10 ^ 70 +
        9676745134332467131472618892428528941226844581074537043148201209740633) * 10 ^ 70 +
        1446262837112486530603910948738987046412120254687224609974819723766745) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 107 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 16 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (337 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_337 :
    recurrence2Scalar1Shift.coeff 337 =
      (((769262980239311452 * 10 ^ 70 +
        6670431708365824834546522091183700736199014641367371851870390422001410) * 10 ^ 70 +
        7989267505623692037406308975457754363275001526536423383595102616148194) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 108 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 15 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Shift_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (338 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_338 :
    recurrence2Scalar1Shift.coeff 338 =
      (((269048024432136180 * 10 ^ 70 +
        6583082660232948139462695234429341518043758627240192882926951579102682) * 10 ^ 70 +
        6985897427098523241715196548465838024978181782076635131530461820164302) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 109 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 14 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
