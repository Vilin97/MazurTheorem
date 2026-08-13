/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4ShiftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B3_coeff_0
  recurrence2B3_coeff_1
  recurrence2B3_coeff_2
  recurrence2B3_coeff_3
  recurrence2B3_coeff_4
  recurrence2B3_coeff_5
  recurrence2B3_coeff_6
  recurrence2B3_coeff_7
  recurrence2B3_coeff_8
  recurrence2B3_coeff_9
  recurrence2B3_coeff_10
  recurrence2B3_coeff_11
  recurrence2B3_coeff_12
  recurrence2B3_coeff_13
  recurrence2B3_coeff_14
  recurrence2B3_coeff_15
  recurrence2B3_coeff_16
  recurrence2B3_coeff_17
  recurrence2B3_coeff_18
  recurrence2B3_coeff_19
  recurrence2B3_coeff_20
  recurrence2B3_coeff_21
  recurrence2B3_coeff_22
  recurrence2B3_coeff_23
  recurrence2B3_coeff_24
  recurrence2B3_coeff_25
  recurrence2B3_coeff_26
  recurrence2B3_coeff_27
  recurrence2B3_coeff_28
  recurrence2B3_coeff_29
  recurrence2B3_coeff_30
  recurrence2B3_coeff_31
  recurrence2B3_coeff_32
  recurrence2B3_coeff_33
  recurrence2B3_coeff_34
  recurrence2B3_coeff_35
  recurrence2B3_coeff_36
  recurrence2B3_coeff_37
  recurrence2B3_coeff_38
  recurrence2B3_coeff_39
  recurrence2B3_coeff_40
  recurrence2B3_coeff_41
  recurrence2B3_coeff_42
  recurrence2B3_coeff_43
  recurrence2B3_coeff_44
  recurrence2B3_coeff_45
  recurrence2B3_coeff_46
  recurrence2B3_coeff_47
  recurrence2B3_coeff_48
  recurrence2B3_coeff_49
  recurrence2B3_coeff_50
  recurrence2B3_coeff_51
  recurrence2B3_coeff_52
  recurrence2B3_coeff_53
  recurrence2B3_coeff_54
  recurrence2B3_coeff_55
  recurrence2B3_coeff_56
  recurrence2B3_coeff_57
  recurrence2B3_coeff_58
  recurrence2B3_coeff_59
  recurrence2B3_coeff_60
  recurrence2B3_coeff_61
  recurrence2B3_coeff_62
  recurrence2B3_coeff_63
  recurrence2B3_coeff_64
  recurrence2B3_coeff_65
  recurrence2B3_coeff_66
  recurrence2B3_coeff_67
  recurrence2B3_coeff_68
  recurrence2B3_coeff_69
  recurrence2B3_coeff_70
  recurrence2B3_coeff_71
  recurrence2B3_coeff_72
  recurrence2B3_coeff_73
  recurrence2B3_coeff_74
  recurrence2B3_coeff_75
  recurrence2B3_coeff_76
  recurrence2B3_coeff_77
  recurrence2B3_coeff_78
  recurrence2B3_coeff_79
  recurrence2B3_coeff_80
  recurrence2B3_coeff_81
  recurrence2B3_coeff_82
  recurrence2B3_coeff_83
  recurrence2B3_coeff_84
  recurrence2B3_coeff_85
  recurrence2B3_coeff_86
  recurrence2B3_coeff_87
  recurrence2B3_coeff_88
  recurrence2B3_coeff_89
  recurrence2B3_coeff_90
  recurrence2B3_coeff_91
  recurrence2B3_coeff_92
  recurrence2B3_coeff_93
  recurrence2B3_coeff_94
  recurrence2B3_coeff_95
  recurrence2B3_coeff_96
  recurrence2B3_coeff_97
  recurrence2B3_coeff_98
  recurrence2B3_coeff_99
  recurrence2B3_coeff_100
  recurrence2B3_coeff_101
  recurrence2B3_coeff_102
  recurrence2B3_coeff_103
  recurrence2B3_coeff_104
  recurrence2B3_coeff_105
  recurrence2B3_coeff_106
  recurrence2B3_coeff_107
  recurrence2B3_coeff_108
  recurrence2B3_coeff_109
  recurrence2B3_coeff_110
  recurrence2B3_coeff_111
  recurrence2B3_coeff_112
  recurrence2B3_coeff_113
  recurrence2B3_coeff_114
  recurrence2B3_coeff_115
  recurrence2B3_coeff_116
  recurrence2B3_coeff_117
  recurrence2B3_coeff_118
  recurrence2B3_coeff_119
  recurrence2B3_coeff_120
  recurrence2B3_coeff_121
  recurrence2B3_coeff_122
  recurrence2B3_coeff_123
  recurrence2B3_coeff_124
  recurrence2B3_coeff_125
  recurrence2B3_coeff_126
  recurrence2B3_coeff_127
  recurrence2B3_coeff_128
  recurrence2B3_coeff_129
  recurrence2B3_coeff_130
  recurrence2B3_coeff_131
  recurrence2B3_coeff_132
  recurrence2B3_coeff_133
  recurrence2B3_coeff_134
  recurrence2B3_coeff_135
  recurrence2B3_coeff_136
  recurrence2B3_coeff_137
  recurrence2B3_coeff_138
  recurrence2B3_coeff_139
  recurrence2B3_coeff_140
  recurrence2B3_coeff_141
  recurrence2B3_coeff_142
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

private theorem recurrence2Scalar4Shift_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (264 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_264 :
    recurrence2Scalar4Shift.coeff 264 =
      (((249767623981559587542087773197600401174753435811565692601911760282 * 10 ^ 70 +
        2447485800139895667624350685012322983192156983774725141983603960277463) * 10 ^ 70 +
        4635030692332039347508541851951033123625973056623557741338861779771741) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 35 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 12 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (265 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_265 :
    recurrence2Scalar4Shift.coeff 265 =
      -(((97562307736093801238100500888519906317768683416940106184187734969 * 10 ^ 70 +
        3257647925738693649705682387020775432535549108754789598713506772049244) * 10 ^ 70 +
        8311540288080734455308014649427280793151439555188317907260891015612148) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 36 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 11 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (266 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_266 :
    recurrence2Scalar4Shift.coeff 266 =
      (((33186791671368097683250762518879093076636454552666303687506312469 * 10 ^ 70 +
        8567976703254638696038481023335506680747357400363357508109773038420631) * 10 ^ 70 +
        2004304927768557905967124447680347373585163684899575195490650993906434) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 37 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 10 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (267 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_267 :
    recurrence2Scalar4Shift.coeff 267 =
      -(((8763691747098821267199672366555062245114485633955418025060484346 * 10 ^ 70 +
        9003645566613952261809178894045614109647369195417143563160016883760498) * 10 ^ 70 +
        4199192552346090049174009296039209690629091468950165617240532780184125) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 38 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 9 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (268 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_268 :
    recurrence2Scalar4Shift.coeff 268 =
      (((881593143801992991918797849036214081480389719818315807717056199 * 10 ^ 70 +
        7265445386056394970998181376326462807590258948339886499109697537864475) * 10 ^ 70 +
        3236271496363933871124116843177344106429806067671014263352257398551355) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 39 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 8 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (269 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_269 :
    recurrence2Scalar4Shift.coeff 269 =
      (((941064219476994122303343434511329757226236097666416952166106391 * 10 ^ 70 +
        6236115720724931142871918723561950113890980654279725310003419934218491) * 10 ^ 70 +
        5711848585003856661302854554332196592721034682861126359488204137558554) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 40 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 7 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (270 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_270 :
    recurrence2Scalar4Shift.coeff 270 =
      -(((935019924607153287331028096202278751439438310987060046175461573 * 10 ^ 70 +
        8729285280872996070849418276794429826253623346251417855387232239034218) * 10 ^ 70 +
        6834513581828089549821838382880256622941518406988555012861600196289285) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 41 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 6 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (271 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_271 :
    recurrence2Scalar4Shift.coeff 271 =
      (((585385653853939263887161918068802903705608841195407989382216837 * 10 ^ 70 +
        3095105726916515541063420753437106827531877244914029109799967259062340) * 10 ^ 70 +
        1284313628290996919825899625878239340716139754513626564369558411962936) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 42 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 5 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (272 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_272 :
    recurrence2Scalar4Shift.coeff 272 =
      -(((302235038072818931126349169553021762820193937717299775599902675 * 10 ^ 70 +
        6766792601553793967659591095643304829310844829276925676752881568455092) * 10 ^ 70 +
        2757723633782905973678712121639460079558129949513658410147823445782296) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 43 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 4 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (273 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_273 :
    recurrence2Scalar4Shift.coeff 273 =
      (((137741359230420451149117517213816430767877375815090551000769553 * 10 ^ 70 +
        1796429423361248762274855743913706361986783464241891459766994950912379) * 10 ^ 70 +
        2481279567553163859187295703942069424271117518798393673825181424392219) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 44 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 3 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (274 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_274 :
    recurrence2Scalar4Shift.coeff 274 =
      -(((56836051038600617201725179652428721297884792384553154065024356 * 10 ^ 70 +
        1334587341987051223882381303922584475266637191327292983067630481136385) * 10 ^ 70 +
        6043601777183635620553255187334260594301423731680642459991412018983756) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 45 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 2 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (275 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_275 :
    recurrence2Scalar4Shift.coeff 275 =
      (((21433740524665530606585612759335753184468980727467217720763181 * 10 ^ 70 +
        8614092551752324076572068849335355664397686856874397462233449957000553) * 10 ^ 70 +
        6539707470647734625242293644882444911617628302711142712120760719404145) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 46 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 1 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (276 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_276 :
    recurrence2Scalar4Shift.coeff 276 =
      -(((7389143420215542812463990751642926021123568347054750811811822 * 10 ^ 70 +
        8866494558845121105106993878849315587663017279209993567491606627416041) * 10 ^ 70 +
        6262763047320555022424447590610615465145085343755222269549206859795731) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 47 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (277 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_277 :
    recurrence2Scalar4Shift.coeff 277 =
      (((2309507331610841722234484090654944648087484621465063329267464 * 10 ^ 70 +
        4112854293674488188063065950574537638601206433065040576845035095271916) * 10 ^ 70 +
        2319437545797492418832869518302676803888326665871369549073304140001219) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 48 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 31 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (278 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_278 :
    recurrence2Scalar4Shift.coeff 278 =
      -(((640542371751855846637919977144976319554836807853997478210372 * 10 ^ 70 +
        1954121447888525507247629160383222542264880216032969442882319137851619) * 10 ^ 70 +
        5934394092478481324862935727302434066431541051960853929135435235873976) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 49 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 30 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (279 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_279 :
    recurrence2Scalar4Shift.coeff 279 =
      (((149541685491664366139491047735279726342239108688596593110420 * 10 ^ 70 +
        2340309096584191567041193160190054877789593737113045249381785336978728) * 10 ^ 70 +
        0774266259885809492564357890793764319703874167172320624086674592542874) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 50 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 29 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (280 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_280 :
    recurrence2Scalar4Shift.coeff 280 =
      -(((24721753304055674262132791706509734221821911960081253758382 * 10 ^ 70 +
        4896630243846070605734143793579114054594604591534369852028849606728401) * 10 ^ 70 +
        3541515301370114888852724466035699816295936995082177731901771240903034) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 51 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 28 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (281 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_281 :
    recurrence2Scalar4Shift.coeff 281 =
      -(((93353788642221593534207235156270968814871894967637860119 * 10 ^ 70 +
        1501858797527613852842008638893921548567729800987592787783991453852722) * 10 ^ 70 +
        9685230962388684002171924813449406153718816468625799916273521032378374) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 52 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 27 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (282 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_282 :
    recurrence2Scalar4Shift.coeff 282 =
      (((2374153773533081190883377524803047795228867321398567290301 * 10 ^ 70 +
        7223273422128670029549335154554861654552641503566113384550866407228910) * 10 ^ 70 +
        1933890474355440771082328368769177839376613695731606322182439871121167) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 53 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 26 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (283 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_283 :
    recurrence2Scalar4Shift.coeff 283 =
      -(((1324248440869642633846259144751523237133691118847651378140 * 10 ^ 70 +
        9937436191281376148638020636612066946704728073209232399170881694452297) * 10 ^ 70 +
        1314020126885904054592074637490234468961548447325947518830755739333515) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 54 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 25 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (284 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_284 :
    recurrence2Scalar4Shift.coeff 284 =
      (((521467053667239320636310927873658236352777045942220730721 * 10 ^ 70 +
        4805467759025402583098844218536356761539117397370000341269282101296227) * 10 ^ 70 +
        4911865956715945600460189133777005243052012077720889172993924029242303) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 55 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 24 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (285 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_285 :
    recurrence2Scalar4Shift.coeff 285 =
      -(((170033781571061891369788368993081871018933632755457361756 * 10 ^ 70 +
        7476031524590697763671404778101921279458817953378708048561403910104858) * 10 ^ 70 +
        9935329271160553118638974963684580670633575025991716735984545523587636) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 56 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 23 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (286 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_286 :
    recurrence2Scalar4Shift.coeff 286 =
      (((47804985698350432143620582090153662083514247115363661213 * 10 ^ 70 +
        0983010907936660541048575175915185088171162951905937204596382647176517) * 10 ^ 70 +
        5523458875861683947284845716209670077706246441451685672821332440047018) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 57 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 22 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (287 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_287 :
    recurrence2Scalar4Shift.coeff 287 =
      -(((11610623487594542566850269332577016082763804985104121087 * 10 ^ 70 +
        0856813980181974325427888497678482548587504990399802704134077975985870) * 10 ^ 70 +
        2438132941288883489403131443969250070056607616913406122633205397747448) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 58 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 21 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (288 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_288 :
    recurrence2Scalar4Shift.coeff 288 =
      (((2358318638391241228220001927173380893496454021175569772 * 10 ^ 70 +
        3069087203630121530659640744420265685487686300578808588188542997367033) * 10 ^ 70 +
        4754625744501346990989801346957181631159588990161140750473098865035151) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 59 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 20 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (289 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_289 :
    recurrence2Scalar4Shift.coeff 289 =
      -(((355963233603097422240414984865968605635005985522852587 * 10 ^ 70 +
        1918264087845982813003455396225439591076320515847340903931927118783250) * 10 ^ 70 +
        0429392535517489567685868029447864852893724783979389187871923438584973) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 60 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 19 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Shift_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (290 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_290 :
    recurrence2Scalar4Shift.coeff 290 =
      (((17128136702190546193812232750803888597058964690076500 * 10 ^ 70 +
        3315231755348792552854977063696284525208452153101549934096977938685418) * 10 ^ 70 +
        3133012583053420457485856361198693025459153413418051896186736431753914) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 61 +
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
  rw [recurrence2Scalar4Shift_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (291 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_291 :
    recurrence2Scalar4Shift.coeff 291 =
      (((13337154653081201044237715110814295511858452334153668 * 10 ^ 70 +
        3978861381051106708450101577605586740451934096559872440492921186740530) * 10 ^ 70 +
        1911676389043525762217431279900721467560148214715543369840947387396685) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 62 +
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
  rw [recurrence2Scalar4Shift_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (292 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_292 :
    recurrence2Scalar4Shift.coeff 292 =
      -(((6743424852778523331417008004635843218348038282555573 * 10 ^ 70 +
        3585150357806781630214649792031792863358328108106093085297938506129987) * 10 ^ 70 +
        7449967970514857947040559544539205764941791535171845445703527872308109) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 63 +
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
  rw [recurrence2Scalar4Shift_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (293 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_293 :
    recurrence2Scalar4Shift.coeff 293 =
      (((2133390281255526967903273141897676725378565902776207 * 10 ^ 70 +
        0169129921598421020742772705040203452994044387096087563777058492766665) * 10 ^ 70 +
        3628731385726895156606482046404119190885702796896937007629910293865443) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 64 +
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
  rw [recurrence2Scalar4Shift_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (294 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_294 :
    recurrence2Scalar4Shift.coeff 294 =
      -(((533601317594521033399574886313294258272818709544665 * 10 ^ 70 +
        4763348999418786273042715223800336800453358976735491548122477173535555) * 10 ^ 70 +
        1893676924844330531760335829989316461072530273250349813179210498736481) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 65 +
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
  rw [recurrence2Scalar4Shift_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (295 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_295 :
    recurrence2Scalar4Shift.coeff 295 =
      (((110258756366130742668107103846923487846573173975924 * 10 ^ 70 +
        0157772419561042986523617597847884526134287658074100584482233408642718) * 10 ^ 70 +
        6815956096360475383301790230472524782209494874170007756079219298817832) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 66 +
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
  rw [recurrence2Scalar4Shift_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Shift_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient3.coeff x * recurrence2B5A6.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Shift_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2B5A6.coeff (296 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Shift_coeff_296 :
    recurrence2Scalar4Shift.coeff 296 =
      -(((18420645399584009482243711836036032609794699916876 * 10 ^ 70 +
        7307373514496663735814036860931034233255218221803473385010688976949978) * 10 ^ 70 +
        5490077707359664270227604491746348081097732570801203167050825995441985) : ℚ) := by
  unfold recurrence2Scalar4Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 67 +
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
  rw [recurrence2Scalar4Shift_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Shift_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
