/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Exceptional coefficient convolution

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
  recurrence2C0_coeff_0
  recurrence2C0_coeff_1
  recurrence2C0_coeff_2
  recurrence2C0_coeff_3
  recurrence2C0_coeff_4
  recurrence2C0_coeff_5
  recurrence2C0_coeff_6
  recurrence2C0_coeff_7
  recurrence2C0_coeff_8
  recurrence2C0_coeff_9
  recurrence2C0_coeff_10
  recurrence2C0_coeff_11
  recurrence2C0_coeff_12
  recurrence2C0_coeff_13
  recurrence2C0_coeff_14
  recurrence2C0_coeff_15
  recurrence2C0_coeff_16
  recurrence2C0_coeff_17
  recurrence2C0_coeff_18
  recurrence2C0_coeff_19
  recurrence2C0_coeff_20
  recurrence2C0_coeff_21
  recurrence2C0_coeff_22
  recurrence2C0_coeff_23
  recurrence2C0_coeff_24
  recurrence2C0_coeff_25
  recurrence2C0_coeff_26
  recurrence2C0_coeff_27
  recurrence2C0_coeff_28
  recurrence2C0_coeff_29
  recurrence2C0_coeff_30
  recurrence2C0_coeff_31
  recurrence2C0_coeff_32
  recurrence2C0_coeff_33
  recurrence2C0_coeff_34
  recurrence2C0_coeff_35
  recurrence2C0_coeff_36
  recurrence2C0_coeff_37
  recurrence2C0_coeff_38
  recurrence2C0_coeff_39
  recurrence2C0_coeff_40
  recurrence2C0_coeff_41
  recurrence2C0_coeff_42
  recurrence2C0_coeff_43
  recurrence2C0_coeff_44
  recurrence2C0_coeff_45
  recurrence2C0_coeff_46
  recurrence2C0_coeff_47
  recurrence2C0_coeff_48
  recurrence2C0_coeff_49
  recurrence2C0_coeff_50
  recurrence2C0_coeff_51
  recurrence2C0_coeff_52
  recurrence2C0_coeff_53
  recurrence2C0_coeff_54
  recurrence2C0_coeff_55
  recurrence2C0_coeff_56
  recurrence2C0_coeff_57
  recurrence2C0_coeff_58
  recurrence2C0_coeff_59
  recurrence2C0_coeff_60
  recurrence2C0_coeff_61
  recurrence2C0_coeff_62
  recurrence2C0_coeff_63
  recurrence2C0_coeff_64
  recurrence2C0_coeff_65
  recurrence2C0_coeff_66
  recurrence2C0_coeff_67
  recurrence2C0_coeff_68
  recurrence2C0_coeff_69
  recurrence2C0_coeff_70
  recurrence2C0_coeff_71
  recurrence2C0_coeff_72
  recurrence2C0_coeff_73
  recurrence2C0_coeff_74
  recurrence2C0_coeff_75
  recurrence2C0_coeff_76
  recurrence2C0_coeff_77
  recurrence2C0_coeff_78
  recurrence2C0_coeff_79
  recurrence2C0_coeff_80
  recurrence2C0_coeff_81
  recurrence2C0_coeff_82
  recurrence2C0_coeff_83
  recurrence2C0_coeff_84
  recurrence2C0_coeff_85
  recurrence2C0_coeff_86
  recurrence2C0_coeff_87
  recurrence2C0_coeff_88
  recurrence2C0_coeff_89
  recurrence2C0_coeff_90
  recurrence2C0_coeff_91
  recurrence2C0_coeff_92
  recurrence2C0_coeff_93
  recurrence2C0_coeff_94
  recurrence2C0_coeff_95
  recurrence2C0_coeff_96
  recurrence2C0_coeff_97
  recurrence2C0_coeff_98
  recurrence2C0_coeff_99
  recurrence2C0_coeff_100
  recurrence2C0_coeff_101
  recurrence2C0_coeff_102
  recurrence2C0_coeff_103
  recurrence2C0_coeff_104
  recurrence2C0_coeff_105
  recurrence2C0_coeff_106
  recurrence2C0_coeff_107
  recurrence2C0_coeff_108
  recurrence2C0_coeff_109
  recurrence2C0_coeff_110
  recurrence2C0_coeff_111
  recurrence2C0_coeff_112
  recurrence2C0_coeff_113
  recurrence2C0_coeff_114
  recurrence2C0_coeff_115
  recurrence2C0_coeff_116
  recurrence2C0_coeff_117
  recurrence2C0_coeff_118
  recurrence2C0_coeff_119
  recurrence2C0_coeff_120
  recurrence2C0_coeff_121
  recurrence2C0_coeff_122
  recurrence2C0_coeff_123
  recurrence2C0_coeff_124
  recurrence2C0_coeff_125
  recurrence2C0_coeff_126
  recurrence2C0_coeff_127
  recurrence2C0_coeff_128
  recurrence2C0_coeff_129
  recurrence2C0_coeff_130
  recurrence2C0_coeff_131
  recurrence2C0_coeff_132
  recurrence2C0_coeff_133
  recurrence2C0_coeff_134
  recurrence2C0_coeff_135
  recurrence2C0_coeff_136
  recurrence2C0_coeff_137
  recurrence2C0_coeff_138
  recurrence2C0_coeff_139
  recurrence2C0_coeff_140
  recurrence2C0_coeff_141
  recurrence2C0_coeff_142
  recurrence2C0_coeff_143
  recurrence2C0_coeff_144
  recurrence2C0_coeff_145
  recurrence2C0_coeff_146
  recurrence2C0_coeff_147
  recurrence2C0_coeff_148
  recurrence2C0_coeff_149
  recurrence2C0_coeff_150
  recurrence2C0_coeff_151
  recurrence2C0_coeff_152
  recurrence2C0_coeff_153
  recurrence2C0_coeff_154
  recurrence2C0_coeff_155
  recurrence2C0_coeff_156
  recurrence2C0_coeff_157
  recurrence2C0_coeff_158
  recurrence2C0_coeff_159
  recurrence2C0_coeff_160
  recurrence2C0_coeff_161
  recurrence2C0_coeff_162
  recurrence2C0_coeff_163
  recurrence2C0_coeff_164
  recurrence2C0_coeff_165
  recurrence2C0_coeff_166
  recurrence2C0_coeff_167
  recurrence2C0_coeff_168
  recurrence2C0_coeff_169
  recurrence2C0_coeff_170
  recurrence2C0_coeff_171
  recurrence2C0_coeff_172
  recurrence2C0_coeff_173
  recurrence2C0_coeff_174
  recurrence2C0_coeff_175
  recurrence2C0_coeff_176
  recurrence2C0_coeff_177
  recurrence2C0_coeff_178
  recurrence2C0_coeff_179
  recurrence2C0_coeff_180
  recurrence2C0_coeff_181
  recurrence2C0_coeff_182
  recurrence2C0_coeff_183
  recurrence2C0_coeff_184
  recurrence2C0_coeff_185
  recurrence2C0_coeff_186
  recurrence2C0_coeff_187
  recurrence2C0_coeff_188
  recurrence2C0_coeff_189
  recurrence2C0_coeff_190
  recurrence2C0_coeff_191
  recurrence2C0_coeff_192
  recurrence2C0_coeff_193
  recurrence2C0_coeff_194

private theorem recurrence2Scalar0Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (258 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_258 :
    recurrence2Scalar0Exceptional.coeff 258 =
      -(((43574199007027636672883971471227412368788532571546176892 * 10 ^ 70 +
        2586283100497691051785892185030243641986838145564053421648659492336964) * 10 ^ 70 +
        2616752582071267754239376131231891736770458900833573783912956684001734) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 64 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 67 = 2 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (259 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_259 :
    recurrence2Scalar0Exceptional.coeff 259 =
      (((10252887087874249873459646909114430606795571807711030937 * 10 ^ 70 +
        3694218391681558728505884325914955866375882278932634248909910198534297) * 10 ^ 70 +
        0955286313718272307449579012949173681260097268382774995315872123810234) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 65 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 67 = 1 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (260 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_260 :
    recurrence2Scalar0Exceptional.coeff 260 =
      (((843125021738405403521816566593990179600502526866313951 * 10 ^ 70 +
        8494378415068510071887465970695208036518961921633752164093910513600147) * 10 ^ 70 +
        5887955754893843307822715240276621457701355409053682726546106377491878) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 66 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (261 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_261 :
    recurrence2Scalar0Exceptional.coeff 261 =
      -(((3016485866916152412573759766731414188900812347532250257 * 10 ^ 70 +
        2558057287015484892286301739916802376343474884582521396554097310762379) * 10 ^ 70 +
        0262945206665327913458843506846335373239289005786882877906708498010710) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 67 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 31 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_262 :
    recurrence2Scalar0Exceptional.coeff 262 =
      (((2417357127732110587531166237242657022625164505664512001 * 10 ^ 70 +
        4180894843789464788259477574644930629550025471955380527710268662619643) * 10 ^ 70 +
        9919442090087626440590155060635061599079029350080656593624460018991609) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 68 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 30 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_263 :
    recurrence2Scalar0Exceptional.coeff 263 =
      -(((1420082613514195423182001984853173201163017929361517379 * 10 ^ 70 +
        8893136603391889590844978569114018242622642829094707556854038429586143) * 10 ^ 70 +
        9680789154091828452534320937801492392320354927489780866861150650034478) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 69 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 29 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_264 :
    recurrence2Scalar0Exceptional.coeff 264 =
      (((697268766959056859941283795856285018935619501995700232 * 10 ^ 70 +
        4167773058282608322879234970875381743006241568417116087876980654009385) * 10 ^ 70 +
        8447615865873933803382849788704109533227736634329028911818717582637776) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 70 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 28 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_265 :
    recurrence2Scalar0Exceptional.coeff 265 =
      -(((296261456595762839721850493814235938975791147224913967 * 10 ^ 70 +
        8322050042774072485383879784149438296507457345535780032462930637619714) * 10 ^ 70 +
        3607241734286883260671730636460079592542255227554706861862753397508045) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 71 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 27 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_266 :
    recurrence2Scalar0Exceptional.coeff 266 =
      (((108887272737494805271796056439522399897087429007771069 * 10 ^ 70 +
        7371604274502955153588109212024855149263101941758952173191792756497811) * 10 ^ 70 +
        5995262858382398424839157788797431771357237755630479935437968501167873) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 72 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 26 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_267 :
    recurrence2Scalar0Exceptional.coeff 267 =
      -(((33387907641601356211320351397772280114460866627251463 * 10 ^ 70 +
        4408262786687025185795663818420238081652214405815146868854895954038405) * 10 ^ 70 +
        6055756679520464936567395603716032099722516229299149297474765570820393) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 73 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 25 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_268 :
    recurrence2Scalar0Exceptional.coeff 268 =
      (((7427116281348822459005009406003730716108764558690400 * 10 ^ 70 +
        6570914029213293704202981489038639588000764232294512248855406621228248) * 10 ^ 70 +
        9785378463925331162125220903543571382060577668432057782007378115485908) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 74 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 24 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_269 :
    recurrence2Scalar0Exceptional.coeff 269 =
      -(((253862906953289379732746025933835065452080968324032 * 10 ^ 70 +
        4644828071841147058526850195967134018797555615108063217439616973872325) * 10 ^ 70 +
        6272491709868086522707669995201344511311309324330003024396811772159230) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 75 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 23 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_270 :
    recurrence2Scalar0Exceptional.coeff 270 =
      -(((961811671611426394243266073415566254180716985182021 * 10 ^ 70 +
        2126723421426544281150464348872818122984426442780516489252769237651716) * 10 ^ 70 +
        4027073354197848662957867316228823731926082864185689918154532743641242) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 76 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 22 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_271 :
    recurrence2Scalar0Exceptional.coeff 271 =
      (((752826921292770900879956438803897493800519598507090 * 10 ^ 70 +
        0235979430683284104288662034440338033593509277845340584152347116864132) * 10 ^ 70 +
        8803909270961134834040722894183371027490151016578268182367415126016648) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 77 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 21 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_272 :
    recurrence2Scalar0Exceptional.coeff 272 =
      -(((416103660941125821653263463255901110206214793380213 * 10 ^ 70 +
        7648833731340923323506368089485846037333633381158843205673093279996736) * 10 ^ 70 +
        7620518191872104775382487507609388275420751614614180213338499114577071) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 78 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 20 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_273 :
    recurrence2Scalar0Exceptional.coeff 273 =
      (((198973389874188117737638927229340875271967448402870 * 10 ^ 70 +
        6371620199711636140649340079579088070760009371152835349929076026010776) * 10 ^ 70 +
        0466004792097269664743984763737627549629705807035021623591599148079331) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 79 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 19 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_274 :
    recurrence2Scalar0Exceptional.coeff 274 =
      -(((87536589133536725035926569859094721525574755319962 * 10 ^ 70 +
        7136535790353500717086508610819498735761507111026257596148037145500255) * 10 ^ 70 +
        3191743072730440843017854464566258074150607614302444035900572342198453) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 80 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 18 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_275 :
    recurrence2Scalar0Exceptional.coeff 275 =
      (((36241429747935458808411441195796623022731935653836 * 10 ^ 70 +
        4900278390164188472144583785006146416995578001364456251298834872161802) * 10 ^ 70 +
        4320072434700379196249374917684288289338899867866702133621077248760985) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 81 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 17 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_276 :
    recurrence2Scalar0Exceptional.coeff 276 =
      -(((14177629689898964616945632119793318996738720177009 * 10 ^ 70 +
        2040594374358257797561538758672286925894802467105843375261581147043512) * 10 ^ 70 +
        6893495627152607866045253667264413831988953313748709661667985936783579) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 82 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 16 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_277 :
    recurrence2Scalar0Exceptional.coeff 277 =
      (((5193305331989844039191817165321540848581747637092 * 10 ^ 70 +
        4524676550500514569300221361520866843534213464586293259240134659664552) * 10 ^ 70 +
        5620394368732972661184316588127083812311056123140584171778475470568991) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 83 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 15 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_278 :
    recurrence2Scalar0Exceptional.coeff 278 =
      -(((1732244759324372728661255349519250444760929563246 * 10 ^ 70 +
        4964564021325862096198485839660365953155124782126962306471367743220730) * 10 ^ 70 +
        9844857172511169128891248273755322489351676427087618589896725785725286) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 84 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 14 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_279 :
    recurrence2Scalar0Exceptional.coeff 279 =
      (((483903644625711397746177984724433566181295421056 * 10 ^ 70 +
        7215611820590380411076030385068173458426888852874570044157823919394644) * 10 ^ 70 +
        8876402640221468372360585491693915537338962477050036679819053889806867) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 85 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 13 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_280 :
    recurrence2Scalar0Exceptional.coeff 280 =
      -(((74937904817035208333256314466429167613576284867 * 10 ^ 70 +
        5668615452779425701094084120863704394249332035395577043056743590696557) * 10 ^ 70 +
        4909733706622143705407661765179685523908573003096054337537533575151937) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 86 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 12 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_281 :
    recurrence2Scalar0Exceptional.coeff 281 =
      -(((34698813803660243907404156947126304618967284595 * 10 ^ 70 +
        5225887996575664016463379418201587648505114342607533157235049064101978) * 10 ^ 70 +
        1988517599324277104399915143956750570763862486072146829127373548853491) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 87 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 11 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_282 :
    recurrence2Scalar0Exceptional.coeff 282 =
      (((46970635340258099859422159982355707957047417781 * 10 ^ 70 +
        2917910886291022694194645290326608742715206302830225467385513815929045) * 10 ^ 70 +
        1055541513382769750668927288435594824749024828787688297535549925437886) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 88 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 10 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_283 :
    recurrence2Scalar0Exceptional.coeff 283 =
      -(((33879612018819325719098491008080919296595438196 * 10 ^ 70 +
        9209756594692448153211642830848403099837502123024038634939859532989386) * 10 ^ 70 +
        4483439437169088097344030286377930342233341672374533678287834722763161) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 89 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 9 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_284 :
    recurrence2Scalar0Exceptional.coeff 284 =
      (((19184659783156735233813632357713224768991905392 * 10 ^ 70 +
        7750921312532413136625113926965219232544468584738780246048285719695895) * 10 ^ 70 +
        1060359656031265406509997952513925636010061396435780941850742281642272) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 90 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 8 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
