/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Exceptional coefficient convolution

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
  recurrence2C4_coeff_0
  recurrence2C4_coeff_1
  recurrence2C4_coeff_2
  recurrence2C4_coeff_3
  recurrence2C4_coeff_4
  recurrence2C4_coeff_5
  recurrence2C4_coeff_6
  recurrence2C4_coeff_7
  recurrence2C4_coeff_8
  recurrence2C4_coeff_9
  recurrence2C4_coeff_10
  recurrence2C4_coeff_11
  recurrence2C4_coeff_12
  recurrence2C4_coeff_13
  recurrence2C4_coeff_14
  recurrence2C4_coeff_15
  recurrence2C4_coeff_16
  recurrence2C4_coeff_17
  recurrence2C4_coeff_18
  recurrence2C4_coeff_19
  recurrence2C4_coeff_20
  recurrence2C4_coeff_21
  recurrence2C4_coeff_22
  recurrence2C4_coeff_23
  recurrence2C4_coeff_24
  recurrence2C4_coeff_25
  recurrence2C4_coeff_26
  recurrence2C4_coeff_27
  recurrence2C4_coeff_28
  recurrence2C4_coeff_29
  recurrence2C4_coeff_30
  recurrence2C4_coeff_31
  recurrence2C4_coeff_32
  recurrence2C4_coeff_33
  recurrence2C4_coeff_34
  recurrence2C4_coeff_35
  recurrence2C4_coeff_36
  recurrence2C4_coeff_37
  recurrence2C4_coeff_38
  recurrence2C4_coeff_39
  recurrence2C4_coeff_40
  recurrence2C4_coeff_41
  recurrence2C4_coeff_42
  recurrence2C4_coeff_43
  recurrence2C4_coeff_44
  recurrence2C4_coeff_45
  recurrence2C4_coeff_46
  recurrence2C4_coeff_47
  recurrence2C4_coeff_48
  recurrence2C4_coeff_49
  recurrence2C4_coeff_50
  recurrence2C4_coeff_51
  recurrence2C4_coeff_52
  recurrence2C4_coeff_53
  recurrence2C4_coeff_54
  recurrence2C4_coeff_55
  recurrence2C4_coeff_56
  recurrence2C4_coeff_57
  recurrence2C4_coeff_58
  recurrence2C4_coeff_59
  recurrence2C4_coeff_60
  recurrence2C4_coeff_61
  recurrence2C4_coeff_62
  recurrence2C4_coeff_63
  recurrence2C4_coeff_64
  recurrence2C4_coeff_65
  recurrence2C4_coeff_66
  recurrence2C4_coeff_67
  recurrence2C4_coeff_68
  recurrence2C4_coeff_69
  recurrence2C4_coeff_70
  recurrence2C4_coeff_71
  recurrence2C4_coeff_72
  recurrence2C4_coeff_73
  recurrence2C4_coeff_74
  recurrence2C4_coeff_75
  recurrence2C4_coeff_76
  recurrence2C4_coeff_77
  recurrence2C4_coeff_78
  recurrence2C4_coeff_79
  recurrence2C4_coeff_80
  recurrence2C4_coeff_81
  recurrence2C4_coeff_82
  recurrence2C4_coeff_83
  recurrence2C4_coeff_84
  recurrence2C4_coeff_85
  recurrence2C4_coeff_86
  recurrence2C4_coeff_87
  recurrence2C4_coeff_88
  recurrence2C4_coeff_89
  recurrence2C4_coeff_90
  recurrence2C4_coeff_91
  recurrence2C4_coeff_92
  recurrence2C4_coeff_93
  recurrence2C4_coeff_94
  recurrence2C4_coeff_95
  recurrence2C4_coeff_96
  recurrence2C4_coeff_97
  recurrence2C4_coeff_98
  recurrence2C4_coeff_99
  recurrence2C4_coeff_100
  recurrence2C4_coeff_101
  recurrence2C4_coeff_102
  recurrence2C4_coeff_103
  recurrence2C4_coeff_104
  recurrence2C4_coeff_105
  recurrence2C4_coeff_106
  recurrence2C4_coeff_107
  recurrence2C4_coeff_108
  recurrence2C4_coeff_109
  recurrence2C4_coeff_110
  recurrence2C4_coeff_111
  recurrence2C4_coeff_112
  recurrence2C4_coeff_113
  recurrence2C4_coeff_114
  recurrence2C4_coeff_115
  recurrence2C4_coeff_116
  recurrence2C4_coeff_117
  recurrence2C4_coeff_118
  recurrence2C4_coeff_119
  recurrence2C4_coeff_120
  recurrence2C4_coeff_121
  recurrence2C4_coeff_122
  recurrence2C4_coeff_123
  recurrence2C4_coeff_124
  recurrence2C4_coeff_125
  recurrence2C4_coeff_126
  recurrence2C4_coeff_127
  recurrence2C4_coeff_128
  recurrence2C4_coeff_129
  recurrence2C4_coeff_130
  recurrence2C4_coeff_131
  recurrence2C4_coeff_132
  recurrence2C4_coeff_133
  recurrence2C4_coeff_134
  recurrence2C4_coeff_135
  recurrence2C4_coeff_136
  recurrence2C4_coeff_137
  recurrence2C4_coeff_138
  recurrence2C4_coeff_139
  recurrence2C4_coeff_140
  recurrence2C4_coeff_141
  recurrence2C4_coeff_142
  recurrence2C4_coeff_143
  recurrence2C4_coeff_144
  recurrence2C4_coeff_145
  recurrence2C4_coeff_146
  recurrence2C4_coeff_147
  recurrence2C4_coeff_148
  recurrence2C4_coeff_149
  recurrence2C4_coeff_150
  recurrence2C4_coeff_151
  recurrence2C4_coeff_152
  recurrence2C4_coeff_153
  recurrence2C4_coeff_154
  recurrence2C4_coeff_155
  recurrence2C4_coeff_156
  recurrence2C4_coeff_157
  recurrence2C4_coeff_158
  recurrence2C4_coeff_159
  recurrence2C4_coeff_160
  recurrence2C4_coeff_161
  recurrence2C4_coeff_162
  recurrence2C4_coeff_163
  recurrence2C4_coeff_164
  recurrence2C4_coeff_165
  recurrence2C4_coeff_166
  recurrence2C4_coeff_167
  recurrence2C4_coeff_168
  recurrence2C4_coeff_169
  recurrence2C4_coeff_170
  recurrence2C4_coeff_171
  recurrence2C4_coeff_172
  recurrence2C4_coeff_173
  recurrence2C4_coeff_174
  recurrence2C4_coeff_175
  recurrence2C4_coeff_176
  recurrence2C4_coeff_177
  recurrence2C4_coeff_178

private theorem recurrence2Scalar4Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_262 :
    recurrence2Scalar4Exceptional.coeff 262 =
      -(((575022726094787759337198481519642167828018308406 * 10 ^ 70 +
        2632710713045506671719110345375200020118852681015113069629335336426476) * 10 ^ 70 +
        4025885879055168300527720898335846026143194151623310374814263034148513) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 84 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 14 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_263 :
    recurrence2Scalar4Exceptional.coeff 263 =
      (((167678852090430807723499534195808965197144357084 * 10 ^ 70 +
        2024315295733749452002813755788520404205485112878536041609873973774801) * 10 ^ 70 +
        4691917028930871549962132175614103248328699005330554960619679402409385) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 85 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 13 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_264 :
    recurrence2Scalar4Exceptional.coeff 264 =
      -(((35066649967830343182883750165194028346696709611 * 10 ^ 70 +
        5535750441454928343479647274189682576450113942700711937718403516583309) * 10 ^ 70 +
        0159750705734797593429233072010859281430036538869431437516320689969933) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 86 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_265 :
    recurrence2Scalar4Exceptional.coeff 265 =
      (((41779203627471408041033887357162194563447848 * 10 ^ 70 +
        7522918581010936690876960438961123527397614702594315070835566444640516) * 10 ^ 70 +
        2210209492836194273844319431835562839844486724574680201950138681076562) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 87 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 11 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_266 :
    recurrence2Scalar4Exceptional.coeff 266 =
      (((5663117074125394913949533327198455175267390397 * 10 ^ 70 +
        1402482523424696665559764611208967899942348446721060114798215840620025) * 10 ^ 70 +
        6304216027090463506124828395248208620222843505538889463853765742647168) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 88 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 10 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_267 :
    recurrence2Scalar4Exceptional.coeff 267 =
      -(((4395670956357391282092658382521099031780905567 * 10 ^ 70 +
        6717291359145146525735959590750471568822000089100158139253027095477869) * 10 ^ 70 +
        2820179033920463460134423420731564368599250004148613601911860143402889) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 89 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 9 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_268 :
    recurrence2Scalar4Exceptional.coeff 268 =
      (((2399681086219680201456429550826046278096210481 * 10 ^ 70 +
        4116089505566809607731017482204298783884778886879412702295990705496168) * 10 ^ 70 +
        6909684737301049026442477216458587178118995841240349580616128402739976) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 90 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 8 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_269 :
    recurrence2Scalar4Exceptional.coeff 269 =
      -(((1022672917594052677251941978339286921128064745 * 10 ^ 70 +
        3519920645500179704785071776377585838895322793772537883053851383164042) * 10 ^ 70 +
        4246043003976822049869457878631992311416469483692741081684392190215879) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 91 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 7 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_270 :
    recurrence2Scalar4Exceptional.coeff 270 =
      (((303704807581783561222964197198021825892062320 * 10 ^ 70 +
        7928012524653107764093289758711809940990031161091605144255477914443917) * 10 ^ 70 +
        8080701977304376650147994765907404038684170282705829253434327959373193) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 92 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 6 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_271 :
    recurrence2Scalar4Exceptional.coeff 271 =
      -(((13148772155267050875992660449807724321785686 * 10 ^ 70 +
        4002792877627628131308130651664659821404424260509682529123917136284194) * 10 ^ 70 +
        9593145445626604128955665288720766901029691537699431608602578627227114) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 93 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 5 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_272 :
    recurrence2Scalar4Exceptional.coeff 272 =
      -(((61754002719692596931219113462119234920624746 * 10 ^ 70 +
        2893335767253272701038663542811100222478838590328972442709403402908435) * 10 ^ 70 +
        8119505713120501314508015629242958399782540022212778324080609293708713) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 94 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 4 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_273 :
    recurrence2Scalar4Exceptional.coeff 273 =
      (((55074507417185054895679285996560048419767848 * 10 ^ 70 +
        8664870422009210773487479640810807109538155566561829502509995458651737) * 10 ^ 70 +
        9048722746369586197206908818447433664116795468676951319131301168562875) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 95 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 3 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_274 :
    recurrence2Scalar4Exceptional.coeff 274 =
      -(((31573604516090731364220172237098011461979255 * 10 ^ 70 +
        6623187505291376907451558488132547922445184182443284773529378915103264) * 10 ^ 70 +
        5978899047712831707218527798941832107922624165572929657901723678456116) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 96 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 2 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_275 :
    recurrence2Scalar4Exceptional.coeff 275 =
      (((13627931195738996295079993569478683438969391 * 10 ^ 70 +
        6022841872847468794965130373736804510215437608902785949781646011765458) * 10 ^ 70 +
        5370403121510412845338669095678317611013099072809285384565818254937565) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 97 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 1 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_276 :
    recurrence2Scalar4Exceptional.coeff 276 =
      -(((4257302776231725624333446109857866305980674 * 10 ^ 70 +
        5561051417804602335252400810462723839751972629695643637311171675056457) * 10 ^ 70 +
        6081089177529457812502872947438843486202598232604476136949298803426794) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 98 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_277 :
    recurrence2Scalar4Exceptional.coeff 277 =
      (((613698195033000718976352412192445921545953 * 10 ^ 70 +
        8668276961712893938718973914628427345617913394704385143326757998378075) * 10 ^ 70 +
        7164632808516734827233978995927777502426536956776712510039872949880470) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 99 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 31 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_278 :
    recurrence2Scalar4Exceptional.coeff 278 =
      (((324150583235314750101557901624873535145168 * 10 ^ 70 +
        7528741108175957959104810085110898965576018585128119212464523641718848) * 10 ^ 70 +
        9828238928158421331401639464350061107043780158042944356580315083645493) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 100 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 30 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_279 :
    recurrence2Scalar4Exceptional.coeff 279 =
      -(((338491146251273752440975973535868758454778 * 10 ^ 70 +
        8826684255686406150956524570091405919380306995030979876222565243120932) * 10 ^ 70 +
        4556574050681414549569624027106004139757984613554851187493880758120609) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 101 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 29 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_280 :
    recurrence2Scalar4Exceptional.coeff 280 =
      (((182001511212667257440203076252246798634427 * 10 ^ 70 +
        0298483872065719718378877338443467620915600347763690898843900650533392) * 10 ^ 70 +
        0253929491545054450793286509208126356298537197694306509945805125478790) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 102 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 28 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_281 :
    recurrence2Scalar4Exceptional.coeff 281 =
      -(((69906162063173590450311187775360524416380 * 10 ^ 70 +
        9924688500643642770037921961884392236553934326827506321637969757413500) * 10 ^ 70 +
        1178924432301624378757215626431261491612950607837632758349836957854829) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 103 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 27 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_282 :
    recurrence2Scalar4Exceptional.coeff 282 =
      (((18756371758666819886151188738910072989119 * 10 ^ 70 +
        0117176408851346550368635497520127966472866493351096412960320693792904) * 10 ^ 70 +
        0637206102315852649644102632150790390804745108650287898207925016583871) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 104 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_283 :
    recurrence2Scalar4Exceptional.coeff 283 =
      -(((2065898800959257635316519378140697158128 * 10 ^ 70 +
        0000621958254531930174692630388569562659688885129342047791087683229742) * 10 ^ 70 +
        0383009199304060331456304623500777490728685055536107604342661184418263) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 105 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 25 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_284 :
    recurrence2Scalar4Exceptional.coeff 284 =
      -(((1228791816696165620291446478299935740081 * 10 ^ 70 +
        2263906508210333914845660717768199339101106010067165849214594589276081) * 10 ^ 70 +
        1619582745361205323911328763557877523974708499822015795346168010542608) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 106 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 24 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_285 :
    recurrence2Scalar4Exceptional.coeff 285 =
      (((989031115554345134990080095419919044429 * 10 ^ 70 +
        2260058143089994458159683369264880855864192094104900003802531739257694) * 10 ^ 70 +
        5346606266056545437383582205098553351794571978865694149293184158327727) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 107 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 23 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_286 :
    recurrence2Scalar4Exceptional.coeff 286 =
      -(((420051979905012158529395774186639470420 * 10 ^ 70 +
        9016955834560818686578441483849346698735270367468257491360212542981458) * 10 ^ 70 +
        1353003952009040035085198904873910233647930470590622688257687774333159) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 108 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_287 :
    recurrence2Scalar4Exceptional.coeff 287 =
      (((120536130145503844034897237229926842888 * 10 ^ 70 +
        0376273644667166362819567343119606650073455754386412130308201074091992) * 10 ^ 70 +
        8141870056944101369715927369539288282667432385377772484673646754823493) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 109 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 21 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_288 :
    recurrence2Scalar4Exceptional.coeff 288 =
      -(((19268200331628781670068967286786574396 * 10 ^ 70 +
        4548946063844529107054675538906884582424577625335338353498311327707434) * 10 ^ 70 +
        9644221385633460108023223385650865544364723728702340465347055442979994) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 110 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 20 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_289 :
    recurrence2Scalar4Exceptional.coeff 289 =
      -(((2399241627878615036183098833660284521 * 10 ^ 70 +
        6876103020310320568913844756216699179837028888146196839070584356220132) * 10 ^ 70 +
        0216091137997701077084366009290518349644792279858275356338185571710221) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 111 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 19 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_290 :
    recurrence2Scalar4Exceptional.coeff 290 =
      (((3097983821735091685776910435531178370 * 10 ^ 70 +
        3874840347441255710461053249862010888525563930351700133683149150933725) * 10 ^ 70 +
        9791475050823348616345642078237454283573709610231278797326914007200893) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 112 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 18 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_291 :
    recurrence2Scalar4Exceptional.coeff 291 =
      -(((1287053590092959492894595571832944824 * 10 ^ 70 +
        4991342595026275655868130956972529136301761880773344845141942607462772) * 10 ^ 70 +
        1571670126488948187300132980228020930482332648684866739415708146890224) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 113 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 17 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_292 :
    recurrence2Scalar4Exceptional.coeff 292 =
      (((333063619524255994739629858052331440 * 10 ^ 70 +
        3486904581208771865142224886621275507533317270510671290234329250786692) * 10 ^ 70 +
        9899686033579492418789444397656298294621922121172391636398661410472309) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 114 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_293 :
    recurrence2Scalar4Exceptional.coeff 293 =
      -(((43964221280592098368831906383469542 * 10 ^ 70 +
        3737381531369365613099301426589108056815216509729270476933643594695748) * 10 ^ 70 +
        7613280268503084366829623982019173479277115651270186874439875960408879) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 115 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 15 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_294 :
    recurrence2Scalar4Exceptional.coeff 294 =
      -(((7043454770392603905586580971329736 * 10 ^ 70 +
        9316869830387571866278466652991647549685692264873055934987052600297596) * 10 ^ 70 +
        4756855170692682077212331663478410103045761299752764820326334500150784) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 116 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 14 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C4_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient4.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Exceptional_coeff_295 :
    recurrence2Scalar4Exceptional.coeff 295 =
      (((6266765281649131219079280429129283 * 10 ^ 70 +
        4038570785481171051737136565898710936532496757621377106789442198255668) * 10 ^ 70 +
        2725628190848368375701233119079623780365069530057494600918363595324738) : ℚ) := by
  unfold recurrence2Scalar4Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 117 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 13 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Exceptional_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
