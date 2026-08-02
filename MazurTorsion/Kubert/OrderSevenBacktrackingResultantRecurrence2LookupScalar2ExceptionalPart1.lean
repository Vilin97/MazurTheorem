/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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
  recurrence2C2_coeff_0
  recurrence2C2_coeff_1
  recurrence2C2_coeff_2
  recurrence2C2_coeff_3
  recurrence2C2_coeff_4
  recurrence2C2_coeff_5
  recurrence2C2_coeff_6
  recurrence2C2_coeff_7
  recurrence2C2_coeff_8
  recurrence2C2_coeff_9
  recurrence2C2_coeff_10
  recurrence2C2_coeff_11
  recurrence2C2_coeff_12
  recurrence2C2_coeff_13
  recurrence2C2_coeff_14
  recurrence2C2_coeff_15
  recurrence2C2_coeff_16
  recurrence2C2_coeff_17
  recurrence2C2_coeff_18
  recurrence2C2_coeff_19
  recurrence2C2_coeff_20
  recurrence2C2_coeff_21
  recurrence2C2_coeff_22
  recurrence2C2_coeff_23
  recurrence2C2_coeff_24
  recurrence2C2_coeff_25
  recurrence2C2_coeff_26
  recurrence2C2_coeff_27
  recurrence2C2_coeff_28
  recurrence2C2_coeff_29
  recurrence2C2_coeff_30
  recurrence2C2_coeff_31
  recurrence2C2_coeff_32
  recurrence2C2_coeff_33
  recurrence2C2_coeff_34
  recurrence2C2_coeff_35
  recurrence2C2_coeff_36
  recurrence2C2_coeff_37
  recurrence2C2_coeff_38
  recurrence2C2_coeff_39
  recurrence2C2_coeff_40
  recurrence2C2_coeff_41
  recurrence2C2_coeff_42
  recurrence2C2_coeff_43
  recurrence2C2_coeff_44
  recurrence2C2_coeff_45
  recurrence2C2_coeff_46
  recurrence2C2_coeff_47
  recurrence2C2_coeff_48
  recurrence2C2_coeff_49
  recurrence2C2_coeff_50
  recurrence2C2_coeff_51
  recurrence2C2_coeff_52
  recurrence2C2_coeff_53
  recurrence2C2_coeff_54
  recurrence2C2_coeff_55
  recurrence2C2_coeff_56
  recurrence2C2_coeff_57
  recurrence2C2_coeff_58
  recurrence2C2_coeff_59
  recurrence2C2_coeff_60
  recurrence2C2_coeff_61
  recurrence2C2_coeff_62
  recurrence2C2_coeff_63
  recurrence2C2_coeff_64
  recurrence2C2_coeff_65
  recurrence2C2_coeff_66
  recurrence2C2_coeff_67
  recurrence2C2_coeff_68
  recurrence2C2_coeff_69
  recurrence2C2_coeff_70
  recurrence2C2_coeff_71
  recurrence2C2_coeff_72
  recurrence2C2_coeff_73
  recurrence2C2_coeff_74
  recurrence2C2_coeff_75
  recurrence2C2_coeff_76
  recurrence2C2_coeff_77
  recurrence2C2_coeff_78
  recurrence2C2_coeff_79
  recurrence2C2_coeff_80
  recurrence2C2_coeff_81
  recurrence2C2_coeff_82
  recurrence2C2_coeff_83
  recurrence2C2_coeff_84
  recurrence2C2_coeff_85
  recurrence2C2_coeff_86
  recurrence2C2_coeff_87
  recurrence2C2_coeff_88
  recurrence2C2_coeff_89
  recurrence2C2_coeff_90
  recurrence2C2_coeff_91
  recurrence2C2_coeff_92
  recurrence2C2_coeff_93
  recurrence2C2_coeff_94
  recurrence2C2_coeff_95
  recurrence2C2_coeff_96
  recurrence2C2_coeff_97
  recurrence2C2_coeff_98
  recurrence2C2_coeff_99
  recurrence2C2_coeff_100
  recurrence2C2_coeff_101
  recurrence2C2_coeff_102
  recurrence2C2_coeff_103
  recurrence2C2_coeff_104
  recurrence2C2_coeff_105
  recurrence2C2_coeff_106
  recurrence2C2_coeff_107
  recurrence2C2_coeff_108
  recurrence2C2_coeff_109
  recurrence2C2_coeff_110
  recurrence2C2_coeff_111
  recurrence2C2_coeff_112
  recurrence2C2_coeff_113
  recurrence2C2_coeff_114
  recurrence2C2_coeff_115
  recurrence2C2_coeff_116
  recurrence2C2_coeff_117
  recurrence2C2_coeff_118
  recurrence2C2_coeff_119
  recurrence2C2_coeff_120
  recurrence2C2_coeff_121
  recurrence2C2_coeff_122
  recurrence2C2_coeff_123
  recurrence2C2_coeff_124
  recurrence2C2_coeff_125
  recurrence2C2_coeff_126
  recurrence2C2_coeff_127
  recurrence2C2_coeff_128
  recurrence2C2_coeff_129
  recurrence2C2_coeff_130
  recurrence2C2_coeff_131
  recurrence2C2_coeff_132
  recurrence2C2_coeff_133
  recurrence2C2_coeff_134
  recurrence2C2_coeff_135
  recurrence2C2_coeff_136
  recurrence2C2_coeff_137
  recurrence2C2_coeff_138
  recurrence2C2_coeff_139
  recurrence2C2_coeff_140
  recurrence2C2_coeff_141
  recurrence2C2_coeff_142
  recurrence2C2_coeff_143
  recurrence2C2_coeff_144
  recurrence2C2_coeff_145
  recurrence2C2_coeff_146
  recurrence2C2_coeff_147
  recurrence2C2_coeff_148
  recurrence2C2_coeff_149
  recurrence2C2_coeff_150
  recurrence2C2_coeff_151
  recurrence2C2_coeff_152
  recurrence2C2_coeff_153
  recurrence2C2_coeff_154
  recurrence2C2_coeff_155
  recurrence2C2_coeff_156
  recurrence2C2_coeff_157
  recurrence2C2_coeff_158
  recurrence2C2_coeff_159
  recurrence2C2_coeff_160
  recurrence2C2_coeff_161
  recurrence2C2_coeff_162
  recurrence2C2_coeff_163
  recurrence2C2_coeff_164
  recurrence2C2_coeff_165
  recurrence2C2_coeff_166
  recurrence2C2_coeff_167
  recurrence2C2_coeff_168
  recurrence2C2_coeff_169
  recurrence2C2_coeff_170
  recurrence2C2_coeff_171
  recurrence2C2_coeff_172
  recurrence2C2_coeff_173
  recurrence2C2_coeff_174
  recurrence2C2_coeff_175
  recurrence2C2_coeff_176
  recurrence2C2_coeff_177
  recurrence2C2_coeff_178
  recurrence2C2_coeff_179
  recurrence2C2_coeff_180
  recurrence2C2_coeff_181
  recurrence2C2_coeff_182
  recurrence2C2_coeff_183
  recurrence2C2_coeff_184
  recurrence2C2_coeff_185
  recurrence2C2_coeff_186

private theorem recurrence2Scalar2Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (231 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_231 :
    recurrence2Scalar2Exceptional.coeff 231 =
      (((552784354652433930758462639452792623511812871254837912058370 * 10 ^ 70 +
        1789168214523650790596109913650277139459295681613639260515776684931084) * 10 ^ 70 +
        3714359115867824265721642690190092804828848839502112098758254243530921) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 45 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 21 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (232 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_232 :
    recurrence2Scalar2Exceptional.coeff 232 =
      -(((255071974749057787875794846335851851419651874466262835697339 * 10 ^ 70 +
        7322418350138417884622871023440651083542204507606605343529501720403794) * 10 ^ 70 +
        6648671273242396458678755592305420091979628869291789574029530405548230) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 46 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 20 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (233 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_233 :
    recurrence2Scalar2Exceptional.coeff 233 =
      (((59940769027738858741029829327669364665898562491547124762628 * 10 ^ 70 +
        6286719360696723779477548473913536190590698740736608369465353405923285) * 10 ^ 70 +
        5018507381080209387982072566727902357952954355999663955040238088817977) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 47 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 19 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (234 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_234 :
    recurrence2Scalar2Exceptional.coeff 234 =
      (((48172080324132394881379974533670616445138734952397558784026 * 10 ^ 70 +
        6117599427471044726582583842916128261533191190153419384961556023871495) * 10 ^ 70 +
        2211978641073636338623202685872463117642035032146709860194851036617332) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 48 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 18 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (235 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_235 :
    recurrence2Scalar2Exceptional.coeff 235 =
      -(((92547099973373691589147220279876310228016428819755009791664 * 10 ^ 70 +
        0504334633951260447344631162546393589212028701690030106185659475948966) * 10 ^ 70 +
        4270887353662748504310267307553595939010465034654799955170718225131775) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 49 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 17 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (236 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_236 :
    recurrence2Scalar2Exceptional.coeff 236 =
      (((96908774113428256347971902784435289689999950265247424146496 * 10 ^ 70 +
        0321427782045027709775820942063928518698785449295011745988622501182238) * 10 ^ 70 +
        2539564458930997561238575661511274872397475338652688648018825951451105) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 50 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 16 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (237 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_237 :
    recurrence2Scalar2Exceptional.coeff 237 =
      -(((80907885607549477579538322409993723560318539858248129636630 * 10 ^ 70 +
        5490940839220451779579590192226398589110018417173146464507004938614174) * 10 ^ 70 +
        4233019525090313319621208140245185390502776567569107496706646724541931) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 51 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 15 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (238 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_238 :
    recurrence2Scalar2Exceptional.coeff 238 =
      (((58286249624251151737649928005327798784085498838206967678546 * 10 ^ 70 +
        7417797439567474787251722488481164829487332571382091511028130943279552) * 10 ^ 70 +
        3706183825734044346364643557862429487360795068823479628676542596807864) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 52 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 14 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (239 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_239 :
    recurrence2Scalar2Exceptional.coeff 239 =
      -(((37033218825409129308022656800080610895206292440342427861194 * 10 ^ 70 +
        2850958101098534464982900169353876178393071673967429290952972127065370) * 10 ^ 70 +
        9069221730923753966802302543663500701997514566470071611263519170290882) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 53 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 13 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (240 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_240 :
    recurrence2Scalar2Exceptional.coeff 240 =
      (((20646998479583013102913986568572637471456368004543632137957 * 10 ^ 70 +
        0539614276415827291702214193518255030687289336060159413726213415300445) * 10 ^ 70 +
        2127215773803181242584263075047025811052961838098031147867339731317312) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 54 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 12 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (241 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_241 :
    recurrence2Scalar2Exceptional.coeff 241 =
      -(((9726968134542566688291388911214216618424908426373285623737 * 10 ^ 70 +
        5678573057359115564557339433339735247298820015487708626139011372691702) * 10 ^ 70 +
        8076527228509190654233740757846208115935700230445744441942591898327446) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 55 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 11 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (242 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_242 :
    recurrence2Scalar2Exceptional.coeff 242 =
      (((3387570508148279669288185617988517319916318410679615504453 * 10 ^ 70 +
        5016111989482037404473674526602130288529855199461707312061068477623240) * 10 ^ 70 +
        6530982971684188716548666138411882190793532424924629454921137370008204) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 56 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 10 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (243 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_243 :
    recurrence2Scalar2Exceptional.coeff 243 =
      -(((262556764480850674601222247784986584053271341296069031433 * 10 ^ 70 +
        0998469841873870988810139550973855730277291815653994231171125491484439) * 10 ^ 70 +
        1195188244312844721906749237895480959226317444552609873355567915738600) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 57 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 9 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (244 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_244 :
    recurrence2Scalar2Exceptional.coeff 244 =
      -(((922027620892773007062752228113157266527151206126989379001 * 10 ^ 70 +
        3148170515431847498963436519913744515660322094078003800601744796687372) * 10 ^ 70 +
        9152918257236227496550406790157167457221889458488125317981129031292546) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 58 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 8 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (245 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_245 :
    recurrence2Scalar2Exceptional.coeff 245 =
      (((1112592968074157590592761230785738515851455450779462013441 * 10 ^ 70 +
        4845472915607052504198148559709231107577792143610084658909120522393509) * 10 ^ 70 +
        2406518665870501433700418626367785042313338744671292319372239298484472) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 59 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 7 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (246 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_246 :
    recurrence2Scalar2Exceptional.coeff 246 =
      -(((902799503093460215738974146078111345941554075770598192941 * 10 ^ 70 +
        7848959102647492643791807181478381935112006358017433382001058896240689) * 10 ^ 70 +
        5524381611220608644332867261862362395281652325875631558933972286625638) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 60 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 6 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (247 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_247 :
    recurrence2Scalar2Exceptional.coeff 247 =
      (((606997675219658726159965070950330329601033833684171361552 * 10 ^ 70 +
        7675008738607761191617650650005598583676214282282643105613306679027768) * 10 ^ 70 +
        8909863529205191084923619096448886057869240863212256626753659797418879) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 61 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 5 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (248 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_248 :
    recurrence2Scalar2Exceptional.coeff 248 =
      -(((357576612684157814128300308694140009640407453434346090759 * 10 ^ 70 +
        0530976936629382619378789939742919596444068449364789420745266063396491) * 10 ^ 70 +
        3432390092914289116665262510527202773921918812936373373385326864682704) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 62 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 4 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (249 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_249 :
    recurrence2Scalar2Exceptional.coeff 249 =
      (((187783982550808580357376402207504543778840977514584373421 * 10 ^ 70 +
        9894708763685939562071537365152103281071933453689875708150984094809430) * 10 ^ 70 +
        7820759296837218847044361012654909173122182436872422559354490398324921) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 63 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 3 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (250 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_250 :
    recurrence2Scalar2Exceptional.coeff 250 =
      -(((87721344982238806803539833461890859750422554182984702850 * 10 ^ 70 +
        7746206731899960961074694584223010443311304970793332907581038040265472) * 10 ^ 70 +
        1115722054498075961335952137079858018841071929932166521366385246794812) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 64 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 2 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (251 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_251 :
    recurrence2Scalar2Exceptional.coeff 251 =
      (((35600899156879374306013508614270004087594279384467994486 * 10 ^ 70 +
        7269720649327267285921399582255963980677909539159274078932123605806294) * 10 ^ 70 +
        7499390398777044625980906396141665445040816313845538914882060896672790) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 65 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 1 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (252 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_252 :
    recurrence2Scalar2Exceptional.coeff 252 =
      -(((11667389910389588388164698094005833221663086848228247934 * 10 ^ 70 +
        8562947312505831661366248750523889351334288210211840707498870059554753) * 10 ^ 70 +
        8820899631329482020480150409871354037141058934823222833488025855085655) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 66 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (253 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_253 :
    recurrence2Scalar2Exceptional.coeff 253 =
      (((2251419739677074361652430267098069213496429062976793303 * 10 ^ 70 +
        9374012384112140906884223471147661643654397597324323748629207936948319) * 10 ^ 70 +
        6418760064277338433650776551319047103514888280876641027685488667121888) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 67 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 31 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (254 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_254 :
    recurrence2Scalar2Exceptional.coeff 254 =
      (((637475222517754442734037680351242887594194060832424385 * 10 ^ 70 +
        9275159463864750228894929294710736767480626009796937017527269468467076) * 10 ^ 70 +
        1985089715160115113747153008630862788894987655443971212159176885860101) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 68 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 30 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (255 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_255 :
    recurrence2Scalar2Exceptional.coeff 255 =
      -(((1053748487683121107516166222506554858600843189999809375 * 10 ^ 70 +
        0363781281327575927015391725147888070285807459602377650299734247942431) * 10 ^ 70 +
        9328658895072812841788236513990196913834846379169199234135307356624864) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 69 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 29 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (256 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_256 :
    recurrence2Scalar2Exceptional.coeff 256 =
      (((773694993611066968160092571536070611860599244168379038 * 10 ^ 70 +
        6179619812359607619011289519771242040105021955994858418656414955668518) * 10 ^ 70 +
        3723720434043746312845423996974010670322938555291039053321087423440600) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 70 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 28 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (257 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_257 :
    recurrence2Scalar2Exceptional.coeff 257 =
      -(((439688309468970457290467341799760195914209488620361405 * 10 ^ 70 +
        8228296278715177774010074940222824785751632167332530700096951422916580) * 10 ^ 70 +
        3296610615662980405924855790257692289742979937134618903892841962500463) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 71 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 27 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (258 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_258 :
    recurrence2Scalar2Exceptional.coeff 258 =
      (((212793299342856833839053377369359954812545246831088850 * 10 ^ 70 +
        6924320038775870228568318110051656928227913419959171000390938550458077) * 10 ^ 70 +
        3973959554498507079704391899764656057231478408022155832792520558005351) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 72 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 26 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (259 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_259 :
    recurrence2Scalar2Exceptional.coeff 259 =
      -(((89796650442966042492913222341599518012241420245548091 * 10 ^ 70 +
        5891337298296137481289788308943370023565413723893320994988465211951526) * 10 ^ 70 +
        5308220239643347198045810406962250625220096152104806920613216624424665) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 73 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 25 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (260 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_260 :
    recurrence2Scalar2Exceptional.coeff 260 =
      (((32670760570195642837953305445026011550662441711621570 * 10 ^ 70 +
        7213651909317300319897475599737807550251067486617605511237075019542239) * 10 ^ 70 +
        8301264490853517831359689119183250099958209677052371402933209048206923) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 74 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 24 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (261 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_261 :
    recurrence2Scalar2Exceptional.coeff 261 =
      -(((9629091384981221792945180894991288782551293101037913 * 10 ^ 70 +
        2549968104166771050195079462061790250553284878627191600018099768368131) * 10 ^ 70 +
        2487901249822569919376615193560309337268698524007589423230398827760830) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 75 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 23 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (262 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_262 :
    recurrence2Scalar2Exceptional.coeff 262 =
      (((1750371422170842361714800837589581261180070468565533 * 10 ^ 70 +
        6665688942068635049271586908729732158280272191767666350871710202061825) * 10 ^ 70 +
        0149781354541365110004574037680526764548743521297351703162580697703675) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 76 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 22 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (263 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_263 :
    recurrence2Scalar2Exceptional.coeff 263 =
      (((311965556430972384890604735726328773865185986817609 * 10 ^ 70 +
        0141667749943978102712380711894594884241684442448906537732361093846613) * 10 ^ 70 +
        0028190238908208748308300553723012666054616223540613355544030274909734) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 77 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 21 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (264 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_264 :
    recurrence2Scalar2Exceptional.coeff 264 =
      -(((530593836264933805365345827550430853322105393301232 * 10 ^ 70 +
        9465433175806202156833823104690481772261808112947411650417158760516066) * 10 ^ 70 +
        1842931897963653295628711522453311309777225810607293550021698974436453) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 78 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 20 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (265 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_265 :
    recurrence2Scalar2Exceptional.coeff 265 =
      (((344900487900388824079563653599170651304621552848195 * 10 ^ 70 +
        4990805701451841201376692276877091939457849430951773547634545317289417) * 10 ^ 70 +
        6174750003323999466618129246905499660870774526589479097109943718056766) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 79 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 19 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (266 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_266 :
    recurrence2Scalar2Exceptional.coeff 266 =
      -(((168843619826711632991801451029881002578671303643594 * 10 ^ 70 +
        4386899281386328292171139475308777512533033497316715531745830023903188) * 10 ^ 70 +
        3986433291849433356826725922318979804419394895635028339190110053892290) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 80 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 18 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (267 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_267 :
    recurrence2Scalar2Exceptional.coeff 267 =
      (((68827501250110407117028171692860032756756823453333 * 10 ^ 70 +
        1123763538547862227685443333701360152061694768266266893909211646796239) * 10 ^ 70 +
        0713083549240207410483667755423508443003796343996702042121345776943922) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 81 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 17 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (268 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_268 :
    recurrence2Scalar2Exceptional.coeff 268 =
      -(((23897471023767231508586826957211613256505680049936 * 10 ^ 70 +
        9721335523748634200613455940835276117301732243862806000163789052137638) * 10 ^ 70 +
        7829393622651725514071199110499352037088848710743179732613579609276561) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 82 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 16 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (269 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_269 :
    recurrence2Scalar2Exceptional.coeff 269 =
      (((7038837491558450252619125080474731257040841336741 * 10 ^ 70 +
        6676116419338913528571475630298854320046143680550903912528630850076874) * 10 ^ 70 +
        9582412292501191161390194891102133710704534532436529146301104229707606) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 83 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 15 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (270 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_270 :
    recurrence2Scalar2Exceptional.coeff 270 =
      -(((1746393425905647613515845202106618740503723736385 * 10 ^ 70 +
        7009658367351753951477926860145834672901493435508128306786897176716077) * 10 ^ 70 +
        2900417195389137122211906966004115437422826522508596767805569491363583) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 84 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 14 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (271 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_271 :
    recurrence2Scalar2Exceptional.coeff 271 =
      (((390944837008536232662200418259289054631123054882 * 10 ^ 70 +
        1964530823471878737561806702046711609035510425537253479002112363635994) * 10 ^ 70 +
        4938213873693654067990970762265683752355175574961785316913614116359750) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 85 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 13 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (272 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_272 :
    recurrence2Scalar2Exceptional.coeff 272 =
      -(((113024002451601375880740502017451322805264006243 * 10 ^ 70 +
        5549631949093500117094425653280102997951293754425492755380009118586804) * 10 ^ 70 +
        4520822839009768323026951652118445336874033549833283145571774664914061) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 86 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 12 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (273 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_273 :
    recurrence2Scalar2Exceptional.coeff 273 =
      (((54578357646183583908814843173658143338836623820 * 10 ^ 70 +
        0875678996264384971548501836692291919528240646357217554455255570547747) * 10 ^ 70 +
        9441764058022994076601200857197703723806320497807364593089102755493746) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 87 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 11 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (274 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_274 :
    recurrence2Scalar2Exceptional.coeff 274 =
      -(((26945752836193164093020437500440587107554070550 * 10 ^ 70 +
        0726147044359837993376344538995050594119558947487657511596902012883421) * 10 ^ 70 +
        7185059484763680282055191896947856342241866841598239309126333044616395) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 88 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 10 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (275 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_275 :
    recurrence2Scalar2Exceptional.coeff 275 =
      (((8125753056556697696286732239201468392565493961 * 10 ^ 70 +
        4890535602100244361055489869159037775607425228510346612698022404880305) * 10 ^ 70 +
        2696478741282741373582026389571176611607522054478956877284687168130861) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 89 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 9 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (276 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_276 :
    recurrence2Scalar2Exceptional.coeff 276 =
      (((1414821526824699234413477378851705996946437498 * 10 ^ 70 +
        3988847926998264904420812616455481670501936119731102472145530601453763) * 10 ^ 70 +
        5740802343277538850478148785703489213456090085940751481834335761444350) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 90 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 8 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (277 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_277 :
    recurrence2Scalar2Exceptional.coeff 277 =
      -(((4005897262975037512738367681893531637341087802 * 10 ^ 70 +
        3666267877802618502940727959004250313795220565008300393179049743821181) * 10 ^ 70 +
        2826913761681242856050004997389573274170639873691891856265055216087814) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 91 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 7 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (278 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_278 :
    recurrence2Scalar2Exceptional.coeff 278 =
      (((3345228176540276371804741579384905786910690115 * 10 ^ 70 +
        8091770215939509636498199720113857805202134101819598454380679065760824) * 10 ^ 70 +
        4815717875865776648617614977250162158204430337929611262469048394757410) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 92 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 6 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (279 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_279 :
    recurrence2Scalar2Exceptional.coeff 279 =
      -(((1964953887887406427598277797666706172820992710 * 10 ^ 70 +
        8603448283168380876555493127483902713906134660144075735188287850245442) * 10 ^ 70 +
        7232176255467159379927605722526921179196815552226804679418289267752150) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 93 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 5 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (280 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_280 :
    recurrence2Scalar2Exceptional.coeff 280 =
      (((904438307255582041257839467120960677392282539 * 10 ^ 70 +
        1655162185406202790618320526959502080258727125908627961350701376451943) * 10 ^ 70 +
        7069199870127777124794384727291867460378772238143332330381476468786972) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 94 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 4 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (281 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_281 :
    recurrence2Scalar2Exceptional.coeff 281 =
      -(((323895734877359746477971086231382821598918158 * 10 ^ 70 +
        0131457589661761409002917386012765671400736141817959961970710727587314) * 10 ^ 70 +
        8056487936212359319372915938825842440510833476929630821169993542007058) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 95 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 3 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (282 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_282 :
    recurrence2Scalar2Exceptional.coeff 282 =
      (((77209092170927876593462980052832546108579289 * 10 ^ 70 +
        0900392085186915865007729425404645451442029103257006866454581131907521) * 10 ^ 70 +
        4474027313445616442924790417107559667198055869223828574517423479421836) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 96 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 2 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (283 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_283 :
    recurrence2Scalar2Exceptional.coeff 283 =
      (((1026043635217218094887550433735033242777295 * 10 ^ 70 +
        5811836313511546457770352172072429058740824275184913988241240623813204) * 10 ^ 70 +
        6364934251767483307813183255812898152639716433957143792664971511551465) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 97 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 1 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (284 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_284 :
    recurrence2Scalar2Exceptional.coeff 284 =
      -(((14233189156523677521421212883005881549755041 * 10 ^ 70 +
        5074034108029359172357253726307860658364889863922691084341291308018545) * 10 ^ 70 +
        8651973453690273369461242749001231139922346466663166746689663254432381) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 98 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_285 :
    recurrence2Scalar2Exceptional.coeff 285 =
      (((10027854606738741094584063892338723108987245 * 10 ^ 70 +
        1718558507137470627072866287852645029894716370506432677232440970315351) * 10 ^ 70 +
        3828484254346483336435798836344504144648242901799781088373013476966836) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 99 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 31 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_286 :
    recurrence2Scalar2Exceptional.coeff 286 =
      -(((4737633970617453263620236143868099127029615 * 10 ^ 70 +
        1546706873029290775832932382181900502644857011476370464316347656290501) * 10 ^ 70 +
        3498438095029078861643331683345406594164154933761678198605528370381415) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 100 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 30 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_287 :
    recurrence2Scalar2Exceptional.coeff 287 =
      (((1699741327005970739476457715555518169130804 * 10 ^ 70 +
        3498878829645622018045199387198646972400780998077177206733890379322931) * 10 ^ 70 +
        1826921932932058539486640703834306185075194812753329674904960941137023) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 101 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 29 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_288 :
    recurrence2Scalar2Exceptional.coeff 288 =
      -(((439600394059449182657731189733529940535252 * 10 ^ 70 +
        9317376724555468455319228142615956466048306306866880581336226545718742) * 10 ^ 70 +
        4157099471201440697344912370621256829845498462499933218512978361188800) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 102 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 28 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_289 :
    recurrence2Scalar2Exceptional.coeff 289 =
      (((49026373579864332843063895555217624257928 * 10 ^ 70 +
        8350860472759634925502156710097943482413739150979812994978186185758902) * 10 ^ 70 +
        5996896103798233887009674661977766482365347045339498257386248282417898) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 103 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 27 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_290 :
    recurrence2Scalar2Exceptional.coeff 290 =
      (((26609312891049027578063872129770689035510 * 10 ^ 70 +
        2743004588636872224777139057522188025626095445764303671102615806520951) * 10 ^ 70 +
        4055708160750659261282257969964837607498819728621968995782715131669864) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 104 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 26 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_291 :
    recurrence2Scalar2Exceptional.coeff 291 =
      -(((21978527562175569443283712955674585502311 * 10 ^ 70 +
        1851652782489799665642676996609514932132280767178312662015020429255369) * 10 ^ 70 +
        2176710696081443963106681632602460442168960806112433639967028760057350) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 105 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 25 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_292 :
    recurrence2Scalar2Exceptional.coeff 292 =
      (((9625012012044214306083008292549816726903 * 10 ^ 70 +
        2155917649770241408534876025739050804998466373567719375536429095927802) * 10 ^ 70 +
        6551165033792024891986779088058998650483179002444033823703100303826605) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 106 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 24 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_293 :
    recurrence2Scalar2Exceptional.coeff 293 =
      -(((2946652673882779575915358828464182652288 * 10 ^ 70 +
        1843731659658036770790063472516463483196886987070404741679160481191739) * 10 ^ 70 +
        2155613347620943275934729305300642689043812188636972957284705681396167) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 107 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 23 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_294 :
    recurrence2Scalar2Exceptional.coeff 294 =
      (((574888698355983469906374561152230524043 * 10 ^ 70 +
        0322353608815529129874783518329749854556037023047251248337521725769553) * 10 ^ 70 +
        0549777032444000284760621425730272628122080330239962630686911705781441) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 108 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 22 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_295 :
    recurrence2Scalar2Exceptional.coeff 295 =
      -(((2281792391198616732491703663866644051 * 10 ^ 70 +
        8978463875407283797950755039804717958722103123619577849093699500326532) * 10 ^ 70 +
        0759427117807614887513696267817800386754495842245915569780325467675133) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 109 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 21 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (296 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_296 :
    recurrence2Scalar2Exceptional.coeff 296 =
      -(((54912379832166583096012259532806802666 * 10 ^ 70 +
        9692949320153554905179648630328886920255554134332429607483414476482599) * 10 ^ 70 +
        0640378609853263786187569826294000535197541563818333003430930826664284) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 110 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 20 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (297 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_297 :
    recurrence2Scalar2Exceptional.coeff 297 =
      (((27398944128386042751714383532672033653 * 10 ^ 70 +
        2510397270619468062018300308836295165556487328563028311362645129981963) * 10 ^ 70 +
        3724582047176747472340806179164853451312332797098943259234416484688088) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 111 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 19 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (298 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_298 :
    recurrence2Scalar2Exceptional.coeff 298 =
      -(((8260073726373629222334366477333473922 * 10 ^ 70 +
        3860338333524948030752850630526214531889923061001947835392702781543732) * 10 ^ 70 +
        2804717156293907607663160890172709746914353076035531317211003541136700) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 112 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 18 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (299 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_299 :
    recurrence2Scalar2Exceptional.coeff 299 =
      (((1516622296025270646006076900723155588 * 10 ^ 70 +
        2248187409539777745055127912521488005285604513217411713079964649918927) * 10 ^ 70 +
        1076804583297964541938098919224148711199815377314899323543586228439803) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 113 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 17 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (300 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_300 :
    recurrence2Scalar2Exceptional.coeff 300 =
      -(((17568907265820501076075392798108511 * 10 ^ 70 +
        0867466793639262722197490607441697422906255631927282708141088217730289) * 10 ^ 70 +
        2019354141304949251000712114162774207632200018685790496559277879395638) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 114 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 16 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (301 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_301 :
    recurrence2Scalar2Exceptional.coeff 301 =
      -(((107242287369794411994067759317872990 * 10 ^ 70 +
        3044547510511204084193460779362101002817473610495284681635842262449184) * 10 ^ 70 +
        7160632318481854947295798570362411704319897489395903424956067825547149) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 115 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 15 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (302 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_302 :
    recurrence2Scalar2Exceptional.coeff 302 =
      (((45682872420415285193470592772612877 * 10 ^ 70 +
        2135595369692850840891768474357016445585284425691980245112657103796933) * 10 ^ 70 +
        1028499134411522201247859859145974176870422637514366695242854475186814) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 116 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 14 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (303 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_303 :
    recurrence2Scalar2Exceptional.coeff 303 =
      -(((10918299824118076270698777157050231 * 10 ^ 70 +
        7011560065044214924421614085572622645349190106786949197293210928255555) * 10 ^ 70 +
        5617247021703847301228555328162464789656395823550129269421305433472806) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 117 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 13 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (304 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_304 :
    recurrence2Scalar2Exceptional.coeff 304 =
      (((1243697152248162409097199484491549 * 10 ^ 70 +
        4846557356912137538541444121235685086825028276051532768932566014340675) * 10 ^ 70 +
        3153144841829562575194907600549541184588757579892755445842487196201465) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 118 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 12 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (305 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_305 :
    recurrence2Scalar2Exceptional.coeff 305 =
      (((207079654429976399587512395649315 * 10 ^ 70 +
        3961936504228315951880209027057255985183245429615683342890393331026268) * 10 ^ 70 +
        5470094611408159853052286147015835026403977616704034115791091570469754) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 119 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 11 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (306 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_306 :
    recurrence2Scalar2Exceptional.coeff 306 =
      -(((144721731307245425688924475436016 * 10 ^ 70 +
        0405244817553716671767509650929169619184268379603477319447826475067802) * 10 ^ 70 +
        3485593843377110632126429889128129853813280765605313188864236231752686) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 120 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 10 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (307 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_307 :
    recurrence2Scalar2Exceptional.coeff 307 =
      (((37721906242627070918398248788349 * 10 ^ 70 +
        6118606748813566225127723508021844575558692311278802274749872516465016) * 10 ^ 70 +
        5249822893526863452343291654090999238245135578101802091962189762474101) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 121 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 9 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (308 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_308 :
    recurrence2Scalar2Exceptional.coeff 308 =
      -(((4793882870634908732974260026033 * 10 ^ 70 +
        0006067197530168657391425801953045038772975877248104188741813694505597) * 10 ^ 70 +
        8493558756683604042196461945900929274849821264626593532270284698644374) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 122 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 8 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (309 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_309 :
    recurrence2Scalar2Exceptional.coeff 309 =
      -(((341055477333835379312982797581 * 10 ^ 70 +
        1852508280364400357626789282990665954806341116382362142828123443014559) * 10 ^ 70 +
        9034721131345781953430153361165354656781632022706874297778424820782777) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 123 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 7 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (310 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_310 :
    recurrence2Scalar2Exceptional.coeff 310 =
      (((319549007103991988280575184643 * 10 ^ 70 +
        2067137556743691159813098383200953193751311930355377276310129675182644) * 10 ^ 70 +
        9622851273948836728871159034702836350784015491009034727301566342985058) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 124 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 6 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (311 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_311 :
    recurrence2Scalar2Exceptional.coeff 311 =
      -(((75438669017306721536332785106 * 10 ^ 70 +
        3885633399216576960262655088821238528906723870301825555169465874121121) * 10 ^ 70 +
        0924393440293512341113189709541767799260730758397523796273664392102832) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 125 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 5 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (312 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_312 :
    recurrence2Scalar2Exceptional.coeff 312 =
      (((7325747123534633412076998504 * 10 ^ 70 +
        3746468246706505382426320275729265952334660836582114254882779232021504) * 10 ^ 70 +
        6727790977837840353528182194941643815783933605529161739731290454646249) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 126 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 4 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (313 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_313 :
    recurrence2Scalar2Exceptional.coeff 313 =
      (((1000147800224175411643826818 * 10 ^ 70 +
        9043687577881766270142320648690527372734333137697200956966511171206472) * 10 ^ 70 +
        7857335604985078696223457573314768086878369736998644867378666449549620) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 127 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 3 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (314 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_314 :
    recurrence2Scalar2Exceptional.coeff 314 =
      -(((503827678286081861419181200 * 10 ^ 70 +
        3873770195029118539497150999479055948709431657451508423398736654673839) * 10 ^ 70 +
        9400847465155178659842049763591129896854138840861657759444710851116474) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 128 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 2 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (315 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_315 :
    recurrence2Scalar2Exceptional.coeff 315 =
      (((81874804671940265859552595 * 10 ^ 70 +
        2940594855773183558550468883513479032229011311922027234019831662801486) * 10 ^ 70 +
        2203629483672929620340955531348266266747101554952355248808708105741723) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 129 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 1 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (316 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_316 :
    recurrence2Scalar2Exceptional.coeff 316 =
      -(((1854921481429163296578276 * 10 ^ 70 +
        5345802574154246197682176010546961618980411691008201391794121397841753) * 10 ^ 70 +
        3072158993789098474030836265010762378892934662538971996839486647621600) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 130 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (317 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_317 :
    recurrence2Scalar2Exceptional.coeff 317 =
      -(((2041588420925511602295904 * 10 ^ 70 +
        3091104615110597065651336924240675708877819667294122198227775803559838) * 10 ^ 70 +
        6355012738197634975187086521258017155458588349238553315716104106330208) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 131 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 31 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (318 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_318 :
    recurrence2Scalar2Exceptional.coeff 318 =
      (((443901168895715940596470 * 10 ^ 70 +
        6614587604652287620609300110635361468277644733037212388738725016623264) * 10 ^ 70 +
        1462976226712179521956939669561199716043138225231778436067463492313805) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 132 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 30 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (319 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_319 :
    recurrence2Scalar2Exceptional.coeff 319 =
      -(((27134951489994032037365 * 10 ^ 70 +
        6473867892700604121629228343354462806885491122348807827356535898174891) * 10 ^ 70 +
        6113726626456556925360461914940987990235102167477378537388231646684703) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 133 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 29 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (320 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_320 :
    recurrence2Scalar2Exceptional.coeff 320 =
      -(((6187189960839707899084 * 10 ^ 70 +
        6599709173011766837389482096541967082820145624610700447172363342636122) * 10 ^ 70 +
        0141104337898856946390686786355052302534611111389488840290812045730926) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 134 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 28 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (321 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_321 :
    recurrence2Scalar2Exceptional.coeff 321 =
      (((1588699909188841273318 * 10 ^ 70 +
        5474218913114297859260526797433862144124635876101131200697956236737718) * 10 ^ 70 +
        9142919520153942995640653867680133224076099311725918756274031308274809) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 135 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 27 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (322 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_322 :
    recurrence2Scalar2Exceptional.coeff 322 =
      -(((101481457762941132160 * 10 ^ 70 +
        2840353776763065024117075130565495359665520764309341686316806106067232) * 10 ^ 70 +
        9022371488032118550753934695269027021419536277126658406805376922392218) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 136 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 26 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (323 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_323 :
    recurrence2Scalar2Exceptional.coeff 323 =
      -(((17561880775566355960 * 10 ^ 70 +
        8616931982216303016934833460197368634298373512464469837647517464364244) * 10 ^ 70 +
        4684332835458169133811892998125500363697209300383805229923882655813264) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 137 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 25 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (324 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_324 :
    recurrence2Scalar2Exceptional.coeff 324 =
      (((4041281742346528630 * 10 ^ 70 +
        6135049135662906137328271776742333701432309901728959262224795297059709) * 10 ^ 70 +
        1023799262206490179838949662159793471531510139304941553802303972173564) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 138 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 24 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (325 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_325 :
    recurrence2Scalar2Exceptional.coeff 325 =
      -(((160527860315960745 * 10 ^ 70 +
        0524141624947267914503866578330226860902052500544048389063137786389814) * 10 ^ 70 +
        8937792673386279182552423377789813949588346590991584635799750696054742) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 139 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 23 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (326 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_326 :
    recurrence2Scalar2Exceptional.coeff 326 =
      -(((47153268548959551 * 10 ^ 70 +
        3215561545237843842076470882990880715809366050712617455883523440972592) * 10 ^ 70 +
        4939559656190074002570915156448662777996123054821870413965581827857246) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 140 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 22 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (327 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_327 :
    recurrence2Scalar2Exceptional.coeff 327 =
      (((6712575433197638 * 10 ^ 70 +
        8326404438058031696076564364111840924056898512247789580629953581136490) * 10 ^ 70 +
        9818514196254695622459819542970446264317495851706802281029702863958508) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 141 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 21 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (328 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_328 :
    recurrence2Scalar2Exceptional.coeff 328 =
      (((81648056469271 * 10 ^ 70 +
        2595379780390210409529114398557938121512491021963114891932671003096864) * 10 ^ 70 +
        9484601689249367666421579267058260698066865715289351180839550586300213) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 142 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 20 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (329 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_329 :
    recurrence2Scalar2Exceptional.coeff 329 =
      -(((89262648552405 * 10 ^ 70 +
        2792004565259237661434272160643303397725626293875118579486401385834291) * 10 ^ 70 +
        3383575014208170786683047981071325447243434978629651720120689295704735) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 143 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 19 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (330 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_330 :
    recurrence2Scalar2Exceptional.coeff 330 =
      (((4639044415097 * 10 ^ 70 +
        9114074009289438795816452047849651944585668861513437640410751998861484) * 10 ^ 70 +
        2557039255745059819744471939410083969131012914294262513745636068671364) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 144 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 18 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (331 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_331 :
    recurrence2Scalar2Exceptional.coeff 331 =
      (((691922017134 * 10 ^ 70 +
        0560863286456180109081415362086316046011366050144294052414888323091487) * 10 ^ 70 +
        3301731473492119434199349174736270383882670860719929535756477339179990) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 145 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 17 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (332 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_332 :
    recurrence2Scalar2Exceptional.coeff 332 =
      -(((74241271280 * 10 ^ 70 +
        1078647055191145241486837881576374068306057062648685578263629138753403) * 10 ^ 70 +
        9696888586343843885035762381818987947530388635942916288263673382564981) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 146 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 16 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (333 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_333 :
    recurrence2Scalar2Exceptional.coeff 333 =
      -(((3595112029 * 10 ^ 70 +
        1555374239196846082016745797945157302760803683815682692849143144823649) * 10 ^ 70 +
        5915083025241793239575661141093882876411387993846649324447890494299481) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 147 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 15 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (334 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_334 :
    recurrence2Scalar2Exceptional.coeff 334 =
      (((679872738 * 10 ^ 70 +
        7754718101402708804413254067351169707314128279605688770038604004300607) * 10 ^ 70 +
        0745818085278001388655391407549302158060065280630455711748531027663626) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 148 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 14 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (335 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_335 :
    recurrence2Scalar2Exceptional.coeff 335 =
      (((16197704 * 10 ^ 70 +
        6768973851853435736393715300983848614802441708067725624447563730070321) * 10 ^ 70 +
        3950153860946403960214952123214000148090160558327161234325295142703823) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 149 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 13 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (336 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_336 :
    recurrence2Scalar2Exceptional.coeff 336 =
      -(((4572633 * 10 ^ 70 +
        7784254466913461102999366801942464567977141162664759924101983354974544) * 10 ^ 70 +
        5610822013086164307310551714031069704112627423408848384823202318509634) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 150 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 12 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (337 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_337 :
    recurrence2Scalar2Exceptional.coeff 337 =
      -(((112982 * 10 ^ 70 +
        8337057345435346358397858949235040041747700550028879317533529564063363) * 10 ^ 70 +
        5225460215372303330899400630447454262589255568627862584027447159816074) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 151 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 11 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (338 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_338 :
    recurrence2Scalar2Exceptional.coeff 338 =
      (((23185 * 10 ^ 70 +
        6735981271520416066333099065496666802054751968227178209889636585337185) * 10 ^ 70 +
        1675657012242528279952320903575146880331016033811911010590370794584640) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 152 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 10 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (339 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_339 :
    recurrence2Scalar2Exceptional.coeff 339 =
      (((1039 * 10 ^ 70 +
        9781891876917199543588072166625991872395517851848586788738788600457363) * 10 ^ 70 +
        4979117664704555420296546802829979440569581136161240416210261051084317) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 153 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 9 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (340 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_340 :
    recurrence2Scalar2Exceptional.coeff 340 =
      -(((69 * 10 ^ 70 +
        3717768677907796179106394124797276976959534640659469338356425284537691) * 10 ^ 70 +
        7021872789177325900142147925213087417632619477454598700810952796987930) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 154 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 8 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (341 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_341 :
    recurrence2Scalar2Exceptional.coeff 341 =
      -(((6 * 10 ^ 70 +
        6980414870611092264442604467484695653355088685936768213774715847923149) * 10 ^ 70 +
        5058408370098138833412759135554622071460741471808900142770055133676416) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 155 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 7 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (342 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_342 :
    recurrence2Scalar2Exceptional.coeff 342 =
      -((748679152607287457807778457278076588548978525043425402850874413050888 * 10 ^ 70 +
        6209712514867602247553706446209735687875875925975061109107361404701243) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 156 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 6 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (343 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_343 :
    recurrence2Scalar2Exceptional.coeff 343 =
      ((163623862041576463861203973984003809215600272248035244499787880393168 * 10 ^ 70 +
        1940875455571545615266833181670556662202124972668346917789218864680711) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 157 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 5 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (344 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_344 :
    recurrence2Scalar2Exceptional.coeff 344 =
      ((12387351213659236688827127381171112846799816621661115770639299111840 * 10 ^ 70 +
        5902240693279949211476556074035446755235851460301672558579320349859255) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 158 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 4 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (345 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_345 :
    recurrence2Scalar2Exceptional.coeff 345 =
      ((494548013231565395394107373421615793511138909707598009537089575921 * 10 ^ 70 +
        3034748068525241023522940557143326569051333117318741115595084901659581) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 159 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 3 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (346 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_346 :
    recurrence2Scalar2Exceptional.coeff 346 =
      ((13365873373330739878179506549138585973177428841577903932735929243 * 10 ^ 70 +
        2666511819353181512383642559429154305734432958482323157590951673630501) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 160 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 2 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (347 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_347 :
    recurrence2Scalar2Exceptional.coeff 347 =
      ((264160985651744138756551342727776215151358686633982823516423887 * 10 ^ 70 +
        5579500358120864219861411287218573380822193671604203952192937935085763) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 161 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 1 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (348 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_348 :
    recurrence2Scalar2Exceptional.coeff 348 =
      ((3948995606126024970098649907620749511263851955910272821226198 * 10 ^ 70 +
        9355177002011220713850889559874921706773609028049948168606566272191974) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 162 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (349 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_349 :
    recurrence2Scalar2Exceptional.coeff 349 =
      ((45339652873347273149867910428040122752534126599380971127560 * 10 ^ 70 +
        8653719969580976206665364906459004592575218925569135949224779488289980) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 163 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 31 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (350 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_350 :
    recurrence2Scalar2Exceptional.coeff 350 =
      ((401307901716500964548974295605753104973619798333321795107 * 10 ^ 70 +
        8242097586250307910562702375286408114539165670721226853587148958777407) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 164 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 30 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (351 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_351 :
    recurrence2Scalar2Exceptional.coeff 351 =
      ((2719335999002904031005162749530880496401404482726734535 * 10 ^ 70 +
        4993840098068632215930929389097336697496227500927478679652414130364459) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 165 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 29 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (352 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_352 :
    recurrence2Scalar2Exceptional.coeff 352 =
      ((13795034372967129382657265828146525930857481106554678 * 10 ^ 70 +
        5716063097865545784239903109754676841996864905055431331443050187237221) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 166 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 28 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (353 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_353 :
    recurrence2Scalar2Exceptional.coeff 353 =
      ((49553170761641731863484230696599034569939122930788 * 10 ^ 70 +
        7781818893157203091564039291023351765722657532902138818823503415218158) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 167 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 27 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (354 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_354 :
    recurrence2Scalar2Exceptional.coeff 354 =
      ((105955811055547107893414390342643991025155706551 * 10 ^ 70 +
        7244763397927060737108464853793426419393748196308448367556021958801914) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 168 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 26 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (355 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_355 :
    recurrence2Scalar2Exceptional.coeff 355 =
      ((7779002332430986798519543214975032154800212 * 10 ^ 70 +
        0847884125149123577925845305778401845553841375813171038872049539711815) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 169 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 25 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (356 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_356 :
    recurrence2Scalar2Exceptional.coeff 356 =
      -((808551181130801562239590434121771772549477 * 10 ^ 70 +
        5749003002019338954653013782067216339100296379665933870167525091491949) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 170 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 24 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (357 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_357 :
    recurrence2Scalar2Exceptional.coeff 357 =
      -((2754251321055780819019260661329039268617 * 10 ^ 70 +
        0210473544075210447684945372960852010129717301192866515659086881729078) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 171 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 23 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (358 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_358 :
    recurrence2Scalar2Exceptional.coeff 358 =
      -((3640057198288236179019275002568996126 * 10 ^ 70 +
        1196357439218105547322658464425099995672100146339681821695956651339275) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 172 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 22 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (359 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_359 :
    recurrence2Scalar2Exceptional.coeff 359 =
      ((2824238433225707664744922431106061 * 10 ^ 70 +
        5734950421248152638906169625188004212011211753931374525279979169487106) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 173 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 21 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (360 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_360 :
    recurrence2Scalar2Exceptional.coeff 360 =
      ((18994595696398195247723682660733 * 10 ^ 70 +
        0928873038737495368147183637558106952681297415601571134311113643941804) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 174 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 20 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (361 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_361 :
    recurrence2Scalar2Exceptional.coeff 361 =
      ((29144579970527653714923396134 * 10 ^ 70 +
        4130665300809468579287338449034406691646287766139051989645968266154668) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 175 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 19 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (362 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_362 :
    recurrence2Scalar2Exceptional.coeff 362 =
      ((9053918625925141626809973 * 10 ^ 70 +
        7135055268818391812362177671830363951676131520446059596989151666573241) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 176 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 18 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (363 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_363 :
    recurrence2Scalar2Exceptional.coeff 363 =
      -((35280548029742859454540 * 10 ^ 70 +
        6358957843728032318865852295968139734841458333820183245904106306173142) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 177 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 17 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (364 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_364 :
    recurrence2Scalar2Exceptional.coeff 364 =
      -((63156253612457086367 * 10 ^ 70 +
        8161120249499894513630170248451432351253829142799837560657556445338579) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 178 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 16 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (365 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_365 :
    recurrence2Scalar2Exceptional.coeff 365 =
      -((52829565754715974 * 10 ^ 70 +
        9019211172547558201740171096710915743539120006494875860121405615200455) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 179 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 15 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (366 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_366 :
    recurrence2Scalar2Exceptional.coeff 366 =
      -((25842362623700 * 10 ^ 70 +
        7036621456356761267183215270050486679792628521864636900469230871580923) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 180 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 14 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (367 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_367 :
    recurrence2Scalar2Exceptional.coeff 367 =
      -((7665325702 * 10 ^ 70 +
        1323102776661730666047519427909966123087642633989179362324275719891139) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 181 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 13 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (368 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_368 :
    recurrence2Scalar2Exceptional.coeff 368 =
      -((1361718 * 10 ^ 70 +
        2111718329293120772884893782566007878961251386021098287957266254066632) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 182 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 12 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (369 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_369 :
    recurrence2Scalar2Exceptional.coeff 369 =
      -((140 * 10 ^ 70 +
        7225299108895109598663058466640247395724471499732668118017745440542151) : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 183 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 11 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (370 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_370 :
    recurrence2Scalar2Exceptional.coeff 370 =
      (-81868686228454203299039834674591618851832451577061332668030070126200 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 184 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 10 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (371 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_371 :
    recurrence2Scalar2Exceptional.coeff 371 =
      (-2505467286567715828679445105200296487845655259314399725987942672 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 185 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 9 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (372 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_372 :
    recurrence2Scalar2Exceptional.coeff 372 =
      (-35272625218556995847679522300422653934473812817667793754774 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 186 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 8 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (373 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_373 :
    recurrence2Scalar2Exceptional.coeff 373 =
      (-210015516513919244718194431875260172136175321293110433 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 187 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 7 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (374 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_374 :
    recurrence2Scalar2Exceptional.coeff 374 =
      (-558380106899000772440910619237484769080014123044 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 188 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 6 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (375 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_375 :
    recurrence2Scalar2Exceptional.coeff 375 =
      (-589884556831854449741078234015576543128996 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 189 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 5 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (376 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_376 :
    recurrence2Scalar2Exceptional.coeff 376 =
      (-111005000805264452755470793520906832 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 190 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 4 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Exceptional_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient2.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C2_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Exceptional_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient2.coeff (377 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Exceptional_coeff_377 :
    recurrence2Scalar2Exceptional.coeff 377 =
      (-845310990356491934016919003 : ℚ) := by
  unfold recurrence2Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 191 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 3 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Exceptional_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Exceptional_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
