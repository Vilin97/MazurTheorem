/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Exceptional coefficient convolution

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
  recurrence2C1_coeff_0
  recurrence2C1_coeff_1
  recurrence2C1_coeff_2
  recurrence2C1_coeff_3
  recurrence2C1_coeff_4
  recurrence2C1_coeff_5
  recurrence2C1_coeff_6
  recurrence2C1_coeff_7
  recurrence2C1_coeff_8
  recurrence2C1_coeff_9
  recurrence2C1_coeff_10
  recurrence2C1_coeff_11
  recurrence2C1_coeff_12
  recurrence2C1_coeff_13
  recurrence2C1_coeff_14
  recurrence2C1_coeff_15
  recurrence2C1_coeff_16
  recurrence2C1_coeff_17
  recurrence2C1_coeff_18
  recurrence2C1_coeff_19
  recurrence2C1_coeff_20
  recurrence2C1_coeff_21
  recurrence2C1_coeff_22
  recurrence2C1_coeff_23
  recurrence2C1_coeff_24
  recurrence2C1_coeff_25
  recurrence2C1_coeff_26
  recurrence2C1_coeff_27
  recurrence2C1_coeff_28
  recurrence2C1_coeff_29
  recurrence2C1_coeff_30
  recurrence2C1_coeff_31
  recurrence2C1_coeff_32
  recurrence2C1_coeff_33
  recurrence2C1_coeff_34
  recurrence2C1_coeff_35
  recurrence2C1_coeff_36
  recurrence2C1_coeff_37
  recurrence2C1_coeff_38
  recurrence2C1_coeff_39
  recurrence2C1_coeff_40
  recurrence2C1_coeff_41
  recurrence2C1_coeff_42
  recurrence2C1_coeff_43
  recurrence2C1_coeff_44
  recurrence2C1_coeff_45
  recurrence2C1_coeff_46
  recurrence2C1_coeff_47
  recurrence2C1_coeff_48
  recurrence2C1_coeff_49
  recurrence2C1_coeff_50
  recurrence2C1_coeff_51
  recurrence2C1_coeff_52
  recurrence2C1_coeff_53
  recurrence2C1_coeff_54
  recurrence2C1_coeff_55
  recurrence2C1_coeff_56
  recurrence2C1_coeff_57
  recurrence2C1_coeff_58
  recurrence2C1_coeff_59
  recurrence2C1_coeff_60
  recurrence2C1_coeff_61
  recurrence2C1_coeff_62
  recurrence2C1_coeff_63
  recurrence2C1_coeff_64
  recurrence2C1_coeff_65
  recurrence2C1_coeff_66
  recurrence2C1_coeff_67
  recurrence2C1_coeff_68
  recurrence2C1_coeff_69
  recurrence2C1_coeff_70
  recurrence2C1_coeff_71
  recurrence2C1_coeff_72
  recurrence2C1_coeff_73
  recurrence2C1_coeff_74
  recurrence2C1_coeff_75
  recurrence2C1_coeff_76
  recurrence2C1_coeff_77
  recurrence2C1_coeff_78
  recurrence2C1_coeff_79
  recurrence2C1_coeff_80
  recurrence2C1_coeff_81
  recurrence2C1_coeff_82
  recurrence2C1_coeff_83
  recurrence2C1_coeff_84
  recurrence2C1_coeff_85
  recurrence2C1_coeff_86
  recurrence2C1_coeff_87
  recurrence2C1_coeff_88
  recurrence2C1_coeff_89
  recurrence2C1_coeff_90
  recurrence2C1_coeff_91
  recurrence2C1_coeff_92
  recurrence2C1_coeff_93
  recurrence2C1_coeff_94
  recurrence2C1_coeff_95
  recurrence2C1_coeff_96
  recurrence2C1_coeff_97
  recurrence2C1_coeff_98
  recurrence2C1_coeff_99
  recurrence2C1_coeff_100
  recurrence2C1_coeff_101
  recurrence2C1_coeff_102
  recurrence2C1_coeff_103
  recurrence2C1_coeff_104
  recurrence2C1_coeff_105
  recurrence2C1_coeff_106
  recurrence2C1_coeff_107
  recurrence2C1_coeff_108
  recurrence2C1_coeff_109
  recurrence2C1_coeff_110
  recurrence2C1_coeff_111
  recurrence2C1_coeff_112
  recurrence2C1_coeff_113
  recurrence2C1_coeff_114
  recurrence2C1_coeff_115
  recurrence2C1_coeff_116
  recurrence2C1_coeff_117
  recurrence2C1_coeff_118
  recurrence2C1_coeff_119
  recurrence2C1_coeff_120
  recurrence2C1_coeff_121
  recurrence2C1_coeff_122
  recurrence2C1_coeff_123
  recurrence2C1_coeff_124
  recurrence2C1_coeff_125
  recurrence2C1_coeff_126
  recurrence2C1_coeff_127
  recurrence2C1_coeff_128
  recurrence2C1_coeff_129
  recurrence2C1_coeff_130
  recurrence2C1_coeff_131
  recurrence2C1_coeff_132
  recurrence2C1_coeff_133
  recurrence2C1_coeff_134
  recurrence2C1_coeff_135
  recurrence2C1_coeff_136
  recurrence2C1_coeff_137
  recurrence2C1_coeff_138
  recurrence2C1_coeff_139
  recurrence2C1_coeff_140
  recurrence2C1_coeff_141
  recurrence2C1_coeff_142
  recurrence2C1_coeff_143
  recurrence2C1_coeff_144
  recurrence2C1_coeff_145
  recurrence2C1_coeff_146
  recurrence2C1_coeff_147
  recurrence2C1_coeff_148
  recurrence2C1_coeff_149
  recurrence2C1_coeff_150
  recurrence2C1_coeff_151
  recurrence2C1_coeff_152
  recurrence2C1_coeff_153
  recurrence2C1_coeff_154
  recurrence2C1_coeff_155
  recurrence2C1_coeff_156
  recurrence2C1_coeff_157
  recurrence2C1_coeff_158
  recurrence2C1_coeff_159
  recurrence2C1_coeff_160
  recurrence2C1_coeff_161
  recurrence2C1_coeff_162
  recurrence2C1_coeff_163
  recurrence2C1_coeff_164
  recurrence2C1_coeff_165
  recurrence2C1_coeff_166
  recurrence2C1_coeff_167
  recurrence2C1_coeff_168
  recurrence2C1_coeff_169
  recurrence2C1_coeff_170
  recurrence2C1_coeff_171
  recurrence2C1_coeff_172
  recurrence2C1_coeff_173
  recurrence2C1_coeff_174
  recurrence2C1_coeff_175
  recurrence2C1_coeff_176
  recurrence2C1_coeff_177
  recurrence2C1_coeff_178
  recurrence2C1_coeff_179
  recurrence2C1_coeff_180
  recurrence2C1_coeff_181
  recurrence2C1_coeff_182
  recurrence2C1_coeff_183
  recurrence2C1_coeff_184
  recurrence2C1_coeff_185
  recurrence2C1_coeff_186
  recurrence2C1_coeff_187
  recurrence2C1_coeff_188
  recurrence2C1_coeff_189
  recurrence2C1_coeff_190

private theorem recurrence2Scalar1Exceptional_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (285 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_285 :
    recurrence2Scalar1Exceptional.coeff 285 =
      (((264381696217789808725462257865561024161718771 * 10 ^ 70 +
        6990558774924532232046420345344100648961610766519524681683937179378210) * 10 ^ 70 +
        7627963298958559808149563674984451640812900304511528882080527008987124) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 95 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 3 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (286 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_286 :
    recurrence2Scalar1Exceptional.coeff 286 =
      -(((68891738754539153175440797933048759593985667 * 10 ^ 70 +
        7942424326188458868569911528376969141695737805485320022548747031693192) * 10 ^ 70 +
        2011624054184195250738502835289065577626451792429109787806205154005169) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 96 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 2 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (287 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_287 :
    recurrence2Scalar1Exceptional.coeff 287 =
      (((3994606795530035877976419491298121002467647 * 10 ^ 70 +
        0180387094519094072760341941642081278493362037338413447653653722552478) * 10 ^ 70 +
        3563365169072904353729024295019505052052370558348200288664274911066654) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 97 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 1 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (288 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_288 :
    recurrence2Scalar1Exceptional.coeff 288 =
      (((8366370115124385521414567530414624374794334 * 10 ^ 70 +
        0164483034275546004645482126920573625196278103153541016199206339783790) * 10 ^ 70 +
        5183220299150361281257285220515150334366459371317483672117193390315498) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 98 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (289 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_289 :
    recurrence2Scalar1Exceptional.coeff 289 =
      -(((6174842452186898289576171005465350334138352 * 10 ^ 70 +
        8553026604692359164556564441298856334070610207996520908644707929546329) * 10 ^ 70 +
        6295572592859576648884655564696372427243186223005549798529727998058171) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 99 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 31 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (290 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_290 :
    recurrence2Scalar1Exceptional.coeff 290 =
      (((2754504325976807125597760010495151671547722 * 10 ^ 70 +
        1938208191090459997166670267568289763729407588431206577282540517498224) * 10 ^ 70 +
        4556808732765363664976675104288347712618482366532114967982043109210777) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 100 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 30 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (291 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_291 :
    recurrence2Scalar1Exceptional.coeff 291 =
      -(((859541206400782755832743699998611377563490 * 10 ^ 70 +
        3886016859893953968273448580493631512267121529604112308254599278974558) * 10 ^ 70 +
        4355668073382284063894758916292149993750356451378514448002615702180258) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 101 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 29 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (292 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_292 :
    recurrence2Scalar1Exceptional.coeff 292 =
      (((154466756816596563819233395879523487529675 * 10 ^ 70 +
        1158879580923077197585929355740331207807899483245642323851124675519342) * 10 ^ 70 +
        6887875092695467137914654967394336046740787849734839552083904926654024) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 102 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 28 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (293 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_293 :
    recurrence2Scalar1Exceptional.coeff 293 =
      (((18161391615661832015249023781292103350869 * 10 ^ 70 +
        2085163857461930101434736392568715175125991377496310591448766471279576) * 10 ^ 70 +
        0745404934841110412197469382868991529066558350355174919621994108767465) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 103 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 27 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (294 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_294 :
    recurrence2Scalar1Exceptional.coeff 294 =
      -(((28959878502880858292874247816359799531683 * 10 ^ 70 +
        8609601331699810975026519046968663473328806568016580587793957909341252) * 10 ^ 70 +
        1091382912339805883484075780301095928445189810181058131744144125079112) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 104 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 26 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (295 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_295 :
    recurrence2Scalar1Exceptional.coeff 295 =
      (((13871601630974152103489570788171439652145 * 10 ^ 70 +
        1037266334681077277402943021350362346196281466529687556396716776693177) * 10 ^ 70 +
        0478108382003141128072534580139324064388771824911030875279714190070756) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 105 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 25 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (296 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_296 :
    recurrence2Scalar1Exceptional.coeff 296 =
      -(((4234880325668558390033248014144605559491 * 10 ^ 70 +
        2224941587717922109938839297747442796563094851543039436617197044999597) * 10 ^ 70 +
        5300917777170299059241003061563696751825671127184119064627115448089315) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 106 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 24 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (297 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_297 :
    recurrence2Scalar1Exceptional.coeff 297 =
      (((743352595236625407263001437640267113663 * 10 ^ 70 +
        3388416637614922975550197980927249887630541070114172641642493667662697) * 10 ^ 70 +
        9483780018911810237924101364303519058769796408990229439845614757583091) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 107 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 23 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (298 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_298 :
    recurrence2Scalar1Exceptional.coeff 298 =
      (((48051460689405947099412894577533237509 * 10 ^ 70 +
        8205796122424546909252974610382740165019023721656816956419863037332737) * 10 ^ 70 +
        8797206449753812932337330648442258434095450549985499828366440708639497) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 108 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 22 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (299 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_299 :
    recurrence2Scalar1Exceptional.coeff 299 =
      -(((93278510016636752061220170822643211732 * 10 ^ 70 +
        6311251110036688585343856827687439911819030905909380642045557897659354) * 10 ^ 70 +
        8164061270107603076835653240418028926162584473964641424575969778581080) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 109 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 21 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (300 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_300 :
    recurrence2Scalar1Exceptional.coeff 300 =
      (((39253161189637614086217806276988123266 * 10 ^ 70 +
        0408270699502067987729963203792851667983918249449073908030182827169138) * 10 ^ 70 +
        6475227315898479205668382728842898465124665011913303806150442696506090) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 110 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 20 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (301 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_301 :
    recurrence2Scalar1Exceptional.coeff 301 =
      -(((9753005405841125352304567359634688319 * 10 ^ 70 +
        1647867036681559659506509496568216556485402914607545966207790974358910) * 10 ^ 70 +
        3213069352378136657569625911270120321249106757494072670610605094281147) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 111 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 19 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (302 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_302 :
    recurrence2Scalar1Exceptional.coeff 302 =
      (((1064288595106627699166068375022215358 * 10 ^ 70 +
        6292272129373870465404162960458370456097380350814763866125977071557441) * 10 ^ 70 +
        5237004787444526087233990391223794994888906298680916383288355372202020) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 112 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 18 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (303 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_303 :
    recurrence2Scalar1Exceptional.coeff 303 =
      (((304792375595836714136147445143908030 * 10 ^ 70 +
        7140308040245043818221786044951556285104639662255512439557973654618440) * 10 ^ 70 +
        2347321040876942675307010405402629352858152954111753758121783942119916) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 113 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 17 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (304 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_304 :
    recurrence2Scalar1Exceptional.coeff 304 =
      -(((201501287588238129681052254173567365 * 10 ^ 70 +
        4110962006257435872661740761991486186165956114359740131703918974590354) * 10 ^ 70 +
        6925186147708071711628388407209538245265271867250429432401808414319789) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 114 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 16 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (305 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_305 :
    recurrence2Scalar1Exceptional.coeff 305 =
      (((57434839704781723234920165317805279 * 10 ^ 70 +
        1293194246502091230133552013422970197105859917234256522435578836444592) * 10 ^ 70 +
        7378186341397400389171480473319263491925834075472592441861296144098637) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 115 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 15 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (306 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_306 :
    recurrence2Scalar1Exceptional.coeff 306 =
      -(((8250946857127590080018261229264595 * 10 ^ 70 +
        1831673862454414770958450289497648040447478180141457976159714139930311) * 10 ^ 70 +
        0132633663371721540865316275492020946554773912791214159442363362650079) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 116 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 14 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (307 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_307 :
    recurrence2Scalar1Exceptional.coeff 307 =
      -(((629142439359668862723439553544759 * 10 ^ 70 +
        8988343593011121275087357445974586468925125698473646923073816516278911) * 10 ^ 70 +
        8696843841354671447427757913285668203406073835106259744137986326599808) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 117 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 13 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (308 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_308 :
    recurrence2Scalar1Exceptional.coeff 308 =
      (((712564262206706573897266075607150 * 10 ^ 70 +
        8120944177274601909030877178601022799677861667916585143555992205068420) * 10 ^ 70 +
        3400840350992598983823643991829758774005841413915360796908406959078810) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 118 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 12 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (309 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_309 :
    recurrence2Scalar1Exceptional.coeff 309 =
      -(((202722884530526532366382129678198 * 10 ^ 70 +
        0277545034132458955026700402407405690866733755594353313384870143623874) * 10 ^ 70 +
        0237229387139698829064796000088137709574040313509979494472828506813314) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 119 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 11 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (310 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_310 :
    recurrence2Scalar1Exceptional.coeff 310 =
      (((26725448256019702070527679504444 * 10 ^ 70 +
        7389604617183682767869869713078871670564177938355695149067639850484506) * 10 ^ 70 +
        5698965260492380364317577850590948221082759913179848311048044351587650) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 120 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 10 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (311 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_311 :
    recurrence2Scalar1Exceptional.coeff 311 =
      (((2131547907481481704761403154427 * 10 ^ 70 +
        2701861064046013521667012069895944721199799017187566763641160169743352) * 10 ^ 70 +
        9537871875642346318280091725243825070804638934609584486956286047516472) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 121 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 9 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (312 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_312 :
    recurrence2Scalar1Exceptional.coeff 312 =
      -(((1926457916866307726732692172339 * 10 ^ 70 +
        2288736884838084419559336710990591523441056730761361019832911199463607) * 10 ^ 70 +
        8156322122109581297247354269209323937116021512824223605954413600911525) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 122 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 8 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient1.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C1_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient1.coeff (313 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Exceptional_coeff_313 :
    recurrence2Scalar1Exceptional.coeff 313 =
      (((446989394028780227505629565380 * 10 ^ 70 +
        8705558357201707348175460655551534295977494164809442157675237026282722) * 10 ^ 70 +
        3075896781313641679314126077871898630822400573102489767626258783928840) : ℚ) := by
  unfold recurrence2Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 123 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 7 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Exceptional_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
