/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2ExceptionalPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C2_coeff_0
  recurrence4C2_coeff_1
  recurrence4C2_coeff_10
  recurrence4C2_coeff_100
  recurrence4C2_coeff_101
  recurrence4C2_coeff_102
  recurrence4C2_coeff_103
  recurrence4C2_coeff_104
  recurrence4C2_coeff_105
  recurrence4C2_coeff_106
  recurrence4C2_coeff_107
  recurrence4C2_coeff_108
  recurrence4C2_coeff_109
  recurrence4C2_coeff_11
  recurrence4C2_coeff_110
  recurrence4C2_coeff_111
  recurrence4C2_coeff_112
  recurrence4C2_coeff_113
  recurrence4C2_coeff_114
  recurrence4C2_coeff_115
  recurrence4C2_coeff_116
  recurrence4C2_coeff_117
  recurrence4C2_coeff_118
  recurrence4C2_coeff_119
  recurrence4C2_coeff_12
  recurrence4C2_coeff_120
  recurrence4C2_coeff_121
  recurrence4C2_coeff_122
  recurrence4C2_coeff_123
  recurrence4C2_coeff_124
  recurrence4C2_coeff_125
  recurrence4C2_coeff_126
  recurrence4C2_coeff_127
  recurrence4C2_coeff_128
  recurrence4C2_coeff_129
  recurrence4C2_coeff_13
  recurrence4C2_coeff_130
  recurrence4C2_coeff_131
  recurrence4C2_coeff_132
  recurrence4C2_coeff_133
  recurrence4C2_coeff_134
  recurrence4C2_coeff_135
  recurrence4C2_coeff_136
  recurrence4C2_coeff_137
  recurrence4C2_coeff_138
  recurrence4C2_coeff_139
  recurrence4C2_coeff_14
  recurrence4C2_coeff_140
  recurrence4C2_coeff_141
  recurrence4C2_coeff_142
  recurrence4C2_coeff_143
  recurrence4C2_coeff_144
  recurrence4C2_coeff_145
  recurrence4C2_coeff_15
  recurrence4C2_coeff_16
  recurrence4C2_coeff_17
  recurrence4C2_coeff_18
  recurrence4C2_coeff_19
  recurrence4C2_coeff_2
  recurrence4C2_coeff_20
  recurrence4C2_coeff_21
  recurrence4C2_coeff_22
  recurrence4C2_coeff_23
  recurrence4C2_coeff_24

attribute [local simp]
  recurrence4C2_coeff_25
  recurrence4C2_coeff_26
  recurrence4C2_coeff_27
  recurrence4C2_coeff_28
  recurrence4C2_coeff_29
  recurrence4C2_coeff_3
  recurrence4C2_coeff_30
  recurrence4C2_coeff_31
  recurrence4C2_coeff_32
  recurrence4C2_coeff_33
  recurrence4C2_coeff_34
  recurrence4C2_coeff_35
  recurrence4C2_coeff_36
  recurrence4C2_coeff_37
  recurrence4C2_coeff_38
  recurrence4C2_coeff_39
  recurrence4C2_coeff_4
  recurrence4C2_coeff_40
  recurrence4C2_coeff_41
  recurrence4C2_coeff_42
  recurrence4C2_coeff_43
  recurrence4C2_coeff_44
  recurrence4C2_coeff_45
  recurrence4C2_coeff_46
  recurrence4C2_coeff_47
  recurrence4C2_coeff_48
  recurrence4C2_coeff_49
  recurrence4C2_coeff_5
  recurrence4C2_coeff_50
  recurrence4C2_coeff_51
  recurrence4C2_coeff_52
  recurrence4C2_coeff_53
  recurrence4C2_coeff_54
  recurrence4C2_coeff_55
  recurrence4C2_coeff_56
  recurrence4C2_coeff_57
  recurrence4C2_coeff_58
  recurrence4C2_coeff_59
  recurrence4C2_coeff_6
  recurrence4C2_coeff_60
  recurrence4C2_coeff_61
  recurrence4C2_coeff_62
  recurrence4C2_coeff_63
  recurrence4C2_coeff_64
  recurrence4C2_coeff_65
  recurrence4C2_coeff_66
  recurrence4C2_coeff_67
  recurrence4C2_coeff_68
  recurrence4C2_coeff_69
  recurrence4C2_coeff_7
  recurrence4C2_coeff_70
  recurrence4C2_coeff_71
  recurrence4C2_coeff_72
  recurrence4C2_coeff_73
  recurrence4C2_coeff_74
  recurrence4C2_coeff_75
  recurrence4C2_coeff_76
  recurrence4C2_coeff_77
  recurrence4C2_coeff_78
  recurrence4C2_coeff_79
  recurrence4C2_coeff_8
  recurrence4C2_coeff_80
  recurrence4C2_coeff_81
  recurrence4C2_coeff_82

attribute [local simp]
  recurrence4C2_coeff_83
  recurrence4C2_coeff_84
  recurrence4C2_coeff_85
  recurrence4C2_coeff_86
  recurrence4C2_coeff_87
  recurrence4C2_coeff_88
  recurrence4C2_coeff_89
  recurrence4C2_coeff_9
  recurrence4C2_coeff_90
  recurrence4C2_coeff_91
  recurrence4C2_coeff_92
  recurrence4C2_coeff_93
  recurrence4C2_coeff_94
  recurrence4C2_coeff_95
  recurrence4C2_coeff_96
  recurrence4C2_coeff_97
  recurrence4C2_coeff_98
  recurrence4C2_coeff_99
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
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139

attribute [local simp]
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
  recurrence4ExceptionalProduct_coeff_160
  recurrence4ExceptionalProduct_coeff_161
  recurrence4ExceptionalProduct_coeff_162
  recurrence4ExceptionalProduct_coeff_163
  recurrence4ExceptionalProduct_coeff_164
  recurrence4ExceptionalProduct_coeff_165
  recurrence4ExceptionalProduct_coeff_166
  recurrence4ExceptionalProduct_coeff_167
  recurrence4ExceptionalProduct_coeff_168
  recurrence4ExceptionalProduct_coeff_169
  recurrence4ExceptionalProduct_coeff_17
  recurrence4ExceptionalProduct_coeff_170
  recurrence4ExceptionalProduct_coeff_171
  recurrence4ExceptionalProduct_coeff_172
  recurrence4ExceptionalProduct_coeff_173
  recurrence4ExceptionalProduct_coeff_174
  recurrence4ExceptionalProduct_coeff_175
  recurrence4ExceptionalProduct_coeff_176
  recurrence4ExceptionalProduct_coeff_177
  recurrence4ExceptionalProduct_coeff_178
  recurrence4ExceptionalProduct_coeff_179
  recurrence4ExceptionalProduct_coeff_18
  recurrence4ExceptionalProduct_coeff_180
  recurrence4ExceptionalProduct_coeff_181
  recurrence4ExceptionalProduct_coeff_182
  recurrence4ExceptionalProduct_coeff_183
  recurrence4ExceptionalProduct_coeff_184
  recurrence4ExceptionalProduct_coeff_185
  recurrence4ExceptionalProduct_coeff_186
  recurrence4ExceptionalProduct_coeff_187
  recurrence4ExceptionalProduct_coeff_188
  recurrence4ExceptionalProduct_coeff_189
  recurrence4ExceptionalProduct_coeff_19
  recurrence4ExceptionalProduct_coeff_190
  recurrence4ExceptionalProduct_coeff_191
  recurrence4ExceptionalProduct_coeff_192
  recurrence4ExceptionalProduct_coeff_193
  recurrence4ExceptionalProduct_coeff_194
  recurrence4ExceptionalProduct_coeff_195
  recurrence4ExceptionalProduct_coeff_196
  recurrence4ExceptionalProduct_coeff_197

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_198
  recurrence4ExceptionalProduct_coeff_199
  recurrence4ExceptionalProduct_coeff_2
  recurrence4ExceptionalProduct_coeff_20
  recurrence4ExceptionalProduct_coeff_200
  recurrence4ExceptionalProduct_coeff_201
  recurrence4ExceptionalProduct_coeff_202
  recurrence4ExceptionalProduct_coeff_203
  recurrence4ExceptionalProduct_coeff_204
  recurrence4ExceptionalProduct_coeff_205
  recurrence4ExceptionalProduct_coeff_206
  recurrence4ExceptionalProduct_coeff_207
  recurrence4ExceptionalProduct_coeff_208
  recurrence4ExceptionalProduct_coeff_209
  recurrence4ExceptionalProduct_coeff_21
  recurrence4ExceptionalProduct_coeff_210
  recurrence4ExceptionalProduct_coeff_211
  recurrence4ExceptionalProduct_coeff_212
  recurrence4ExceptionalProduct_coeff_213
  recurrence4ExceptionalProduct_coeff_214
  recurrence4ExceptionalProduct_coeff_215
  recurrence4ExceptionalProduct_coeff_216
  recurrence4ExceptionalProduct_coeff_217
  recurrence4ExceptionalProduct_coeff_218
  recurrence4ExceptionalProduct_coeff_219
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
  recurrence4ExceptionalProduct_coeff_51
  recurrence4ExceptionalProduct_coeff_52
  recurrence4ExceptionalProduct_coeff_53
  recurrence4ExceptionalProduct_coeff_54
  recurrence4ExceptionalProduct_coeff_55
  recurrence4ExceptionalProduct_coeff_56
  recurrence4ExceptionalProduct_coeff_57

attribute [local simp]
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

private theorem recurrence4Scalar2Exceptional_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (156 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_156 :
    recurrence4Scalar2Exceptional.coeff 156 =
      ((((1722259135545036965485700821697737843982490184934162581007940074447 * 10 ^ 70 +
        6811056538803431677431797528520122182743981085784532096243686402452094) * 10 ^ 70 +
        2668500848265753204204003447219923111333294302033643962990112738422919) * 10 ^ 70 +
        8631385474181592202173712311236115990661462978345812975741522586359462) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (156 - x)) = _
  rw [show 157 = 11 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_156_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (157 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_157 :
    recurrence4Scalar2Exceptional.coeff 157 =
      -((((8055461561816930350060230587872914250993279417105110613501924514269 * 10 ^ 70 +
        3073297390800499263213544292574947330063580556299971065459420836268476) * 10 ^ 70 +
        9955559479253172002778646483485848377534545025996125929074444992243853) * 10 ^ 70 +
        6138818425309348462735893416228424543725933727594806687303324968347757) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (157 - x)) = _
  rw [show 158 = 12 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_157_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (158 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_158 :
    recurrence4Scalar2Exceptional.coeff 158 =
      ((((36627931567446415925870379175426356347695921972229957038783427791321 * 10 ^ 70 +
        1898775168870756515523575930446160305700602681981982010118823711409842) * 10 ^ 70 +
        7045558622201339584077457089787017126463503929545770575674703489402252) * 10 ^ 70 +
        6760298751173509657061469528741749732734958106607110001257733177963418) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (158 - x)) = _
  rw [show 159 = 13 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_158_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (159 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_159 :
    recurrence4Scalar2Exceptional.coeff 159 =
      -((((162188294292405448151619045943957618250051850147926261986054451502848 * 10 ^ 70 +
        1534456939562918056087946659792306774766366924169072012456285884057656) * 10 ^ 70 +
        2869954739844330160867042425559629213419271003734436282659869580804191) * 10 ^ 70 +
        4674414553707042654106624089364379927884863742284796070171192454181862) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (159 - x)) = _
  rw [show 160 = 14 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_159_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (160 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_160 :
    recurrence4Scalar2Exceptional.coeff 160 =
      ((((700350963692292927235116953119812969796164495223207637521014422959219 * 10 ^ 70 +
        0272493403961464829392064644052579945178834176396494807455160029299181) * 10 ^ 70 +
        4016538931501973024857940179283319131294925498287142093719164959115470) * 10 ^ 70 +
        1269405878420326488253527766461772748353930619122122303042531757763654) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (160 - x)) = _
  rw [show 161 = 15 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_160_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (161 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_161 :
    recurrence4Scalar2Exceptional.coeff 161 =
      -((((2952532251417406813919199672273361711740457272815812808169844741859256 * 10 ^ 70 +
        0637997563060357737321714483104106032170593085485080811568792052971119) * 10 ^ 70 +
        9504635598263614385318083236221277259587874592879705257151089194465792) * 10 ^ 70 +
        3455447938307155120138709364823502841760648136965689465686861878206232) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (161 - x)) = _
  rw [show 162 = 16 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_161_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (162 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_162 :
    recurrence4Scalar2Exceptional.coeff 162 =
      (((((1 * 10 ^ 70 +
        2163739060476377649190827049754798401534957609548664388042989593974849) * 10 ^ 70 +
        8399344061660895978758876635352406009005711823021385315184395360712861) * 10 ^ 70 +
        4634402508760249658199238239103406226016865601961932360970125906341841) * 10 ^ 70 +
        8173502665298202669607193613266630828922929827067621671741177499263581) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (162 - x)) = _
  rw [show 163 = 17 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_162_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (163 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_163 :
    recurrence4Scalar2Exceptional.coeff 163 =
      -(((((4 * 10 ^ 70 +
        9009518814919973647702218408697136128254768462386784387519121600839608) * 10 ^ 70 +
        7657510209451392159980526243946388487219281735630381594968505469597141) * 10 ^ 70 +
        3704160711014890144895610391881957577952628233575420611484086836181978) * 10 ^ 70 +
        2418360111317584460148191615915995550016148895759513599535136356685946) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (163 - x)) = _
  rw [show 164 = 18 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_163_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (164 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_164 :
    recurrence4Scalar2Exceptional.coeff 164 =
      (((((19 * 10 ^ 70 +
        3255755805755568321964619687689993685080702664832526841546579735699993) * 10 ^ 70 +
        5909392365587311279763803050927471465853702610358925761155452622123193) * 10 ^ 70 +
        7787746812923047669933654786310944773512172035613368219396061938208404) * 10 ^ 70 +
        6034852014569982126100459083469401485362729695428687607886141210252030) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (164 - x)) = _
  rw [show 165 = 19 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_164_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (165 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_165 :
    recurrence4Scalar2Exceptional.coeff 165 =
      -(((((74 * 10 ^ 70 +
        6244912814153207939166767276649666369462014288396761090131825656314390) * 10 ^ 70 +
        0484328633290945420809144089938097833753532861829383262298387909637546) * 10 ^ 70 +
        7480206837548950212938853884521903391702991244389887183036853926003808) * 10 ^ 70 +
        8995043428369492258039253871207128102072309572815158307083472247213423) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (165 - x)) = _
  rw [show 166 = 20 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_165_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (166 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_166 :
    recurrence4Scalar2Exceptional.coeff 166 =
      (((((282 * 10 ^ 70 +
        3278371783672948558440410806241948679515803594928100197463513877244875) * 10 ^ 70 +
        9508025098745724312445380816859995746611754666826419643408633302435049) * 10 ^ 70 +
        1166614821521169848298820728731758681302425464235276499254603803021651) * 10 ^ 70 +
        5896547139538353751916537970453167239588081766900969789917996587731543) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (166 - x)) = _
  rw [show 167 = 21 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_166_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (167 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_167 :
    recurrence4Scalar2Exceptional.coeff 167 =
      -(((((1047 * 10 ^ 70 +
        0073625659785096636694516858936430928563169810965533606217585898574106) * 10 ^ 70 +
        4767338013895144320148357122588553676483191267717743103306168248856819) * 10 ^ 70 +
        0594183905912587543816820865824147125755969911947853496301680668813232) * 10 ^ 70 +
        7747433094364067302439963824008936455206077744725664642339245624366635) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (167 - x)) = _
  rw [show 168 = 22 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_167_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (168 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_168 :
    recurrence4Scalar2Exceptional.coeff 168 =
      (((((3807 * 10 ^ 70 +
        5729388105632386429635630372500517596761234887584439237081148353254255) * 10 ^ 70 +
        0696800221374688617803351714274265791517661417566170729601993100338513) * 10 ^ 70 +
        0412433223907696388114512298524358901521465938549865651288620691179286) * 10 ^ 70 +
        8615886495320057233370954176215983181190696407532184500471541112637380) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (168 - x)) = _
  rw [show 169 = 23 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_168_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (169 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_169 :
    recurrence4Scalar2Exceptional.coeff 169 =
      -(((((13583 * 10 ^ 70 +
        4424579556015367743350623456487396137357980925630456254950693281823533) * 10 ^ 70 +
        2316835539905878783424153063409543322286197697241746531391926086975646) * 10 ^ 70 +
        1400103747962177572347713426488900241975310340680018806058079948846280) * 10 ^ 70 +
        3982036360470028784336275927100101584356162936682574217789245448589007) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (169 - x)) = _
  rw [show 170 = 24 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_169_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (170 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_170 :
    recurrence4Scalar2Exceptional.coeff 170 =
      (((((47553 * 10 ^ 70 +
        2220994723261192011692887853339704573680505875829218050542356277562913) * 10 ^ 70 +
        9218512678045580667247258863456900415163810287798390041073642605387529) * 10 ^ 70 +
        8741538943289003306708330920975340098897385576261250249369840255378242) * 10 ^ 70 +
        3965949166934063983357155836326589778684802775582200577507239009376763) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (170 - x)) = _
  rw [show 171 = 25 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_170_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (171 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_171 :
    recurrence4Scalar2Exceptional.coeff 171 =
      -(((((163414 * 10 ^ 70 +
        6004053180166700852612354139335643410055316199703796973310610974031049) * 10 ^ 70 +
        9879895821765674746153260658143836705620596759672654740049882158317405) * 10 ^ 70 +
        0573240814162563755516716703156378230621442605706193247027349709385313) * 10 ^ 70 +
        9608354891012069593990838037795763218925065067322036468380624001842070) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (171 - x)) = _
  rw [show 172 = 26 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_171_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (172 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_172 :
    recurrence4Scalar2Exceptional.coeff 172 =
      (((((551396 * 10 ^ 70 +
        0703895529524587799773634977507865573411059695803474757728793339129217) * 10 ^ 70 +
        7685198737419972888176657669745866774700288952652130971335698673586794) * 10 ^ 70 +
        7119555004691952230287920251258105611687103064816435950491288930544139) * 10 ^ 70 +
        0825908523667952532951917355783753103705099914663548037386443981698531) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (172 - x)) = _
  rw [show 173 = 27 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_172_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (173 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_173 :
    recurrence4Scalar2Exceptional.coeff 173 =
      -(((((1827299 * 10 ^ 70 +
        5734634264984774300750296381285628831639769087230226114024718496199261) * 10 ^ 70 +
        9260756396416742038321997943867006540811771302335829427311275426440190) * 10 ^ 70 +
        6726267797386846821782920458974282903156508461473241315360262524082711) * 10 ^ 70 +
        0281450409469535502840286801337317142598927695359895636278175388988459) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (173 - x)) = _
  rw [show 174 = 28 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_173_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (174 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_174 :
    recurrence4Scalar2Exceptional.coeff 174 =
      (((((5948836 * 10 ^ 70 +
        0575136993967327713928513665666437166535284530424358195512018010901178) * 10 ^ 70 +
        9927122372702913091408098291218235838289481083657165044539607604754579) * 10 ^ 70 +
        6304218670289311021783125313467302726414936875698395661343979775615378) * 10 ^ 70 +
        0451494513671293198798531305744287243627868721296422314029813433056568) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (174 - x)) = _
  rw [show 175 = 29 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_174_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (175 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_175 :
    recurrence4Scalar2Exceptional.coeff 175 =
      -(((((19029432 * 10 ^ 70 +
        7057053502472431358669866419124279125143535448803784323117137103218008) * 10 ^ 70 +
        7506510315719996097340358577134331390309710837036529279832712725515953) * 10 ^ 70 +
        3435362414895130125650788450487552021309048215786472894503114186262357) * 10 ^ 70 +
        8024551461840622121177031574613569781590893831648726277757243733435304) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (175 - x)) = _
  rw [show 176 = 30 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_175_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (176 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_176 :
    recurrence4Scalar2Exceptional.coeff 176 =
      (((((59824643 * 10 ^ 70 +
        9014127613439362602996511784313605796887616695828797061625774295779911) * 10 ^ 70 +
        6000739631479282634429144980920580396407101145399635140756818890830411) * 10 ^ 70 +
        7385267157814157175786512958574064423018811076789043072160840819918571) * 10 ^ 70 +
        2947987048509576346604698056786523124410427429061009417220675213956146) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (176 - x)) = _
  rw [show 177 = 31 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_176_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (177 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_177 :
    recurrence4Scalar2Exceptional.coeff 177 =
      -(((((184874851 * 10 ^ 70 +
        1397560954452565045602231282545624862743884740453793652108854910671543) * 10 ^ 70 +
        1611462456822520716822006854717282488795303037204820519998573041396229) * 10 ^ 70 +
        7527160284864705631309169510941810621991223159521811466295435654253945) * 10 ^ 70 +
        6786961978350647113539403952496816537543835792433845588209707898473808) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (177 - x)) = _
  rw [show 178 = 32 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_177_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (178 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_178 :
    recurrence4Scalar2Exceptional.coeff 178 =
      (((((561690082 * 10 ^ 70 +
        5753439799514767594413001478968882328187400407965206943143454406038529) * 10 ^ 70 +
        6736640503751373799891069034898284849582682639141583752417981347333672) * 10 ^ 70 +
        9136146927863241164601761823738346272451902040123184702299139564982730) * 10 ^ 70 +
        1447721322995461645203162231630115821687245564175385389877382233863470) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (178 - x)) = _
  rw [show 179 = 33 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_178_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (179 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_179 :
    recurrence4Scalar2Exceptional.coeff 179 =
      -(((((1678069550 * 10 ^ 70 +
        1217977835117642974628362923987882545013015830005741356716812415201180) * 10 ^ 70 +
        0712462090676044977764278702919023055575660876962835209525579555606312) * 10 ^ 70 +
        6003668606347342359621607168723799963762061255824941594785456883962942) * 10 ^ 70 +
        5887126239437383897080727599700613677251020537195706790314303884684254) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (179 - x)) = _
  rw [show 180 = 34 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_179_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (180 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_180 :
    recurrence4Scalar2Exceptional.coeff 180 =
      (((((4930446955 * 10 ^ 70 +
        7528034215561882967993344203594773107281223610822219048955825084843457) * 10 ^ 70 +
        3689307978798681775554397091078186244159779037862920475518375926095811) * 10 ^ 70 +
        4886262717855415582592439009027085522310691327346041593052347982688091) * 10 ^ 70 +
        3658301984094967170235891136904759425906809495503331250445069155793661) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (180 - x)) = _
  rw [show 181 = 35 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_180_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (181 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_181 :
    recurrence4Scalar2Exceptional.coeff 181 =
      -(((((14249209752 * 10 ^ 70 +
        3373362824966456488137290064891093891402138692311654979631656372976129) * 10 ^ 70 +
        9681131063173580988134432866708437633824993441836782800015701991990585) * 10 ^ 70 +
        9064088691187621494072108452997542210563991420209998011881234442360103) * 10 ^ 70 +
        4264608765953278712942073357541043346678034556362053316336300777887404) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (181 - x)) = _
  rw [show 182 = 36 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_181_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (182 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_182 :
    recurrence4Scalar2Exceptional.coeff 182 =
      (((((40512119359 * 10 ^ 70 +
        8033352495717418610497701271167621601464892946295378027860022910472446) * 10 ^ 70 +
        2981173889023139472011302850658098685410572990986438442191460143204851) * 10 ^ 70 +
        1844163128098220592384199411768614297858537146103788884315837786452958) * 10 ^ 70 +
        4153514613450980197251558529969683740048645556478239778105530714777363) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (182 - x)) = _
  rw [show 183 = 37 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_182_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (183 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_183 :
    recurrence4Scalar2Exceptional.coeff 183 =
      -(((((113325385970 * 10 ^ 70 +
        4191160573050371853531942877904284529173668586978628626064313452852899) * 10 ^ 70 +
        8109579192769651805398769334175260127052172601797556055153727037993666) * 10 ^ 70 +
        6608155089120149256036263975150700923257162529273106463902272338235396) * 10 ^ 70 +
        1647384871867467286794497050338295530675110185849668802639008333053225) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (183 - x)) = _
  rw [show 184 = 38 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_183_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (184 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_184 :
    recurrence4Scalar2Exceptional.coeff 184 =
      (((((311941361350 * 10 ^ 70 +
        9665044890489994019514032533671295078128431632100543998400522241899116) * 10 ^ 70 +
        4778541271433006276861306512813691495456851122250256518332292482766762) * 10 ^ 70 +
        0691845405158271011659100704766251558131548873952679321153853031802780) * 10 ^ 70 +
        9449712666874256364508388099714040104071226451204711763818795472698311) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (184 - x)) = _
  rw [show 185 = 39 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_184_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (185 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_185 :
    recurrence4Scalar2Exceptional.coeff 185 =
      -(((((845035611255 * 10 ^ 70 +
        9571759636564688227554404327374923563366391351865535275351165580220501) * 10 ^ 70 +
        4168487966165052983353964941426724301679119778857531461505804971938038) * 10 ^ 70 +
        2903897766979820107906998342930308843187283256487389750605987010646921) * 10 ^ 70 +
        5364456300769966002862595656120183466030519820168855920362076559368145) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (185 - x)) = _
  rw [show 186 = 40 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_185_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (186 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_186 :
    recurrence4Scalar2Exceptional.coeff 186 =
      (((((2253116580848 * 10 ^ 70 +
        0804796284222044334732533544680367858534793123983383244913712832064302) * 10 ^ 70 +
        8171967804926376691165693163074983897269337001411892580726243040075160) * 10 ^ 70 +
        7160866049530463901250771925216965163074637284594082069308920405126033) * 10 ^ 70 +
        5639903000732771483387439876201610037952500299948310919693119650988331) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (186 - x)) = _
  rw [show 187 = 41 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_186_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (187 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_187 :
    recurrence4Scalar2Exceptional.coeff 187 =
      -(((((5913531994507 * 10 ^ 70 +
        1051411800948125784827618662502395748863385053694427346549797412365783) * 10 ^ 70 +
        0135994818131020712931283537383490524291000860841007514990928678680633) * 10 ^ 70 +
        7329885334462155614588990740187533682248389578854348957450215614128113) * 10 ^ 70 +
        8426411434283758904333232920129736814285457690511905986724921187729948) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (187 - x)) = _
  rw [show 188 = 42 +
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Exceptional_coeff_187_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
