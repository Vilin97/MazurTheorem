/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B3A4 coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A4_coeff_0
  recurrence4A4_coeff_1
  recurrence4A4_coeff_10
  recurrence4A4_coeff_100
  recurrence4A4_coeff_101
  recurrence4A4_coeff_102
  recurrence4A4_coeff_103
  recurrence4A4_coeff_104
  recurrence4A4_coeff_105
  recurrence4A4_coeff_106
  recurrence4A4_coeff_107
  recurrence4A4_coeff_108
  recurrence4A4_coeff_109
  recurrence4A4_coeff_11
  recurrence4A4_coeff_110
  recurrence4A4_coeff_111
  recurrence4A4_coeff_112
  recurrence4A4_coeff_113
  recurrence4A4_coeff_114
  recurrence4A4_coeff_115
  recurrence4A4_coeff_116
  recurrence4A4_coeff_117
  recurrence4A4_coeff_118
  recurrence4A4_coeff_119
  recurrence4A4_coeff_12
  recurrence4A4_coeff_120
  recurrence4A4_coeff_121
  recurrence4A4_coeff_122
  recurrence4A4_coeff_123
  recurrence4A4_coeff_124
  recurrence4A4_coeff_125
  recurrence4A4_coeff_126
  recurrence4A4_coeff_127
  recurrence4A4_coeff_128
  recurrence4A4_coeff_129
  recurrence4A4_coeff_13
  recurrence4A4_coeff_130
  recurrence4A4_coeff_131
  recurrence4A4_coeff_132
  recurrence4A4_coeff_133
  recurrence4A4_coeff_134
  recurrence4A4_coeff_135
  recurrence4A4_coeff_136
  recurrence4A4_coeff_137
  recurrence4A4_coeff_138
  recurrence4A4_coeff_139
  recurrence4A4_coeff_14
  recurrence4A4_coeff_140
  recurrence4A4_coeff_141
  recurrence4A4_coeff_142
  recurrence4A4_coeff_143
  recurrence4A4_coeff_144
  recurrence4A4_coeff_145
  recurrence4A4_coeff_146
  recurrence4A4_coeff_147
  recurrence4A4_coeff_148
  recurrence4A4_coeff_149
  recurrence4A4_coeff_15
  recurrence4A4_coeff_150
  recurrence4A4_coeff_151
  recurrence4A4_coeff_152
  recurrence4A4_coeff_153
  recurrence4A4_coeff_154
  recurrence4A4_coeff_155

attribute [local simp]
  recurrence4A4_coeff_156
  recurrence4A4_coeff_157
  recurrence4A4_coeff_158
  recurrence4A4_coeff_159
  recurrence4A4_coeff_16
  recurrence4A4_coeff_160
  recurrence4A4_coeff_161
  recurrence4A4_coeff_162
  recurrence4A4_coeff_163
  recurrence4A4_coeff_164
  recurrence4A4_coeff_165
  recurrence4A4_coeff_166
  recurrence4A4_coeff_167
  recurrence4A4_coeff_168
  recurrence4A4_coeff_169
  recurrence4A4_coeff_17
  recurrence4A4_coeff_170
  recurrence4A4_coeff_171
  recurrence4A4_coeff_172
  recurrence4A4_coeff_173
  recurrence4A4_coeff_174
  recurrence4A4_coeff_175
  recurrence4A4_coeff_176
  recurrence4A4_coeff_177
  recurrence4A4_coeff_178
  recurrence4A4_coeff_18
  recurrence4A4_coeff_19
  recurrence4A4_coeff_2
  recurrence4A4_coeff_20
  recurrence4A4_coeff_21
  recurrence4A4_coeff_22
  recurrence4A4_coeff_23
  recurrence4A4_coeff_24
  recurrence4A4_coeff_25
  recurrence4A4_coeff_26
  recurrence4A4_coeff_27
  recurrence4A4_coeff_28
  recurrence4A4_coeff_29
  recurrence4A4_coeff_3
  recurrence4A4_coeff_30
  recurrence4A4_coeff_31
  recurrence4A4_coeff_32
  recurrence4A4_coeff_33
  recurrence4A4_coeff_34
  recurrence4A4_coeff_35
  recurrence4A4_coeff_36
  recurrence4A4_coeff_37
  recurrence4A4_coeff_38
  recurrence4A4_coeff_39
  recurrence4A4_coeff_4
  recurrence4A4_coeff_40
  recurrence4A4_coeff_41
  recurrence4A4_coeff_42
  recurrence4A4_coeff_43
  recurrence4A4_coeff_44
  recurrence4A4_coeff_45
  recurrence4A4_coeff_46
  recurrence4A4_coeff_47
  recurrence4A4_coeff_48
  recurrence4A4_coeff_49
  recurrence4A4_coeff_5
  recurrence4A4_coeff_50
  recurrence4A4_coeff_51
  recurrence4A4_coeff_52

attribute [local simp]
  recurrence4A4_coeff_53
  recurrence4A4_coeff_54
  recurrence4A4_coeff_55
  recurrence4A4_coeff_56
  recurrence4A4_coeff_57
  recurrence4A4_coeff_58
  recurrence4A4_coeff_59
  recurrence4A4_coeff_6
  recurrence4A4_coeff_60
  recurrence4A4_coeff_61
  recurrence4A4_coeff_62
  recurrence4A4_coeff_63
  recurrence4A4_coeff_64
  recurrence4A4_coeff_65
  recurrence4A4_coeff_66
  recurrence4A4_coeff_67
  recurrence4A4_coeff_68
  recurrence4A4_coeff_69
  recurrence4A4_coeff_7
  recurrence4A4_coeff_70
  recurrence4A4_coeff_71
  recurrence4A4_coeff_72
  recurrence4A4_coeff_73
  recurrence4A4_coeff_74
  recurrence4A4_coeff_75
  recurrence4A4_coeff_76
  recurrence4A4_coeff_77
  recurrence4A4_coeff_78
  recurrence4A4_coeff_79
  recurrence4A4_coeff_8
  recurrence4A4_coeff_80
  recurrence4A4_coeff_81
  recurrence4A4_coeff_82
  recurrence4A4_coeff_83
  recurrence4A4_coeff_84
  recurrence4A4_coeff_85
  recurrence4A4_coeff_86
  recurrence4A4_coeff_87
  recurrence4A4_coeff_88
  recurrence4A4_coeff_89
  recurrence4A4_coeff_9
  recurrence4A4_coeff_90
  recurrence4A4_coeff_91
  recurrence4A4_coeff_92
  recurrence4A4_coeff_93
  recurrence4A4_coeff_94
  recurrence4A4_coeff_95
  recurrence4A4_coeff_96
  recurrence4A4_coeff_97
  recurrence4A4_coeff_98
  recurrence4A4_coeff_99
  recurrence4B3_coeff_0
  recurrence4B3_coeff_1
  recurrence4B3_coeff_10
  recurrence4B3_coeff_100
  recurrence4B3_coeff_101
  recurrence4B3_coeff_102
  recurrence4B3_coeff_103
  recurrence4B3_coeff_104
  recurrence4B3_coeff_105
  recurrence4B3_coeff_106
  recurrence4B3_coeff_107
  recurrence4B3_coeff_108
  recurrence4B3_coeff_109

attribute [local simp]
  recurrence4B3_coeff_11
  recurrence4B3_coeff_110
  recurrence4B3_coeff_111
  recurrence4B3_coeff_112
  recurrence4B3_coeff_113
  recurrence4B3_coeff_114
  recurrence4B3_coeff_115
  recurrence4B3_coeff_116
  recurrence4B3_coeff_117
  recurrence4B3_coeff_118
  recurrence4B3_coeff_119
  recurrence4B3_coeff_12
  recurrence4B3_coeff_120
  recurrence4B3_coeff_121
  recurrence4B3_coeff_122
  recurrence4B3_coeff_123
  recurrence4B3_coeff_124
  recurrence4B3_coeff_125
  recurrence4B3_coeff_126
  recurrence4B3_coeff_127
  recurrence4B3_coeff_128
  recurrence4B3_coeff_129
  recurrence4B3_coeff_13
  recurrence4B3_coeff_130
  recurrence4B3_coeff_131
  recurrence4B3_coeff_132
  recurrence4B3_coeff_133
  recurrence4B3_coeff_134
  recurrence4B3_coeff_135
  recurrence4B3_coeff_136
  recurrence4B3_coeff_137
  recurrence4B3_coeff_138
  recurrence4B3_coeff_139
  recurrence4B3_coeff_14
  recurrence4B3_coeff_140
  recurrence4B3_coeff_141
  recurrence4B3_coeff_142
  recurrence4B3_coeff_143
  recurrence4B3_coeff_144
  recurrence4B3_coeff_145
  recurrence4B3_coeff_146
  recurrence4B3_coeff_147
  recurrence4B3_coeff_148
  recurrence4B3_coeff_149
  recurrence4B3_coeff_15
  recurrence4B3_coeff_150
  recurrence4B3_coeff_151
  recurrence4B3_coeff_152
  recurrence4B3_coeff_153
  recurrence4B3_coeff_154
  recurrence4B3_coeff_155
  recurrence4B3_coeff_156
  recurrence4B3_coeff_157
  recurrence4B3_coeff_158
  recurrence4B3_coeff_159
  recurrence4B3_coeff_16
  recurrence4B3_coeff_160
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163
  recurrence4B3_coeff_164
  recurrence4B3_coeff_17
  recurrence4B3_coeff_18
  recurrence4B3_coeff_19

attribute [local simp]
  recurrence4B3_coeff_2
  recurrence4B3_coeff_20
  recurrence4B3_coeff_21
  recurrence4B3_coeff_22
  recurrence4B3_coeff_23
  recurrence4B3_coeff_24
  recurrence4B3_coeff_25
  recurrence4B3_coeff_26
  recurrence4B3_coeff_27
  recurrence4B3_coeff_28
  recurrence4B3_coeff_29
  recurrence4B3_coeff_3
  recurrence4B3_coeff_30
  recurrence4B3_coeff_31
  recurrence4B3_coeff_32
  recurrence4B3_coeff_33
  recurrence4B3_coeff_34
  recurrence4B3_coeff_35
  recurrence4B3_coeff_36
  recurrence4B3_coeff_37
  recurrence4B3_coeff_38
  recurrence4B3_coeff_39
  recurrence4B3_coeff_4
  recurrence4B3_coeff_40
  recurrence4B3_coeff_41
  recurrence4B3_coeff_42
  recurrence4B3_coeff_43
  recurrence4B3_coeff_44
  recurrence4B3_coeff_45
  recurrence4B3_coeff_46
  recurrence4B3_coeff_47
  recurrence4B3_coeff_48
  recurrence4B3_coeff_49
  recurrence4B3_coeff_5
  recurrence4B3_coeff_50
  recurrence4B3_coeff_51
  recurrence4B3_coeff_52
  recurrence4B3_coeff_53
  recurrence4B3_coeff_54
  recurrence4B3_coeff_55
  recurrence4B3_coeff_56
  recurrence4B3_coeff_57
  recurrence4B3_coeff_58
  recurrence4B3_coeff_59
  recurrence4B3_coeff_6
  recurrence4B3_coeff_60
  recurrence4B3_coeff_61
  recurrence4B3_coeff_62
  recurrence4B3_coeff_63
  recurrence4B3_coeff_64
  recurrence4B3_coeff_65
  recurrence4B3_coeff_66
  recurrence4B3_coeff_67
  recurrence4B3_coeff_68
  recurrence4B3_coeff_69
  recurrence4B3_coeff_7
  recurrence4B3_coeff_70
  recurrence4B3_coeff_71
  recurrence4B3_coeff_72
  recurrence4B3_coeff_73
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77

attribute [local simp]
  recurrence4B3_coeff_78
  recurrence4B3_coeff_79
  recurrence4B3_coeff_8
  recurrence4B3_coeff_80
  recurrence4B3_coeff_81
  recurrence4B3_coeff_82
  recurrence4B3_coeff_83
  recurrence4B3_coeff_84
  recurrence4B3_coeff_85
  recurrence4B3_coeff_86
  recurrence4B3_coeff_87
  recurrence4B3_coeff_88
  recurrence4B3_coeff_89
  recurrence4B3_coeff_9
  recurrence4B3_coeff_90
  recurrence4B3_coeff_91
  recurrence4B3_coeff_92
  recurrence4B3_coeff_93
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

private theorem recurrence4B3A4_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (183 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (183 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_183 :
    recurrence4B3A4.coeff 183 =
      -(((4180143858508476540858978507361311594826244345277641596311240 * 10 ^ 70 +
        0641818959349541219209518458530186536004694959663759479618022342150206) * 10 ^ 70 +
        3664145813826265744944030608338534521296853947342423676481703253044203) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (183 - x)) = _
  rw [show 184 = 5 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (184 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_184 :
    recurrence4B3A4.coeff 184 =
      (((3995816924820522537211226265839682699921957837883005710593366 * 10 ^ 70 +
        3858911078805868863432878931144161434317263267693006258359699396440768) * 10 ^ 70 +
        3943534384690300538572576325210653432021699901573773413380384144847087) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (184 - x)) = _
  rw [show 185 = 6 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (185 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_185 :
    recurrence4B3A4.coeff 185 =
      -(((3637554994176223764487902915643030931817138031346047444367038 * 10 ^ 70 +
        5046720310916804221523594856301078783615220374007231004201209203717982) * 10 ^ 70 +
        6366065446198122094303172896538850001480332741674881915479347559553231) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (185 - x)) = _
  rw [show 186 = 7 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (186 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_186 :
    recurrence4B3A4.coeff 186 =
      (((3177527061372675029112592537232894480896146250555795637816807 * 10 ^ 70 +
        4798615812600696153475482859900834916036709455710829156594911339383395) * 10 ^ 70 +
        2881658341991428123653352191424761615930022423850656443765135076973737) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (186 - x)) = _
  rw [show 187 = 8 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (187 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_187 :
    recurrence4B3A4.coeff 187 =
      -(((2676302418930648452781809475195484162609561825123449097881865 * 10 ^ 70 +
        6357669034280410612738959802667553099191980345307481550966647192736023) * 10 ^ 70 +
        4996517264711280953494278100439327495057689324055015718769260618624337) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (187 - x)) = _
  rw [show 188 = 9 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (188 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_188 :
    recurrence4B3A4.coeff 188 =
      (((2180451331058211141053987210843984178538410832164292291397024 * 10 ^ 70 +
        4467581584911962764290187519499064048040314188338237942304421964150338) * 10 ^ 70 +
        4352460408472028842956116364331291654691697792194005218963959859801864) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (188 - x)) = _
  rw [show 189 = 10 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (189 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_189 :
    recurrence4B3A4.coeff 189 =
      -(((1722229225596053738638075709445920709380571703348238685933114 * 10 ^ 70 +
        4599958109385506739917689943653705389180213395975309502164664068308667) * 10 ^ 70 +
        2739042997806692101115594167223470012468553686783408275453161343832882) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (189 - x)) = _
  rw [show 190 = 11 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (190 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_190 :
    recurrence4B3A4.coeff 190 =
      (((1320841728590254856233253737266523880283984573213591561840804 * 10 ^ 70 +
        5578444898238591514035341586819213528937557717487623390260807532727974) * 10 ^ 70 +
        7857792275732133725729145080030527917802653241966207015660017672516231) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (190 - x)) = _
  rw [show 191 = 12 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (191 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_191 :
    recurrence4B3A4.coeff 191 =
      -(((984705251410877097810170665628424516837962282567609617971127 * 10 ^ 70 +
        8022529597410387695630443218269727514257609544498621427393735543299868) * 10 ^ 70 +
        6658959826420785596275037844302927959510053471478889753490478405358374) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (191 - x)) = _
  rw [show 192 = 13 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (192 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_192 :
    recurrence4B3A4.coeff 192 =
      (((714145684126146521918844766032869231203187859436656429145310 * 10 ^ 70 +
        0023465742975566153461646714062887689131902689016353468014854729379367) * 10 ^ 70 +
        3790474021876462459045979284228976146311549980162305805166022530062218) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (192 - x)) = _
  rw [show 193 = 14 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (193 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_193 :
    recurrence4B3A4.coeff 193 =
      -(((504081512789996793217375976653160174143461002001018485259565 * 10 ^ 70 +
        3957720017433161111099175303125443874519184497137846436926687826691090) * 10 ^ 70 +
        4893224057688477823693448629441552363196932121888747106129974280572327) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (193 - x)) = _
  rw [show 194 = 15 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (194 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_194 :
    recurrence4B3A4.coeff 194 =
      (((346378571220193938768486041292234201317363596106488008205391 * 10 ^ 70 +
        9116724825822999540249629625091435066520519889326230126490795344511112) * 10 ^ 70 +
        7945504311934304221637129835606473555669420178592183769315727561092199) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (194 - x)) = _
  rw [show 195 = 16 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (195 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_195 :
    recurrence4B3A4.coeff 195 =
      -(((231707413191399880825985717789625451763145646191784547366928 * 10 ^ 70 +
        2631668668566468025735693021135499694876684488211649196777033821912757) * 10 ^ 70 +
        0586572266020341771102363167834672347095077519841581022937779134583594) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (195 - x)) = _
  rw [show 196 = 17 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (196 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_196 :
    recurrence4B3A4.coeff 196 =
      (((150856579718489913044813029858362015189311428900463560427222 * 10 ^ 70 +
        0126414543590588878115024417490523683241394912055663116539332829671007) * 10 ^ 70 +
        0413221257576309478377796571255117756089021820025088366788439502605124) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (196 - x)) = _
  rw [show 197 = 18 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (197 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_197 :
    recurrence4B3A4.coeff 197 =
      -(((95543019094774836853934989025377237940276505687894985567619 * 10 ^ 70 +
        5565611381939768751394219851828267899083101118462284159783826610587225) * 10 ^ 70 +
        2125678330702915102196443914189860752893604811087882274985830142255946) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (197 - x)) = _
  rw [show 198 = 19 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (198 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_198 :
    recurrence4B3A4.coeff 198 =
      (((58812074855794631734325199623534389286671219998707638108630 * 10 ^ 70 +
        5646408583802541942888179605306548572044466971801757442666874208622066) * 10 ^ 70 +
        9928129553965639809067727817228705228760348735688178866152254924967803) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (198 - x)) = _
  rw [show 199 = 20 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (199 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_199 :
    recurrence4B3A4.coeff 199 =
      -(((35138600088274906858679850136091915678461940089669326848877 * 10 ^ 70 +
        6324180382272201097342589689512645461687388872226799733445086767726408) * 10 ^ 70 +
        0423864248112521654883754075596200254263631297842759240599074652862356) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (199 - x)) = _
  rw [show 200 = 21 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (200 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_200 :
    recurrence4B3A4.coeff 200 =
      (((20336563367429645980705767828324404094317349173185313056688 * 10 ^ 70 +
        4973136070477178021307700458457005111914924403315209095559189698815951) * 10 ^ 70 +
        1332600817723987860302969586019259570178400834320535715869597855506083) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (200 - x)) = _
  rw [show 201 = 22 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (201 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_201 :
    recurrence4B3A4.coeff 201 =
      -(((11366495353273240915894251252602127609755405139871274618924 * 10 ^ 70 +
        0017378782493623633939340239665964183824090901440319715383801714625556) * 10 ^ 70 +
        5342393005135214772007781416179988740086706905859750288426417788799854) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (201 - x)) = _
  rw [show 202 = 23 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 14 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (202 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_202 :
    recurrence4B3A4.coeff 202 =
      (((6106540927608630249631005500769042713107190447748993220599 * 10 ^ 70 +
        8590906778975300138068001784354319971185231231826245698717165507190653) * 10 ^ 70 +
        7308980918325408693415339551878617825642748039427543399697946189007655) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (202 - x)) = _
  rw [show 203 = 24 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 13 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (203 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_203 :
    recurrence4B3A4.coeff 203 =
      -(((3129677075487442526739522860593903798181312967633968185800 * 10 ^ 70 +
        9767851529917139668478391223897545395352853478935381814118118535659206) * 10 ^ 70 +
        0447290170921129070301286897806585942936076909818553235961586964151156) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (203 - x)) = _
  rw [show 204 = 25 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 12 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (204 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_204 :
    recurrence4B3A4.coeff 204 =
      (((1510291615863271652745588967228798771702352528374504091010 * 10 ^ 70 +
        0386297740277753843676234220513239916496687497476749666542765445906219) * 10 ^ 70 +
        0546797136437315312697818607998355619391043469496245220074417804903562) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (204 - x)) = _
  rw [show 205 = 26 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 11 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (205 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_205 :
    recurrence4B3A4.coeff 205 =
      -(((669151369635943777137227279591927067428138744845602147236 * 10 ^ 70 +
        6278988363171026439733999398561714600295047333756952507593096267034920) * 10 ^ 70 +
        4754031671917475442055602563079619599715866311168312072135178698176035) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (205 - x)) = _
  rw [show 206 = 27 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 10 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (206 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_206 :
    recurrence4B3A4.coeff 206 =
      (((256718499677192076717525134096301269348565081267257180630 * 10 ^ 70 +
        0842495130264200929985569041795188301138543175889286988467221910271302) * 10 ^ 70 +
        2591630221781658401101264978192826397124205872771889431046434693668734) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (206 - x)) = _
  rw [show 207 = 28 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 9 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (207 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_207 :
    recurrence4B3A4.coeff 207 =
      -(((69891038407795409698015121984336367195362249305798518939 * 10 ^ 70 +
        2617507220029325565161355343346789296034895690354719930702655038729659) * 10 ^ 70 +
        9608586900182371864949750810740324806258613736158477095148866271368851) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (207 - x)) = _
  rw [show 208 = 29 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 8 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (208 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_208 :
    recurrence4B3A4.coeff 208 =
      -(((4644811418846471185475020929850689047343790350421460890 * 10 ^ 70 +
        9072143416509198543215886534074850676747997866585115811395635436139522) * 10 ^ 70 +
        8378961249441631079165677041594721651531930426076708835993211613325030) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (208 - x)) = _
  rw [show 209 = 30 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 7 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (209 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_209 :
    recurrence4B3A4.coeff 209 =
      (((27289912642454765826312633873342292917547730625619733898 * 10 ^ 70 +
        4033584147136267163038263415899593117142810857477950137015734780530124) * 10 ^ 70 +
        4856758249590434346985456121849394196256858780766555077078683971816303) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (209 - x)) = _
  rw [show 210 = 31 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 6 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (210 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_210 :
    recurrence4B3A4.coeff 210 =
      -(((28538662785557589200446352191530794082872199963341633507 * 10 ^ 70 +
        2530416888757232713771928930964847411744201702671173197061216227079737) * 10 ^ 70 +
        5418326981530225282155540262294953891603022902815591441848590929760152) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (210 - x)) = _
  rw [show 211 = 32 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 5 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (211 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_211 :
    recurrence4B3A4.coeff 211 =
      (((22740468722941059636481740304122389338558018118670063792 * 10 ^ 70 +
        6739297548187225322262873024342313256868189453795131262624095718159242) * 10 ^ 70 +
        8889134811778444195013634990379247945958255552260567683883866667574813) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (211 - x)) = _
  rw [show 212 = 33 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 4 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (212 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_212 :
    recurrence4B3A4.coeff 212 =
      -(((15982033767915420290951339770683992087420260362520967625 * 10 ^ 70 +
        8688680289144741422122537119680085731306020658880030544537587761165213) * 10 ^ 70 +
        7075326731465485423294173741174436209993435464230015113762246374955387) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (212 - x)) = _
  rw [show 213 = 34 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 3 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (213 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_213 :
    recurrence4B3A4.coeff 213 =
      (((10396708977828404146225380200698366691855309159576298242 * 10 ^ 70 +
        5106559213671476955529410806472048236705641154805546931169857950163551) * 10 ^ 70 +
        8969102711711199135123631246219244210132897744313617954707985937554406) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (213 - x)) = _
  rw [show 214 = 35 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 2 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B3A4_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4B3A4_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff (165 + x) *
        remainder4Coefficient4.coeff (214 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4B3A4_coeff_214 :
    recurrence4B3A4.coeff 214 =
      -(((6399004211506657593313676377347875038156418109631257623 * 10 ^ 70 +
        7216730879231001308318406526921995151161990010568096393430565551914900) * 10 ^ 70 +
        5770148811002709584707260745057022251037426621145702283260859575494289) : ℚ) := by
  unfold recurrence4B3A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient3.coeff x * remainder4Coefficient4.coeff (214 - x)) = _
  rw [show 215 = 36 +
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 1 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4B3A4_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B3A4_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
