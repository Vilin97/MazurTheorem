/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B1A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B1_coeff_0
  recurrence5B1_coeff_1
  recurrence5B1_coeff_2
  recurrence5B1_coeff_3
  recurrence5B1_coeff_4
  recurrence5B1_coeff_5
  recurrence5B1_coeff_6
  recurrence5B1_coeff_7
  recurrence5B1_coeff_8
  recurrence5B1_coeff_9
  recurrence5B1_coeff_10
  recurrence5B1_coeff_11
  recurrence5B1_coeff_12
  recurrence5B1_coeff_13
  recurrence5B1_coeff_14
  recurrence5B1_coeff_15
  recurrence5B1_coeff_16
  recurrence5B1_coeff_17
  recurrence5B1_coeff_18
  recurrence5B1_coeff_19
  recurrence5B1_coeff_20
  recurrence5B1_coeff_21
  recurrence5B1_coeff_22
  recurrence5B1_coeff_23
  recurrence5B1_coeff_24
  recurrence5B1_coeff_25
  recurrence5B1_coeff_26
  recurrence5B1_coeff_27
  recurrence5B1_coeff_28
  recurrence5B1_coeff_29
  recurrence5B1_coeff_30
  recurrence5B1_coeff_31
  recurrence5B1_coeff_32
  recurrence5B1_coeff_33
  recurrence5B1_coeff_34
  recurrence5B1_coeff_35
  recurrence5B1_coeff_36
  recurrence5B1_coeff_37
  recurrence5B1_coeff_38
  recurrence5B1_coeff_39
  recurrence5B1_coeff_40
  recurrence5B1_coeff_41
  recurrence5B1_coeff_42
  recurrence5B1_coeff_43
  recurrence5B1_coeff_44
  recurrence5B1_coeff_45
  recurrence5B1_coeff_46
  recurrence5B1_coeff_47
  recurrence5B1_coeff_48
  recurrence5B1_coeff_49
  recurrence5B1_coeff_50
  recurrence5B1_coeff_51
  recurrence5B1_coeff_52
  recurrence5B1_coeff_53
  recurrence5B1_coeff_54
  recurrence5B1_coeff_55
  recurrence5B1_coeff_56
  recurrence5B1_coeff_57
  recurrence5B1_coeff_58
  recurrence5B1_coeff_59
  recurrence5B1_coeff_60
  recurrence5B1_coeff_61
  recurrence5B1_coeff_62
  recurrence5B1_coeff_63

attribute [local simp]
  recurrence5B1_coeff_64
  recurrence5B1_coeff_65
  recurrence5B1_coeff_66
  recurrence5B1_coeff_67
  recurrence5B1_coeff_68
  recurrence5B1_coeff_69
  recurrence5B1_coeff_70
  recurrence5B1_coeff_71
  recurrence5B1_coeff_72
  recurrence5B1_coeff_73
  recurrence5B1_coeff_74
  recurrence5B1_coeff_75
  recurrence5B1_coeff_76
  recurrence5B1_coeff_77
  recurrence5B1_coeff_78
  recurrence5B1_coeff_79
  recurrence5B1_coeff_80
  recurrence5B1_coeff_81
  recurrence5B1_coeff_82
  recurrence5B1_coeff_83
  recurrence5B1_coeff_84
  recurrence5B1_coeff_85
  recurrence5B1_coeff_86
  recurrence5B1_coeff_87
  recurrence5B1_coeff_88
  recurrence5B1_coeff_89
  recurrence5B1_coeff_90
  recurrence5B1_coeff_91
  recurrence5B1_coeff_92
  recurrence5B1_coeff_93
  recurrence5B1_coeff_94
  recurrence5B1_coeff_95
  recurrence5B1_coeff_96
  recurrence5B1_coeff_97
  recurrence5B1_coeff_98
  recurrence5B1_coeff_99
  recurrence5B1_coeff_100
  recurrence5B1_coeff_101
  recurrence5B1_coeff_102
  recurrence5B1_coeff_103
  recurrence5B1_coeff_104
  recurrence5B1_coeff_105
  recurrence5B1_coeff_106
  recurrence5B1_coeff_107
  recurrence5B1_coeff_108
  recurrence5B1_coeff_109
  recurrence5B1_coeff_110
  recurrence5B1_coeff_111
  recurrence5B1_coeff_112
  recurrence5B1_coeff_113
  recurrence5B1_coeff_114
  recurrence5B1_coeff_115
  recurrence5B1_coeff_116
  recurrence5B1_coeff_117
  recurrence5B1_coeff_118
  recurrence5B1_coeff_119
  recurrence5B1_coeff_120
  recurrence5B1_coeff_121
  recurrence5B1_coeff_122
  recurrence5B1_coeff_123
  recurrence5B1_coeff_124
  recurrence5B1_coeff_125
  recurrence5B1_coeff_126
  recurrence5B1_coeff_127

attribute [local simp]
  recurrence5B1_coeff_128
  recurrence5B1_coeff_129
  recurrence5B1_coeff_130
  recurrence5B1_coeff_131
  recurrence5B1_coeff_132
  recurrence5B1_coeff_133
  recurrence5B1_coeff_134
  recurrence5B1_coeff_135
  recurrence5B1_coeff_136
  recurrence5B1_coeff_137
  recurrence5B1_coeff_138
  recurrence5B1_coeff_139
  recurrence5B1_coeff_140
  recurrence5B1_coeff_141
  recurrence5B1_coeff_142
  recurrence5B1_coeff_143
  recurrence5B1_coeff_144
  recurrence5B1_coeff_145
  recurrence5B1_coeff_146
  recurrence5B1_coeff_147
  recurrence5B1_coeff_148
  recurrence5B1_coeff_149
  recurrence5A3_coeff_0
  recurrence5A3_coeff_1
  recurrence5A3_coeff_2
  recurrence5A3_coeff_3
  recurrence5A3_coeff_4
  recurrence5A3_coeff_5
  recurrence5A3_coeff_6
  recurrence5A3_coeff_7
  recurrence5A3_coeff_8
  recurrence5A3_coeff_9
  recurrence5A3_coeff_10
  recurrence5A3_coeff_11
  recurrence5A3_coeff_12
  recurrence5A3_coeff_13
  recurrence5A3_coeff_14
  recurrence5A3_coeff_15
  recurrence5A3_coeff_16
  recurrence5A3_coeff_17
  recurrence5A3_coeff_18
  recurrence5A3_coeff_19
  recurrence5A3_coeff_20
  recurrence5A3_coeff_21
  recurrence5A3_coeff_22
  recurrence5A3_coeff_23
  recurrence5A3_coeff_24
  recurrence5A3_coeff_25
  recurrence5A3_coeff_26
  recurrence5A3_coeff_27
  recurrence5A3_coeff_28
  recurrence5A3_coeff_29
  recurrence5A3_coeff_30
  recurrence5A3_coeff_31
  recurrence5A3_coeff_32
  recurrence5A3_coeff_33
  recurrence5A3_coeff_34
  recurrence5A3_coeff_35
  recurrence5A3_coeff_36
  recurrence5A3_coeff_37
  recurrence5A3_coeff_38
  recurrence5A3_coeff_39
  recurrence5A3_coeff_40
  recurrence5A3_coeff_41

attribute [local simp]
  recurrence5A3_coeff_42
  recurrence5A3_coeff_43
  recurrence5A3_coeff_44
  recurrence5A3_coeff_45
  recurrence5A3_coeff_46
  recurrence5A3_coeff_47
  recurrence5A3_coeff_48
  recurrence5A3_coeff_49
  recurrence5A3_coeff_50
  recurrence5A3_coeff_51
  recurrence5A3_coeff_52
  recurrence5A3_coeff_53
  recurrence5A3_coeff_54
  recurrence5A3_coeff_55
  recurrence5A3_coeff_56
  recurrence5A3_coeff_57
  recurrence5A3_coeff_58
  recurrence5A3_coeff_59
  recurrence5A3_coeff_60
  recurrence5A3_coeff_61
  recurrence5A3_coeff_62
  recurrence5A3_coeff_63
  recurrence5A3_coeff_64
  recurrence5A3_coeff_65
  recurrence5A3_coeff_66
  recurrence5A3_coeff_67
  recurrence5A3_coeff_68
  recurrence5A3_coeff_69
  recurrence5A3_coeff_70
  recurrence5A3_coeff_71
  recurrence5A3_coeff_72
  recurrence5A3_coeff_73
  recurrence5A3_coeff_74
  recurrence5A3_coeff_75
  recurrence5A3_coeff_76
  recurrence5A3_coeff_77
  recurrence5A3_coeff_78
  recurrence5A3_coeff_79
  recurrence5A3_coeff_80
  recurrence5A3_coeff_81
  recurrence5A3_coeff_82
  recurrence5A3_coeff_83
  recurrence5A3_coeff_84
  recurrence5A3_coeff_85
  recurrence5A3_coeff_86
  recurrence5A3_coeff_87
  recurrence5A3_coeff_88
  recurrence5A3_coeff_89
  recurrence5A3_coeff_90
  recurrence5A3_coeff_91
  recurrence5A3_coeff_92
  recurrence5A3_coeff_93
  recurrence5A3_coeff_94
  recurrence5A3_coeff_95
  recurrence5A3_coeff_96
  recurrence5A3_coeff_97
  recurrence5A3_coeff_98
  recurrence5A3_coeff_99
  recurrence5A3_coeff_100
  recurrence5A3_coeff_101
  recurrence5A3_coeff_102
  recurrence5A3_coeff_103
  recurrence5A3_coeff_104
  recurrence5A3_coeff_105

attribute [local simp]
  recurrence5A3_coeff_106
  recurrence5A3_coeff_107
  recurrence5A3_coeff_108
  recurrence5A3_coeff_109
  recurrence5A3_coeff_110
  recurrence5A3_coeff_111
  recurrence5A3_coeff_112
  recurrence5A3_coeff_113
  recurrence5A3_coeff_114
  recurrence5A3_coeff_115
  recurrence5A3_coeff_116
  recurrence5A3_coeff_117
  recurrence5A3_coeff_118
  recurrence5A3_coeff_119
  recurrence5A3_coeff_120
  recurrence5A3_coeff_121
  recurrence5A3_coeff_122
  recurrence5A3_coeff_123
  recurrence5A3_coeff_124
  recurrence5A3_coeff_125
  recurrence5A3_coeff_126
  recurrence5A3_coeff_127
  recurrence5A3_coeff_128
  recurrence5A3_coeff_129
  recurrence5A3_coeff_130
  recurrence5A3_coeff_131
  recurrence5A3_coeff_132
  recurrence5A3_coeff_133
  recurrence5A3_coeff_134
  recurrence5A3_coeff_135
  recurrence5A3_coeff_136
  recurrence5A3_coeff_137
  recurrence5A3_coeff_138
  recurrence5A3_coeff_139
  recurrence5A3_coeff_140
  recurrence5A3_coeff_141
  recurrence5A3_coeff_142
  recurrence5A3_coeff_143
  recurrence5A3_coeff_144
  recurrence5A3_coeff_145
  recurrence5A3_coeff_146
  recurrence5A3_coeff_147
  recurrence5A3_coeff_148
  recurrence5A3_coeff_149
  recurrence5A3_coeff_150
  recurrence5A3_coeff_151
  recurrence5A3_coeff_152
  recurrence5A3_coeff_153
  recurrence5A3_coeff_154
  recurrence5A3_coeff_155
  recurrence5A3_coeff_156
  recurrence5A3_coeff_157
  recurrence5A3_coeff_158
  recurrence5A3_coeff_159
  recurrence5A3_coeff_160
  recurrence5A3_coeff_161
  recurrence5A3_coeff_162
  recurrence5A3_coeff_163
  recurrence5A3_coeff_164

private theorem recurrence5B1A3_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (184 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_184 :
    recurrence5B1A3.coeff 184 =
      -((((3172591669950470 * 10 ^ 70 +
        3117848169261494798353356916486739123748733135827238134365795456001274) * 10 ^ 70 +
        4024229980423821147446948768939578893263184663804797363974949577025814) * 10 ^ 70 +
        4544916761693237964402363004850624024107076442551175421767562095715774) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 20 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 2 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (185 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_185 :
    recurrence5B1A3.coeff 185 =
      ((((2621383613296346 * 10 ^ 70 +
        8781073551209731810679929409237878531690981457957746368798145741638424) * 10 ^ 70 +
        7130748609238725168858905521779363818954798838442021429076002589109228) * 10 ^ 70 +
        0323675767094156735014036061534654877507548613961146890639932043327589) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 21 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 1 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (186 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_186 :
    recurrence5B1A3.coeff 186 =
      -((((1887171857404294 * 10 ^ 70 +
        0931911352196016422908787924834950597444092475119787234918267600202328) * 10 ^ 70 +
        8493047673190939274910351570194789860642081461990711258455485488547967) * 10 ^ 70 +
        6151762300291903139560878929101501394810066048628203285538828418157449) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 22 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (187 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_187 :
    recurrence5B1A3.coeff 187 =
      ((((1235412132012376 * 10 ^ 70 +
        2555563888233247413025374429569548601497250915271488522123071137006562) * 10 ^ 70 +
        4066929186949037322117212937288759207670784113706921523058481647719162) * 10 ^ 70 +
        6996002436330733963264237931071747300879406937121372321532417334022480) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 23 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 31 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (188 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_188 :
    recurrence5B1A3.coeff 188 =
      -((((748696731855336 * 10 ^ 70 +
        0486606207628409066254395736746351236023678698564299235490255241674132) * 10 ^ 70 +
        0909338820213000186556474152262090225773257993130058025209417181838912) * 10 ^ 70 +
        4264056296064662189191608241060553093141651885874929471271553497973066) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 24 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 30 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (189 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_189 :
    recurrence5B1A3.coeff 189 =
      ((((422825305877086 * 10 ^ 70 +
        3519185704377583867568448620935708545939899239571648014804907625187904) * 10 ^ 70 +
        9169836865984658429206537641955046439237212791648950714210347147004740) * 10 ^ 70 +
        0470572064581151257910552748873882425279213954326782187641906021266229) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 25 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 29 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (190 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_190 :
    recurrence5B1A3.coeff 190 =
      -((((222229740744681 * 10 ^ 70 +
        2253480997395341638415843587555543183511919162069991231176880392894533) * 10 ^ 70 +
        4823033426174026435445318445979140957933343698321347386286122978935165) * 10 ^ 70 +
        6959041041792331820486517308192123663131890679963738918856011017613911) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 26 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 28 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (191 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_191 :
    recurrence5B1A3.coeff 191 =
      ((((107552472377463 * 10 ^ 70 +
        6602247201734166220241145215369825578262419966262754569733473317838368) * 10 ^ 70 +
        9136994020176901661294883521012983543484357388129835429231133057359544) * 10 ^ 70 +
        7466169135345708378890484148024810779206553276349096908817478172612229) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 27 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (192 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_192 :
    recurrence5B1A3.coeff 192 =
      -((((46606450430257 * 10 ^ 70 +
        0456844321509393360567145812862427459816622015845000229310752810824835) * 10 ^ 70 +
        4173802211862737196382950516622449126191953917835299588592230130126274) * 10 ^ 70 +
        8621625054562789528509426334325685787425430004209793044022347567881176) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 28 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (193 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_193 :
    recurrence5B1A3.coeff 193 =
      ((((16742386760387 * 10 ^ 70 +
        6623260712028782546722332134196918591378209828961649043404801115809848) * 10 ^ 70 +
        4662605462728452840486516023006610079913128395930849788970852674289665) * 10 ^ 70 +
        4805912896633660437112948966073948045025359611846427144277940217379568) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 29 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 25 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (194 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_194 :
    recurrence5B1A3.coeff 194 =
      -((((3568930129904 * 10 ^ 70 +
        1065297006426968911923491700488599011707087216948333128718073285438145) * 10 ^ 70 +
        5739038902233538676682236846271119735828133321385335691535034118548973) * 10 ^ 70 +
        4631533997043068430736523952176621060328585249498308584513635282414862) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 30 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 24 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (195 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_195 :
    recurrence5B1A3.coeff 195 =
      -((((1333547296810 * 10 ^ 70 +
        2216305558486899146392464377441179985974294823536595952796049491704330) * 10 ^ 70 +
        5204591863562158963313542386988232569804294301857263441855844766998820) * 10 ^ 70 +
        6653122931166873624224158340259947558725365835201298024762289844821909) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 31 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (196 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_196 :
    recurrence5B1A3.coeff 196 =
      ((((2529770858323 * 10 ^ 70 +
        3991846018269387864685888735024711478510602111334144104028652711276834) * 10 ^ 70 +
        1537661530406075109807856986463839392047593285314454766033856505157249) * 10 ^ 70 +
        8551595564773514943150020935025645944600954872603541482564866368500349) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 32 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (197 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_197 :
    recurrence5B1A3.coeff 197 =
      -((((2304965858753 * 10 ^ 70 +
        2677058927590319329646105272622864060280333153859424376486219340695701) * 10 ^ 70 +
        5801231657780276148139482443439712902433547228618599283386464382980735) * 10 ^ 70 +
        7576614802840951231231338880183659349267276068337252921183431444086091) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 33 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 21 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (198 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_198 :
    recurrence5B1A3.coeff 198 =
      ((((1697646554394 * 10 ^ 70 +
        2032209954997916685285323156479072224858634970257874339572368399589805) * 10 ^ 70 +
        6925305507251209957381879046683276073597066325766748168519794460481935) * 10 ^ 70 +
        7565771053707463287212019480590706036012791571371480231649652576624915) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 34 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 20 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (199 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_199 :
    recurrence5B1A3.coeff 199 =
      -((((1116377313102 * 10 ^ 70 +
        8420355740900661889566800591895212748325652513580875918620440474882640) * 10 ^ 70 +
        0259714484143456839074677500539711414601778883523873964540868294741728) * 10 ^ 70 +
        2541935240834607829598250917137458564423206110891246393937907065545389) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 35 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (200 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_200 :
    recurrence5B1A3.coeff 200 =
      ((((679767278873 * 10 ^ 70 +
        8648215487895280297808510023085974048733903463415736239181041463608486) * 10 ^ 70 +
        1537380300299218648046191192902181524591328892605269487941292788942818) * 10 ^ 70 +
        6323652081702439490088518861912173992421571914594463499760044249620063) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 36 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 18 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (201 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_201 :
    recurrence5B1A3.coeff 201 =
      -((((389725248462 * 10 ^ 70 +
        8558417394915663132269896035300230952890739277026546543632851803258402) * 10 ^ 70 +
        9478403886091046361030048377874796622736559918480966017024526107241348) * 10 ^ 70 +
        3998604578510787326085015178137707339285632630633665691212507764794302) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 37 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 17 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (202 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_202 :
    recurrence5B1A3.coeff 202 =
      ((((212154418763 * 10 ^ 70 +
        7804424256375848388738927977913339617585869769049884057395329953433419) * 10 ^ 70 +
        4299578897460946657485598985741495911093559463618574770836555462044105) * 10 ^ 70 +
        5563797137564573992329345829246825795929329569478371685906908270413776) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 38 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (203 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_203 :
    recurrence5B1A3.coeff 203 =
      -((((110111236024 * 10 ^ 70 +
        8988784018832301300441820823051185894631096471786290786991942922622019) * 10 ^ 70 +
        7071578226540123125623985269664034011509241499030945694007422822956294) * 10 ^ 70 +
        3578402077751291555727661065894815315764010741193879509274439243365660) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 39 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (204 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_204 :
    recurrence5B1A3.coeff 204 =
      ((((54572852897 * 10 ^ 70 +
        8578908346250739957737607651832341858875629635312563417396973118796284) * 10 ^ 70 +
        2060268933698258458333030335547640611743017905843939103148494650494903) * 10 ^ 70 +
        0191918819248137013658158425597695392742159031212001340651888798144104) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 40 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 14 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (205 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_205 :
    recurrence5B1A3.coeff 205 =
      -((((25821654441 * 10 ^ 70 +
        8155186010385139644844567201366017076595103311423546883694464988973882) * 10 ^ 70 +
        8100781927035281062987285433322905031471291157564319623448037228364624) * 10 ^ 70 +
        6661260502410617490441244349715174669515247355482675384662086118173788) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 41 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 13 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (206 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_206 :
    recurrence5B1A3.coeff 206 =
      ((((11643438502 * 10 ^ 70 +
        9961377340920586411927444420664077116433370739592159700617960828458275) * 10 ^ 70 +
        5666441157685412409711130500151390042895916519666964370334696793016174) * 10 ^ 70 +
        7157068832754152017845244954436222336939494210634043394397089515158908) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 42 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 12 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (207 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_207 :
    recurrence5B1A3.coeff 207 =
      -((((4986327634 * 10 ^ 70 +
        1702527065842475973354232269621562616995053016910181878739572577071752) * 10 ^ 70 +
        6433998375580226983483926668695394432385370304210025259300031286013684) * 10 ^ 70 +
        8980838355552498279853346672808111387222163017797870033304037292216582) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 43 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 11 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (208 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_208 :
    recurrence5B1A3.coeff 208 =
      ((((2016751701 * 10 ^ 70 +
        2178418428828565547347595843990256980503173717245865072322027514923625) * 10 ^ 70 +
        1236588640991712635418375259586079303909091891161471923441225074245792) * 10 ^ 70 +
        7265265163514030305685426556476468182038830934849421706190294844242350) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 44 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 10 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (209 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_209 :
    recurrence5B1A3.coeff 209 =
      -((((763448485 * 10 ^ 70 +
        3086207580169140902575806387481179727443434073319832386993911194951860) * 10 ^ 70 +
        0403029516977474598080311938671728230743586505225714037206436177851154) * 10 ^ 70 +
        1290784094002481573710865460093776032063672840648463053756710745985018) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 45 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 9 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (210 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_210 :
    recurrence5B1A3.coeff 210 =
      ((((266381632 * 10 ^ 70 +
        2883601699803619232280385893110904424343187164137131736083369722858537) * 10 ^ 70 +
        8098114128377826264987808525925944697496316828082925251435867323558671) * 10 ^ 70 +
        8113547118028783060586430630659794177392201918234735600867210808077250) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 46 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 8 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (211 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_211 :
    recurrence5B1A3.coeff 211 =
      -((((83204665 * 10 ^ 70 +
        1718606093450564055588283071481128692328769085309022351459103220391020) * 10 ^ 70 +
        1517764067465709471356340651340817787307846982853555459305892280608938) * 10 ^ 70 +
        3518414088256057631299828967530141063624482427030208000813972028674328) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 47 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 7 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (212 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_212 :
    recurrence5B1A3.coeff 212 =
      ((((21730866 * 10 ^ 70 +
        9212884718067363178953977770008683935771164228571309176215820200983714) * 10 ^ 70 +
        7792103897002764463488975581515098349866644129708212597762750586605502) * 10 ^ 70 +
        1143151295615856166579896845372144042849678343300387133711178929717256) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 48 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 6 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (213 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_213 :
    recurrence5B1A3.coeff 213 =
      -((((3705583 * 10 ^ 70 +
        2783985133226448623810973801778259451462411594684398541066303228628749) * 10 ^ 70 +
        8686953999975839801623027734567091262337832716612217906205399264385090) * 10 ^ 70 +
        7449276995364027555979433556241350385058342637213582152088009045646793) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 49 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 5 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (214 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_214 :
    recurrence5B1A3.coeff 214 =
      -((((421235 * 10 ^ 70 +
        3903460176081791154604124754344037892331359721584313672093286909549665) * 10 ^ 70 +
        0632182762951011656806632710151250035285978996641248593009369120918687) * 10 ^ 70 +
        5315399510973165997742630496122375972900190811041493096151151709623909) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 50 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 4 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (215 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_215 :
    recurrence5B1A3.coeff 215 =
      ((((804500 * 10 ^ 70 +
        9054267417714945479659398415506508145253262055986134820165404566569026) * 10 ^ 70 +
        8195540981397872084381048793846561325717787355087667272315131625340543) * 10 ^ 70 +
        2978225367282056727121212470187079684058805016582800497782460923020796) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 51 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 3 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (216 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_216 :
    recurrence5B1A3.coeff 216 =
      -((((500391 * 10 ^ 70 +
        1417315261298425192553785875182464074384961866037431730035080119143047) * 10 ^ 70 +
        3746406204411280510118573328758001986681314964372017669803036561392785) * 10 ^ 70 +
        2452357915191370770370315949858418295134448069126264372072436918076121) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 52 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 2 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (217 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_217 :
    recurrence5B1A3.coeff 217 =
      ((((237142 * 10 ^ 70 +
        7135719865686587007320314450714139296646413577273072971759564641604467) * 10 ^ 70 +
        4115480429313470707998534123961826066678077159472197025002255236551206) * 10 ^ 70 +
        4889454087389417314501725750835269187966613456138538016248254445075939) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 53 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 1 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B1A3_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient1.coeff x * remainder5Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B1A3_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient1.coeff (150 + x) *
        remainder5Coefficient3.coeff (218 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5B1A3_coeff_218 :
    recurrence5B1A3.coeff 218 =
      -((((96974 * 10 ^ 70 +
        1987984446919245652789344979551161880668959896863176242109012358079752) * 10 ^ 70 +
        7122809058969689464147973479232192172109083057242984086151120232909337) * 10 ^ 70 +
        4643990619779582481603864028768459212604674215392200434298172040613601) : ℚ) := by
  unfold recurrence5B1A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 54 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5B1A3_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B1A3_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
