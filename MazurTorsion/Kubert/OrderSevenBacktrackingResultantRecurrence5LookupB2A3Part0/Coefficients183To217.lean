/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B2_coeff_0
  recurrence5B2_coeff_1
  recurrence5B2_coeff_2
  recurrence5B2_coeff_3
  recurrence5B2_coeff_4
  recurrence5B2_coeff_5
  recurrence5B2_coeff_6
  recurrence5B2_coeff_7
  recurrence5B2_coeff_8
  recurrence5B2_coeff_9
  recurrence5B2_coeff_10
  recurrence5B2_coeff_11
  recurrence5B2_coeff_12
  recurrence5B2_coeff_13
  recurrence5B2_coeff_14
  recurrence5B2_coeff_15
  recurrence5B2_coeff_16
  recurrence5B2_coeff_17
  recurrence5B2_coeff_18
  recurrence5B2_coeff_19
  recurrence5B2_coeff_20
  recurrence5B2_coeff_21
  recurrence5B2_coeff_22
  recurrence5B2_coeff_23
  recurrence5B2_coeff_24
  recurrence5B2_coeff_25
  recurrence5B2_coeff_26
  recurrence5B2_coeff_27
  recurrence5B2_coeff_28
  recurrence5B2_coeff_29
  recurrence5B2_coeff_30
  recurrence5B2_coeff_31
  recurrence5B2_coeff_32
  recurrence5B2_coeff_33
  recurrence5B2_coeff_34
  recurrence5B2_coeff_35
  recurrence5B2_coeff_36
  recurrence5B2_coeff_37
  recurrence5B2_coeff_38
  recurrence5B2_coeff_39
  recurrence5B2_coeff_40
  recurrence5B2_coeff_41
  recurrence5B2_coeff_42
  recurrence5B2_coeff_43
  recurrence5B2_coeff_44
  recurrence5B2_coeff_45
  recurrence5B2_coeff_46
  recurrence5B2_coeff_47
  recurrence5B2_coeff_48
  recurrence5B2_coeff_49
  recurrence5B2_coeff_50
  recurrence5B2_coeff_51
  recurrence5B2_coeff_52
  recurrence5B2_coeff_53
  recurrence5B2_coeff_54
  recurrence5B2_coeff_55
  recurrence5B2_coeff_56
  recurrence5B2_coeff_57
  recurrence5B2_coeff_58
  recurrence5B2_coeff_59
  recurrence5B2_coeff_60
  recurrence5B2_coeff_61
  recurrence5B2_coeff_62
  recurrence5B2_coeff_63

attribute [local simp]
  recurrence5B2_coeff_64
  recurrence5B2_coeff_65
  recurrence5B2_coeff_66
  recurrence5B2_coeff_67
  recurrence5B2_coeff_68
  recurrence5B2_coeff_69
  recurrence5B2_coeff_70
  recurrence5B2_coeff_71
  recurrence5B2_coeff_72
  recurrence5B2_coeff_73
  recurrence5B2_coeff_74
  recurrence5B2_coeff_75
  recurrence5B2_coeff_76
  recurrence5B2_coeff_77
  recurrence5B2_coeff_78
  recurrence5B2_coeff_79
  recurrence5B2_coeff_80
  recurrence5B2_coeff_81
  recurrence5B2_coeff_82
  recurrence5B2_coeff_83
  recurrence5B2_coeff_84
  recurrence5B2_coeff_85
  recurrence5B2_coeff_86
  recurrence5B2_coeff_87
  recurrence5B2_coeff_88
  recurrence5B2_coeff_89
  recurrence5B2_coeff_90
  recurrence5B2_coeff_91
  recurrence5B2_coeff_92
  recurrence5B2_coeff_93
  recurrence5B2_coeff_94
  recurrence5B2_coeff_95
  recurrence5B2_coeff_96
  recurrence5B2_coeff_97
  recurrence5B2_coeff_98
  recurrence5B2_coeff_99
  recurrence5B2_coeff_100
  recurrence5B2_coeff_101
  recurrence5B2_coeff_102
  recurrence5B2_coeff_103
  recurrence5B2_coeff_104
  recurrence5B2_coeff_105
  recurrence5B2_coeff_106
  recurrence5B2_coeff_107
  recurrence5B2_coeff_108
  recurrence5B2_coeff_109
  recurrence5B2_coeff_110
  recurrence5B2_coeff_111
  recurrence5B2_coeff_112
  recurrence5B2_coeff_113
  recurrence5B2_coeff_114
  recurrence5B2_coeff_115
  recurrence5B2_coeff_116
  recurrence5B2_coeff_117
  recurrence5B2_coeff_118
  recurrence5B2_coeff_119
  recurrence5B2_coeff_120
  recurrence5B2_coeff_121
  recurrence5B2_coeff_122
  recurrence5B2_coeff_123
  recurrence5B2_coeff_124
  recurrence5B2_coeff_125
  recurrence5B2_coeff_126
  recurrence5B2_coeff_127

attribute [local simp]
  recurrence5B2_coeff_128
  recurrence5B2_coeff_129
  recurrence5B2_coeff_130
  recurrence5B2_coeff_131
  recurrence5B2_coeff_132
  recurrence5B2_coeff_133
  recurrence5B2_coeff_134
  recurrence5B2_coeff_135
  recurrence5B2_coeff_136
  recurrence5B2_coeff_137
  recurrence5B2_coeff_138
  recurrence5B2_coeff_139
  recurrence5B2_coeff_140
  recurrence5B2_coeff_141
  recurrence5B2_coeff_142
  recurrence5B2_coeff_143
  recurrence5B2_coeff_144
  recurrence5B2_coeff_145
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
  recurrence5A3_coeff_42
  recurrence5A3_coeff_43
  recurrence5A3_coeff_44
  recurrence5A3_coeff_45

attribute [local simp]
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
  recurrence5A3_coeff_106
  recurrence5A3_coeff_107
  recurrence5A3_coeff_108
  recurrence5A3_coeff_109

attribute [local simp]
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

private theorem recurrence5B2A3_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (183 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_183 :
    recurrence5B2A3.coeff 183 =
      ((((352382914316756 * 10 ^ 70 +
        3106620601373648582056319184045735706894697796334385558924104842885649) * 10 ^ 70 +
        5816551977432280702509403094929565729093663377862418109204820111968631) * 10 ^ 70 +
        4176413435967663861397936819748140951606256426926068618828406084644472) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 19 +
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
  rw [recurrence5B2A3_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (184 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_184 :
    recurrence5B2A3.coeff 184 =
      -((((208084786633657 * 10 ^ 70 +
        4259707813135106901587758027756676093703084081615531687088374922480671) * 10 ^ 70 +
        4933968142979061432206904716657867142669796555364968241689550493351144) * 10 ^ 70 +
        1100194931656596142080724680886447276173058246727832415068237550375410) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 30 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (185 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_185 :
    recurrence5B2A3.coeff 185 =
      ((((115245238534358 * 10 ^ 70 +
        2916853538500727252279382743964083076178241870300013639110010579860846) * 10 ^ 70 +
        1530942092169338702952386424081532692299415792940370018323032966455908) * 10 ^ 70 +
        4685001977229890997816603122055160331743237229620220467976006266308174) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 29 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (186 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_186 :
    recurrence5B2A3.coeff 186 =
      -((((59509068720985 * 10 ^ 70 +
        6487549448428391460378161674886199236151323415658705760665528626093926) * 10 ^ 70 +
        3464669180982536835873937381267315928259206997565842478941074071956109) * 10 ^ 70 +
        4336559784672732381689172319466850712574539089720222647578098768999050) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 28 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (187 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_187 :
    recurrence5B2A3.coeff 187 =
      ((((28226426042342 * 10 ^ 70 +
        5869179443661848573755372548601939779819151544216997940098678407802356) * 10 ^ 70 +
        2383078414116010728829126866725007532620740749093572902030816007232982) * 10 ^ 70 +
        8623215895216636834168704349290202153130852133216122537943390734827860) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (188 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_188 :
    recurrence5B2A3.coeff 188 =
      -((((11875026520815 * 10 ^ 70 +
        1360188031497922287397615722232991211272513013007608211991526178273777) * 10 ^ 70 +
        8861179274758561386342123086035285703713189211814702911190215397970297) * 10 ^ 70 +
        1596350281992745606129421693705757731809129850418290199379578030696172) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (189 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_189 :
    recurrence5B2A3.coeff 189 =
      ((((4012764492363 * 10 ^ 70 +
        0377430900950862728834502284605279396705546973687948504916936943523187) * 10 ^ 70 +
        3141838044715843148733058852698701120574778764349126742476171922158863) * 10 ^ 70 +
        4221460128804175163184934220075247494567333515652393616455248082608749) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 25 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (190 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_190 :
    recurrence5B2A3.coeff 190 =
      -((((637740799541 * 10 ^ 70 +
        6829337798901231008055332391320472231408112321712985598376510873353945) * 10 ^ 70 +
        2449139227409918442716354397375834803800662191599150350985647950439319) * 10 ^ 70 +
        7177534473350100227065471518569895785110400214695636158511299106677571) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 24 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (191 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_191 :
    recurrence5B2A3.coeff 191 =
      -((((553562745379 * 10 ^ 70 +
        0224834889361838679011531114772306170240597166740707499991560907037237) * 10 ^ 70 +
        3943975931900459621879894308877305395836852752017157365722489938853346) * 10 ^ 70 +
        1599962829393173744170093031788043248484481306703204984487466732250014) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (192 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_192 :
    recurrence5B2A3.coeff 192 =
      ((((791147051783 * 10 ^ 70 +
        2614130065297292968203636780930294886809727383963883715193752936368252) * 10 ^ 70 +
        6851084196852072087469976550556441025761602545597603666380434314024117) * 10 ^ 70 +
        8005314797131524400097646768616310456453090082880479198941429330579330) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (193 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_193 :
    recurrence5B2A3.coeff 193 =
      -((((679907189728 * 10 ^ 70 +
        0540970921001196055619278038513352406153192163910092774251828403601530) * 10 ^ 70 +
        3846631964686254119887000087656320421181495985477465649476954782300473) * 10 ^ 70 +
        1050500036095072821743301453523146400804949697017956052265001221130277) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 21 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (194 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_194 :
    recurrence5B2A3.coeff 194 =
      ((((487965919058 * 10 ^ 70 +
        1109305376975709931795501639046729146181611178269447490797363442852194) * 10 ^ 70 +
        5995185731389675032312386232722538713906437564304327531124747856413884) * 10 ^ 70 +
        6962259221012392555341984260368734241549114933016556062166833578066670) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 20 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (195 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_195 :
    recurrence5B2A3.coeff 195 =
      -((((316334678791 * 10 ^ 70 +
        5631056189221049116183091294457188654763183828148852256737357442178458) * 10 ^ 70 +
        4419644912644108694759949802842893140786837237934523811679066669045330) * 10 ^ 70 +
        4692597031485957068773364072184164669424202373202983103560196685390958) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (196 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_196 :
    recurrence5B2A3.coeff 196 =
      ((((191004179411 * 10 ^ 70 +
        0384231703470269965223739389725277060290520616174273798129853473018883) * 10 ^ 70 +
        5712037787362068054622811035132391650702801602968925833193088068069622) * 10 ^ 70 +
        1309804990076878389439409163530419603851373329955841934539734115923686) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 18 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (197 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_197 :
    recurrence5B2A3.coeff 197 =
      -((((108981784147 * 10 ^ 70 +
        8928654090943987705025682533593087717076242567929845141407487420083327) * 10 ^ 70 +
        7898180848202491891789784612173053343055624470677168962264224057982300) * 10 ^ 70 +
        0664161491024038366065400976194701299008391472240593698533047366367442) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 17 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (198 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_198 :
    recurrence5B2A3.coeff 198 =
      ((((59186381141 * 10 ^ 70 +
        3059510932837058656265463850347801081333181208969978847233402859080165) * 10 ^ 70 +
        8730522442371465483789390094891990215687603166332371927771251677519349) * 10 ^ 70 +
        3454791079584344410806748685230037875786002055631059846384217309339870) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (199 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_199 :
    recurrence5B2A3.coeff 199 =
      -((((30700349678 * 10 ^ 70 +
        6240082259299287476597035219522053147788877976337676117583795441106232) * 10 ^ 70 +
        0810956993985941530340328562951877175705001480320485742963611198692779) * 10 ^ 70 +
        2523139526717817436739948922494207631268829566334102151781496259845944) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (200 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_200 :
    recurrence5B2A3.coeff 200 =
      ((((15228480955 * 10 ^ 70 +
        3762539379204706327467904055605776383078986479790941976223585914045211) * 10 ^ 70 +
        4103482237028659183293245831190906276827002931817231001156449845147930) * 10 ^ 70 +
        9640766819751873013519797343661933175373303399246678819332609726115262) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 14 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (201 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_201 :
    recurrence5B2A3.coeff 201 =
      -((((7223001046 * 10 ^ 70 +
        7767404090394287630905603426214570721133901714678625938294476786311159) * 10 ^ 70 +
        3331111897050182560829960254365480578460494348826772091586731377981378) * 10 ^ 70 +
        7985428895537705892887307152018985255883066461760362974085781883948190) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 13 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (202 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_202 :
    recurrence5B2A3.coeff 202 =
      ((((3273192663 * 10 ^ 70 +
        6693181415517279169060815810370644662139048406985032928403001550491130) * 10 ^ 70 +
        8369769335788572192181469499656657724846940084677475043455599799607890) * 10 ^ 70 +
        4886251051686034241672677497451159046786861453190755244909915543583070) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 12 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (203 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_203 :
    recurrence5B2A3.coeff 203 =
      -((((1415976056 * 10 ^ 70 +
        3596193485812195796989242817991533369681595605644689051041535875520042) * 10 ^ 70 +
        8075598903560876667466849186271569718633689695488763692472028751086044) * 10 ^ 70 +
        9752409758998293821844978403143553011013880435298677266738597249968317) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 11 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (204 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_204 :
    recurrence5B2A3.coeff 204 =
      ((((584949954 * 10 ^ 70 +
        8998598442698872612662394309303487555058133519335397325275973199252544) * 10 ^ 70 +
        8155113466008229339480436138811174209018105526239486611000324012206463) * 10 ^ 70 +
        5617625777146945952254776252998617003901443011826631072816097595133108) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 10 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (205 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_205 :
    recurrence5B2A3.coeff 205 =
      -((((231671320 * 10 ^ 70 +
        7430589634659818635101964262398158825311442363882586991124962053510498) * 10 ^ 70 +
        6744647959781755533930982112846220996006438461726688404814085869796010) * 10 ^ 70 +
        7185221055008654707760862940948146814984575589573055228257660201714326) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 9 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (206 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_206 :
    recurrence5B2A3.coeff 206 =
      ((((89064932 * 10 ^ 70 +
        6196776714131466090016869479495838085831466122299628508659612991390329) * 10 ^ 70 +
        7547357581053795778981422791067990707519610453232150218039590137943825) * 10 ^ 70 +
        9964534410959329274987815684055004397332680212882339460794893495493575) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 8 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (207 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_207 :
    recurrence5B2A3.coeff 207 =
      -((((34209280 * 10 ^ 70 +
        1221770088766626440887686728469665080450931069360758176538169870109358) * 10 ^ 70 +
        7504779399429640522150884908019458594496472321587737344181884040037089) * 10 ^ 70 +
        4492662972987118044588946562614080986621948260965031399709413986696916) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 7 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (208 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_208 :
    recurrence5B2A3.coeff 208 =
      ((((13812153 * 10 ^ 70 +
        3744063093435506570632420583117931533614298169902042156109049681662335) * 10 ^ 70 +
        0155255044648451325094645690026228748779993630027201536784496106764875) * 10 ^ 70 +
        9709373438082877059762337442998982445923040727177217319654653608362568) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 6 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (209 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_209 :
    recurrence5B2A3.coeff 209 =
      -((((6204201 * 10 ^ 70 +
        1031196967946206277302966929713269342520781038107705254914321251451857) * 10 ^ 70 +
        1933271522863414292290852658479150097163687939603425487626231688550739) * 10 ^ 70 +
        3972604820159112800121525000335913905781766471379066650983577734244600) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 5 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (210 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_210 :
    recurrence5B2A3.coeff 210 =
      ((((3155854 * 10 ^ 70 +
        0143775695949349263134505994185985735809903745572906961210453875212874) * 10 ^ 70 +
        7069945440020243303570349353050017185114705841512871280219000750178832) * 10 ^ 70 +
        7261955632183353065030477954753658604388499673083568453541587653114657) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 4 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (211 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_211 :
    recurrence5B2A3.coeff 211 =
      -((((1747244 * 10 ^ 70 +
        6604792074604942990573296254067081806474718131921922184472786305371167) * 10 ^ 70 +
        6231418425670038411497811415986801337322646303659300374838908426610233) * 10 ^ 70 +
        3523790488155184757938860601819947966376283661633860296277210770838730) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 3 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (212 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_212 :
    recurrence5B2A3.coeff 212 =
      ((((993351 * 10 ^ 70 +
        3946839383434243221338638972341676530757970481578678319460788909343659) * 10 ^ 70 +
        0088729787418643478852082688381514973404429421125179622637907854862626) * 10 ^ 70 +
        4269712500069810794952489523805305607415848631528705805525712045709437) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 2 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (213 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_213 :
    recurrence5B2A3.coeff 213 =
      -((((556442 * 10 ^ 70 +
        3163051700850701796681576669069334507688303584340600953737772380942451) * 10 ^ 70 +
        0892915176593928555277795403985470687702784775536261627587406581067392) * 10 ^ 70 +
        6952273621517187217560628396777978879084116803483246748267971723027064) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 69 = 1 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (214 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_214 :
    recurrence5B2A3.coeff 214 =
      ((((300906 * 10 ^ 70 +
        3174901380127088969569000581074614280756289789191058032863202283602536) * 10 ^ 70 +
        5731061802906432264557300351485393257656086050038931080610814839837382) * 10 ^ 70 +
        2219464342585982712387756918155028677897990967506483272586796673966607) : ℚ) := by
  unfold recurrence5B2A3
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
  rw [recurrence5B2A3_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (215 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_215 :
    recurrence5B2A3.coeff 215 =
      -((((155894 * 10 ^ 70 +
        8907009656679085608086838223970877966952468679472345746076778083914631) * 10 ^ 70 +
        3809388396013125537776987996605691235506266438985661691955841223180769) * 10 ^ 70 +
        6453287495727374737058160968484301557361824617143917726766042912405678) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 101 = 31 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (216 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_216 :
    recurrence5B2A3.coeff 216 =
      ((((77262 * 10 ^ 70 +
        9601544337318447748566123922125662583393772523120514705331437939944674) * 10 ^ 70 +
        4773343444367142708463126145017642510812177779452585137688421312041120) * 10 ^ 70 +
        0164443704340924315427292495750596621337162133555472127011263032717329) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 101 = 30 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (217 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_217 :
    recurrence5B2A3.coeff 217 =
      -((((36667 * 10 ^ 70 +
        6121344507718293062894073448914756448777551401784330587430342360471543) * 10 ^ 70 +
        1080684356790561157528417933985036705313390996954296575029191235981090) * 10 ^ 70 +
        8491637660691037799403738615710162817622475601925667027498415609811366) : ℚ) := by
  unfold recurrence5B2A3
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
    rw [show 101 = 29 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
