/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4SquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: A4Square coefficient convolution

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

private theorem recurrence4A4Square_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (196 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_196 :
    recurrence4A4Square.coeff 196 =
      (((127427118392381065839882942502466480902928369947614812521 * 10 ^ 70 +
        2525045415556483503440165459271310478864521136766148059755988597402841) * 10 ^ 70 +
        9985327621110617581311324948884611502340632170715492947642455215258325) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (196 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (197 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_197 :
    recurrence4A4Square.coeff 197 =
      -(((102592535404833112151688276304999575971011934128250194615 * 10 ^ 70 +
        6980643493219230456178813150841591836591013021986682418608629238495081) * 10 ^ 70 +
        9218508075084922943352625785658448232462475568690465232130015007472774) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (197 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (198 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_198 :
    recurrence4A4Square.coeff 198 =
      (((81129414085277207201028988260946296401492233132327530885 * 10 ^ 70 +
        1078904800542346886430369846904832920280036119803873953523983474818778) * 10 ^ 70 +
        9467940692156947978614397365074641762601940321118164817285484678148371) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (198 - x)) = _
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
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (199 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_199 :
    recurrence4A4Square.coeff 199 =
      -(((63013494108596073565776899025629335254722917631687407692 * 10 ^ 70 +
        0845175065262546844550611429259315733769189221582649618470053692114422) * 10 ^ 70 +
        7198765024080990449602820235423760093409228880333214649113776232041146) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (199 - x)) = _
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
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (200 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_200 :
    recurrence4A4Square.coeff 200 =
      (((48068950334476905191384537113348402133256915480667362455 * 10 ^ 70 +
        5444151627424178861576880004165486766861280428989611884721315136099516) * 10 ^ 70 +
        3385717429800055397868243836028985166158530449411624008579025175875980) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (200 - x)) = _
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
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (201 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_201 :
    recurrence4A4Square.coeff 201 =
      -(((36012561551805236600548148108189611122453257228700005083 * 10 ^ 70 +
        5693938968212015225651646296228725888941361787708449076639880209290048) * 10 ^ 70 +
        5252726426439809536446457263444762429549559277054193979421739169400704) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (201 - x)) = _
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
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (202 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_202 :
    recurrence4A4Square.coeff 202 =
      (((26496185958463573779905569020754419634294307955309527545 * 10 ^ 70 +
        5855086086492875453641366270022544273785889090247636645640473422874710) * 10 ^ 70 +
        5561614090556906450286813214936724965363941253255684044431636703494868) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (202 - x)) = _
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
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (203 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_203 :
    recurrence4A4Square.coeff 203 =
      -(((19144040059705333728485452663903582169458974156736493316 * 10 ^ 70 +
        8458314321074021489978833455535826920804889287321798556868735531739077) * 10 ^ 70 +
        8608033885100865747896538408359493215962733525712715492231818925036336) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (203 - x)) = _
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
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (204 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_204 :
    recurrence4A4Square.coeff 204 =
      (((13582660458167184482803590411430919284119998468196418364 * 10 ^ 70 +
        8198004884283256334352882746879601408420443820818665712271017112909344) * 10 ^ 70 +
        5963474725973716565159863142386940885978283988010059448595012953394438) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (204 - x)) = _
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
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (205 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_205 :
    recurrence4A4Square.coeff 205 =
      -(((9462730703731137754127840100113519611698308675726303114 * 10 ^ 70 +
        6387889143553735731400601293070638214788161559305188052231179204481268) * 10 ^ 70 +
        9028709583365712202382056818867469521989553786061643145935841798938136) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (205 - x)) = _
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
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (206 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_206 :
    recurrence4A4Square.coeff 206 =
      (((6473022365620740490254318320939731146410833105855250611 * 10 ^ 70 +
        4279500360995181172032432447846045877010117583133817282536276920187993) * 10 ^ 70 +
        8248608441691702804631000138258744008362794259941571316075465471596449) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (206 - x)) = _
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
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (207 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_207 :
    recurrence4A4Square.coeff 207 =
      -(((4347449753806361752010689588855252196257447609203421700 * 10 ^ 70 +
        7717394731910403500971533080953207209378199820054861410945949992658184) * 10 ^ 70 +
        6639158202685679092161201831511659694497866307324395231054985672536998) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (207 - x)) = _
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
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (208 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_208 :
    recurrence4A4Square.coeff 208 =
      (((2866658605224515369856653543771671471471783336477337948 * 10 ^ 70 +
        0635016525919137980213195554045269426571932309037986482318078843235327) * 10 ^ 70 +
        8361632020628334925136972081174136984382540594718955985291530151858513) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (208 - x)) = _
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
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (209 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_209 :
    recurrence4A4Square.coeff 209 =
      -(((1855699707196045286063010442444333693214423179250532999 * 10 ^ 70 +
        8292901910844455952974862918281945861833184856309874389133513491419345) * 10 ^ 70 +
        9205939998040725607675995455042560543540550692770543856143145054793180) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (209 - x)) = _
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
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (210 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_210 :
    recurrence4A4Square.coeff 210 =
      (((1179248760178926450798875731022362979052245898446067790 * 10 ^ 70 +
        9911929648889563074493524196474404911374628368772726427566452998669486) * 10 ^ 70 +
        9852040994003639503495152469162559977475329918129814051453435088021544) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (210 - x)) = _
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
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (211 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_211 :
    recurrence4A4Square.coeff 211 =
      -(((735604187053004512340435901195117717494977086241298009 * 10 ^ 70 +
        7401683216177114509750095822773533059233603101112406799065292110239850) * 10 ^ 70 +
        2826540141460840037615953299446168767208222761851851482578621373388644) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (211 - x)) = _
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
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (212 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_212 :
    recurrence4A4Square.coeff 212 =
      (((450400040136300826309160521923469593211558472577584070 * 10 ^ 70 +
        2051930018430684261907085130096312651873092556026490048762380579738644) * 10 ^ 70 +
        0654599245132779998507092215312684002621615448829107384526095738881235) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (212 - x)) = _
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
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (213 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_213 :
    recurrence4A4Square.coeff 213 =
      -(((270671175717443746072336484750044567380720928171180963 * 10 ^ 70 +
        0468597266612986213027248037043989867620064942390462098883184636891982) * 10 ^ 70 +
        1286744151662268279992957668900813150099767939640742342984444148396796) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (213 - x)) = _
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
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (214 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_214 :
    recurrence4A4Square.coeff 214 =
      (((159642461282754684879883767022115737944804460831916416 * 10 ^ 70 +
        7608720532190604865637322801650119821319554576423448922221628479255075) * 10 ^ 70 +
        3918980439273235065741788997452261580470836532114885311318462836497570) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (214 - x)) = _
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
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4A4Square_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (215 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_215 :
    recurrence4A4Square.coeff 215 =
      -(((92403998491850340090970333697297715317577459778934754 * 10 ^ 70 +
        3784293180952922783042307775278221618185188901649702842296816464395107) * 10 ^ 70 +
        8413668469958181877160443930082107427672819522653567725301334012348876) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (215 - x)) = _
  rw [show 216 = 37 +
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
  rw [recurrence4A4Square_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (216 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_216 :
    recurrence4A4Square.coeff 216 =
      (((52485821083020052899656749584683283422396683777882284 * 10 ^ 70 +
        1333006131220269825548200746774059591240638255145250539840696090199284) * 10 ^ 70 +
        1582707327746218519737370256563756241619320620312822998058592053999607) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (216 - x)) = _
  rw [show 217 = 38 +
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
  rw [recurrence4A4Square_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (217 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_217 :
    recurrence4A4Square.coeff 217 =
      -(((29253310714650046896634953636701788323309795934458929 * 10 ^ 70 +
        1135771744235423675965157680158947148913108098171772088271850180922739) * 10 ^ 70 +
        5945480791297925771682844346149732883771094412365956774516726738020950) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (217 - x)) = _
  rw [show 218 = 39 +
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
  rw [recurrence4A4Square_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (218 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_218 :
    recurrence4A4Square.coeff 218 =
      (((15997898512680883402591305114788000415854192083059761 * 10 ^ 70 +
        0195177051089515462202280556037680418378361377328524415342553609238374) * 10 ^ 70 +
        8164159332818843428165054534885809080638268291588808357195540868298550) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (218 - x)) = _
  rw [show 219 = 40 +
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
  rw [recurrence4A4Square_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (219 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_219 :
    recurrence4A4Square.coeff 219 =
      -(((8583792619237343730583067348609113878611103912040421 * 10 ^ 70 +
        5479625774138231589878861941200905213201627633915821313984844539671799) * 10 ^ 70 +
        9267345741054540617061320858354100467072997659446205824944969495796896) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (219 - x)) = _
  rw [show 220 = 41 +
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
  rw [recurrence4A4Square_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (220 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_220 :
    recurrence4A4Square.coeff 220 =
      (((4518538367919438756059288031304001532105093119995733 * 10 ^ 70 +
        2850429024651360562486354583694137581676873872487880670331989441062541) * 10 ^ 70 +
        3012743899885908797557561409375095840083849018214583107317337411395945) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (220 - x)) = _
  rw [show 221 = 42 +
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
  rw [recurrence4A4Square_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4A4Square_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4A4Square_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder4Coefficient4.coeff (179 + x) *
        remainder4Coefficient4.coeff (221 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (179 + x) (by
    omega)]
  norm_num

theorem recurrence4A4Square_coeff_221 :
    recurrence4A4Square.coeff 221 =
      -(((2333426858926108274126654916171416754239382641026936 * 10 ^ 70 +
        2901056149826979382694512123751182952007201716806848136229476256015520) * 10 ^ 70 +
        1309361448291461190543526772043600880516808853851340752365320968192068) : ℚ) := by
  unfold recurrence4A4Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder4Coefficient4.coeff x * remainder4Coefficient4.coeff (221 - x)) = _
  rw [show 222 = 43 +
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
  rw [recurrence4A4Square_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4A4Square_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
