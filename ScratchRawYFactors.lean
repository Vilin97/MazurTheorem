import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ScratchRawYFactors

private def A (r s : ℚ) : ℚ := r - s
private def B (_r s : ℚ) : ℚ := s - 1
private def C (r s : ℚ) : ℚ := r * s - 2 * r + 1
private def K (r s : ℚ) : ℚ := r - s ^ 2 + s - 1
private def D (r s : ℚ) : ℚ :=
  r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s
private def E (r s : ℚ) : ℚ :=
  r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1
private def G (r s : ℚ) : ℚ := r * s ^ 2 - 3 * r * s + r + s ^ 2
private def L (r s : ℚ) : ℚ :=
  r ^ 3 - r ^ 2 * s ^ 4 + 5 * r ^ 2 * s ^ 3 - 9 * r ^ 2 * s ^ 2 +
    4 * r ^ 2 * s - 2 * r ^ 2 - r * s ^ 3 + 6 * r * s ^ 2 -
    3 * r * s + r - s ^ 3
private def J (r s : ℚ) : ℚ :=
  r ^ 3 * s ^ 2 - 4 * r ^ 3 * s + 2 * r ^ 3 + 3 * r ^ 2 * s ^ 2 +
    2 * r ^ 2 * s - 2 * r ^ 2 - r * s ^ 5 + 4 * r * s ^ 4 -
    10 * r * s ^ 3 + 6 * r * s ^ 2 - 3 * r * s + r + s ^ 4
private def T (r s : ℚ) : ℚ :=
  r ^ 2 * s ^ 3 - 5 * r ^ 2 * s ^ 2 + 6 * r ^ 2 * s - r ^ 2 +
    r * s ^ 4 - 3 * r * s ^ 3 + 6 * r * s ^ 2 - 7 * r * s + r + s
private def M (r s : ℚ) : ℚ :=
  r ^ 4 * s ^ 3 - 6 * r ^ 4 * s ^ 2 + 9 * r ^ 4 * s - r ^ 4 +
    r ^ 3 * s ^ 5 - 7 * r ^ 3 * s ^ 4 + 20 * r ^ 3 * s ^ 3 -
    19 * r ^ 3 * s ^ 2 - 8 * r ^ 3 * s + r ^ 3 + r ^ 2 * s ^ 4 -
    11 * r ^ 2 * s ^ 3 + 28 * r ^ 2 * s ^ 2 + r * s ^ 4 -
    5 * r * s ^ 3 - 8 * r * s ^ 2 + s ^ 4 + s ^ 3 + s ^ 2
private def N (r s : ℚ) : ℚ :=
  r * A r s * K r s ^ 3 - s * C r s ^ 3 * G r s
private def P6 (r s : ℚ) : ℚ :=
  D r s ^ 2 * A r s * K r s - C r s ^ 2 * s * B r s * G r s * E r s
private def P9 (r s : ℚ) : ℚ :=
  D r s ^ 3 * L r s - r * s * B r s ^ 3 * G r s * E r s ^ 3

private def x2 (r s : ℚ) : ℚ := r * s * (r - 1)
private def x3 (r s : ℚ) : ℚ := s * (r - 1)
private def x4 (r _s : ℚ) : ℚ := r * (r - 1)
private def x6 (r s : ℚ) : ℚ := s * (r - 1) * A r s / B r s ^ 2
private def x7 (r s : ℚ) : ℚ :=
  r * s * (r - 1) * B r s * C r s / A r s ^ 2
private def x8 (r s : ℚ) : ℚ :=
  r * (r - 1) * A r s * K r s / C r s ^ 2
private def x9 (r s : ℚ) : ℚ :=
  s * (r - 1) * C r s * G r s / K r s ^ 2
private def x11 (r s : ℚ) : ℚ :=
  r * s * (r - 1) * B r s * G r s * E r s / D r s ^ 2
private def x12 (r s : ℚ) : ℚ :=
  (r - 1) * D r s * L r s / (B r s ^ 2 * E r s ^ 2)

private def rawY1 (r s : ℚ) : ℚ :=
  ((x7 r s - x9 r s) / (x7 r s - x4 r s)) *
    ((0 - x12 r s) / (0 - x3 r s))
private def rawY2 (r s : ℚ) : ℚ :=
  (x2 r s / (x2 r s - x6 r s)) *
    ((x11 r s - x7 r s) / (x11 r s - x8 r s))
private def rawY4 (r s : ℚ) : ℚ :=
  ((x4 r s - x2 r s) / (x4 r s - x12 r s)) *
    ((x3 r s - x11 r s) / (x3 r s - x9 r s))
private def rawY8 (r s : ℚ) : ℚ :=
  ((x8 r s - x4 r s) / x8 r s) *
    ((x6 r s - x3 r s) / (x6 r s - x7 r s))
private def rawY9 (r s : ℚ) : ℚ :=
  ((x9 r s - x8 r s) / (x9 r s - x2 r s)) *
    ((x12 r s - x6 r s) / (x12 r s - x11 r s))

private def y1 (r s : ℚ) : ℚ :=
  C r s * L r s * J r s / (r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2)
private def y2 (r s : ℚ) : ℚ :=
  -(r * B r s ^ 3 * C r s * K r s * M r s) / (A r s ^ 2 * P6 r s)
private def y4 (r s : ℚ) : ℚ :=
  -(r * A r s * B r s * K r s ^ 2 * E r s * T r s) /
    (C r s * D r s ^ 2 * J r s)
private def y8 (r s : ℚ) : ℚ := -(A r s * B r s * E r s) / L r s
private def y9 (r s : ℚ) : ℚ :=
  -(K r s * D r s * M r s * N r s) / (s * A r s * C r s ^ 2 * P9 r s)

private theorem x7_sub_x9 (r s : ℚ) (hA : A r s ≠ 0) (hK : K r s ≠ 0) :
    x7 r s - x9 r s =
      -(s * (r - 1) * C r s * J r s) / (A r s ^ 2 * K r s ^ 2) := by
  simp only [x7, x9]
  field_simp [hA, hK]
  simp only [A, B, C, K, G, J]
  ring

private theorem x7_sub_x4 (r s : ℚ) (hA : A r s ≠ 0) :
    x7 r s - x4 r s = -(r * (r - 1) * D r s) / A r s ^ 2 := by
  simp only [x7, x4]
  field_simp [hA]
  simp only [A, B, C, D]
  ring

private theorem zero_sub_x12 (r s : ℚ) :
    0 - x12 r s = -(r - 1) * D r s * L r s / (B r s ^ 2 * E r s ^ 2) := by
  simp only [x12]
  ring

private theorem zero_sub_x3 (r s : ℚ) : 0 - x3 r s = -(s * (r - 1)) := by
  simp only [x3]
  ring

private theorem x2_eq (r s : ℚ) : x2 r s = r * s * (r - 1) := by
  simp only [x2]

private theorem x2_sub_x6 (r s : ℚ) (hB : B r s ≠ 0) :
    x2 r s - x6 r s = s ^ 2 * (r - 1) * C r s / B r s ^ 2 := by
  simp only [x2, x6]
  field_simp [hB]
  simp only [A, B, C]
  ring

private theorem x11_sub_x7 (r s : ℚ) (hA : A r s ≠ 0) (hD : D r s ≠ 0) :
    x11 r s - x7 r s =
      r * s * (r - 1) * B r s * K r s * M r s / (A r s ^ 2 * D r s ^ 2) := by
  simp only [x11, x7]
  field_simp [hA, hD]
  simp only [A, B, C, K, D, E, G, M]
  ring

private theorem x11_sub_x8 (r s : ℚ) (hC : C r s ≠ 0) (hD : D r s ≠ 0) :
    x11 r s - x8 r s = -(r * (r - 1) * P6 r s) / (C r s ^ 2 * D r s ^ 2) := by
  simp only [x11, x8]
  field_simp [hC, hD]
  simp only [A, B, C, K, D, E, G, P6]
  ring

private theorem x4_sub_x2 (r s : ℚ) :
    x4 r s - x2 r s = -(r * (r - 1) * B r s) := by
  simp only [x4, x2, B]
  ring

private theorem x4_sub_x12 (r s : ℚ) (hB : B r s ≠ 0) (hE : E r s ≠ 0) :
    x4 r s - x12 r s =
      (r - 1) * C r s ^ 2 * J r s / (B r s ^ 2 * E r s ^ 2) := by
  simp only [x4, x12]
  field_simp [hB, hE]
  simp only [B, C, D, E, L, J]
  ring

private theorem x3_sub_x11 (r s : ℚ) (hD : D r s ≠ 0) :
    x3 r s - x11 r s =
      -(s * (r - 1) * A r s * C r s * T r s) / D r s ^ 2 := by
  simp only [x3, x11]
  field_simp [hD]
  simp only [A, B, C, D, E, G, T]
  ring

private theorem x3_sub_x9 (r s : ℚ) (hK : K r s ≠ 0) :
    x3 r s - x9 r s = -(s * (r - 1) * B r s ^ 2 * E r s) / K r s ^ 2 := by
  simp only [x3, x9]
  field_simp [hK]
  simp only [B, C, K, E, G]
  ring

private theorem x8_sub_x4 (r s : ℚ) (hC : C r s ≠ 0) :
    x8 r s - x4 r s = -(r * (r - 1) * B r s * E r s) / C r s ^ 2 := by
  simp only [x8, x4]
  field_simp [hC]
  simp only [A, B, C, K, E]
  ring

private theorem x8_eq (r s : ℚ) :
    x8 r s = r * (r - 1) * A r s * K r s / C r s ^ 2 := by
  simp only [x8]

private theorem x6_sub_x3 (r s : ℚ) (hB : B r s ≠ 0) :
    x6 r s - x3 r s = s * (r - 1) * K r s / B r s ^ 2 := by
  simp only [x6, x3]
  field_simp [hB]
  simp only [A, B, K]
  ring

private theorem x6_sub_x7 (r s : ℚ) (hA : A r s ≠ 0) (hB : B r s ≠ 0) :
    x6 r s - x7 r s = s * (r - 1) * L r s / (A r s ^ 2 * B r s ^ 2) := by
  simp only [x6, x7]
  field_simp [hA, hB]
  simp only [A, B, C, L]
  ring

private theorem x9_sub_x8 (r s : ℚ) (hC : C r s ≠ 0) (hK : K r s ≠ 0) :
    x9 r s - x8 r s = -(r - 1) * N r s / (C r s ^ 2 * K r s ^ 2) := by
  simp only [x9, x8]
  field_simp [hC, hK]
  simp only [A, C, K, G, N]
  ring

private theorem x9_sub_x2 (r s : ℚ) (hK : K r s ≠ 0) :
    x9 r s - x2 r s = -(s * (r - 1) * A r s * D r s) / K r s ^ 2 := by
  simp only [x9, x2]
  field_simp [hK]
  simp only [A, C, K, D, G]
  ring

private theorem x12_sub_x6 (r s : ℚ) (hB : B r s ≠ 0) (hE : E r s ≠ 0) :
    x12 r s - x6 r s =
      -(r - 1) * K r s * M r s / (B r s ^ 2 * E r s ^ 2) := by
  simp only [x12, x6]
  field_simp [hB, hE]
  simp only [A, K, D, E, L, M]
  ring

private theorem x12_sub_x11 (r s : ℚ)
    (hB : B r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0) :
    x12 r s - x11 r s =
      (r - 1) * P9 r s / (B r s ^ 2 * D r s ^ 2 * E r s ^ 2) := by
  simp only [x12, x11]
  field_simp [hB, hD, hE]
  simp only [B, D, E, G, L, P9]
  ring

theorem rawY1_eq (r s : ℚ)
    (hr : r ≠ 0) (hA : A r s ≠ 0) (hB : B r s ≠ 0)
    (hK : K r s ≠ 0) (hE : E r s ≠ 0)
    (h74 : x7 r s - x4 r s ≠ 0) (h03 : 0 - x3 r s ≠ 0) :
    rawY1 r s = y1 r s := by
  have h74' : -(r * (r - 1) * D r s) / A r s ^ 2 ≠ 0 := by
    rw [← x7_sub_x4 r s hA]
    exact h74
  have h03' : -(s * (r - 1)) ≠ 0 := by
    rw [← zero_sub_x3 r s]
    exact h03
  have hs : s ≠ 0 := by
    intro hs
    apply h03'
    simp [hs]
  have hR : r - 1 ≠ 0 := by
    intro hR
    apply h03'
    simp [hR]
  have hD : D r s ≠ 0 := by
    intro hD
    apply h74'
    simp [hD]
  unfold rawY1 y1
  rw [x7_sub_x9 r s hA hK, x7_sub_x4 r s hA,
    zero_sub_x12 r s, zero_sub_x3 r s]
  field_simp [hr, hs, hR, hA, hB, hK, hD, hE]

theorem rawY2_eq (r s : ℚ)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hP6 : P6 r s ≠ 0)
    (h26 : x2 r s - x6 r s ≠ 0) (h118 : x11 r s - x8 r s ≠ 0) :
    rawY2 r s = y2 r s := by
  have h26' : s ^ 2 * (r - 1) * C r s / B r s ^ 2 ≠ 0 := by
    rw [← x2_sub_x6 r s hB]
    exact h26
  have h118' : -(r * (r - 1) * P6 r s) / (C r s ^ 2 * D r s ^ 2) ≠ 0 := by
    rw [← x11_sub_x8 r s hC hD]
    exact h118
  have hs : s ≠ 0 := by
    intro hs
    apply h26'
    simp [hs]
  have hR : r - 1 ≠ 0 := by
    intro hR
    apply h26'
    simp [hR]
  have hr : r ≠ 0 := by
    intro hr
    apply h118'
    simp [hr]
  unfold rawY2 y2
  rw [x2_sub_x6 r s hB, x11_sub_x7 r s hA hD,
    x11_sub_x8 r s hC hD, x2_eq]
  field_simp [hr, hs, hR, hA, hB, hC, hD, hP6]

theorem rawY4_eq (r s : ℚ)
    (hB : B r s ≠ 0) (hC : C r s ≠ 0) (hK : K r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hJ : J r s ≠ 0)
    (h412 : x4 r s - x12 r s ≠ 0) (h39 : x3 r s - x9 r s ≠ 0) :
    rawY4 r s = y4 r s := by
  have h412' : (r - 1) * C r s ^ 2 * J r s / (B r s ^ 2 * E r s ^ 2) ≠ 0 := by
    rw [← x4_sub_x12 r s hB hE]
    exact h412
  have h39' : -(s * (r - 1) * B r s ^ 2 * E r s) / K r s ^ 2 ≠ 0 := by
    rw [← x3_sub_x9 r s hK]
    exact h39
  have hs : s ≠ 0 := by
    intro hs
    apply h39'
    simp [hs]
  have hR : r - 1 ≠ 0 := by
    intro hR
    apply h412'
    simp [hR]
  unfold rawY4 y4
  rw [x4_sub_x2, x4_sub_x12 r s hB hE, x3_sub_x11 r s hD,
    x3_sub_x9 r s hK]
  field_simp [hs, hR, hB, hC, hK, hD, hE, hJ]

theorem rawY8_eq (r s : ℚ)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hL : L r s ≠ 0)
    (h8 : x8 r s ≠ 0) (h67 : x6 r s - x7 r s ≠ 0) :
    rawY8 r s = y8 r s := by
  have h8' : r * (r - 1) * A r s * K r s / C r s ^ 2 ≠ 0 := by
    rw [← x8_eq r s]
    exact h8
  have h67' : s * (r - 1) * L r s / (A r s ^ 2 * B r s ^ 2) ≠ 0 := by
    rw [← x6_sub_x7 r s hA hB]
    exact h67
  have hr : r ≠ 0 := by
    intro hr
    apply h8'
    simp [hr]
  have hs : s ≠ 0 := by
    intro hs
    apply h67'
    simp [hs]
  have hR : r - 1 ≠ 0 := by
    intro hR
    apply h8'
    simp [hR]
  have hK : K r s ≠ 0 := by
    intro hK
    apply h8'
    simp [hK]
  unfold rawY8 y8
  rw [x8_sub_x4 r s hC, x8_eq, x6_sub_x3 r s hB,
    x6_sub_x7 r s hA hB]
  field_simp [hr, hs, hR, hA, hB, hC, hK, hL]

theorem rawY9_eq (r s : ℚ)
    (hs : s ≠ 0) (hA : A r s ≠ 0) (hB : B r s ≠ 0)
    (hC : C r s ≠ 0) (hK : K r s ≠ 0) (hD : D r s ≠ 0)
    (hE : E r s ≠ 0) (hP9 : P9 r s ≠ 0)
    (h92 : x9 r s - x2 r s ≠ 0) (h1211 : x12 r s - x11 r s ≠ 0) :
    rawY9 r s = y9 r s := by
  have h92' : -(s * (r - 1) * A r s * D r s) / K r s ^ 2 ≠ 0 := by
    rw [← x9_sub_x2 r s hK]
    exact h92
  have h1211' :
      (r - 1) * P9 r s / (B r s ^ 2 * D r s ^ 2 * E r s ^ 2) ≠ 0 := by
    rw [← x12_sub_x11 r s hB hD hE]
    exact h1211
  have hR : r - 1 ≠ 0 := by
    intro hR
    apply h92'
    simp [hR]
  unfold rawY9 y9
  rw [x9_sub_x8 r s hC hK, x9_sub_x2 r s hK,
    x12_sub_x6 r s hB hE, x12_sub_x11 r s hB hD hE]
  field_simp [hs, hR, hA, hB, hC, hK, hD, hE, hP9]

end ScratchRawYFactors
