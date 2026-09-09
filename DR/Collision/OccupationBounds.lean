import DR.Collision.Occupation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Cast

/-!
# Centered occupation bounds

These estimates continue the exact conditional occupation identities. They
complete the square in the constant-vector direction and retain the norm of
the centered first-moment vector. Every probability quantity remains the
finite conditional iid quantity defined in `Occupation`.
-/

namespace DittertRybin

open scoped BigOperators

noncomputable def centeredOccupation {m n : ℕ} (P : Board m n) (k : ℕ) (i : Fin m) : ℝ :=
  occupationProbability P k i - (k : ℝ) * conditionalRowsProbability P k / m

theorem sum_centeredOccupation {m n : ℕ} (hm : 0 < m) (P : Board m n) (k : ℕ) :
    (∑ i, centeredOccupation P k i) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  simp only [centeredOccupation, Finset.sum_sub_distrib, sum_occupationProbability,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem occupation_dot_centered {m n : ℕ} (P : Board m n) (k : ℕ) (x : Fin m → ℝ) :
    (∑ i, occupationProbability P k i * x i) =
      (∑ i, centeredOccupation P k i * x i) +
        ((k : ℝ) * conditionalRowsProbability P k / m) * ∑ i, x i := by
  simp only [centeredOccupation, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- Centering exposes the positive constant-vector coefficient in the exact kernel bound. -/
theorem occupationKernel_centered_lower {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (x : Fin m → ℝ) (qmax : ℝ)
    (hq : ∀ i, occupationProbability P k i ≤ qmax) :
    (1 - conditionalRowsProbability P k +
      2 * ((k : ℝ) * conditionalRowsProbability P k / m)) * (∑ i, x i) ^ 2 +
      2 * (∑ i, x i) * (∑ i, centeredOccupation P k i * x i) +
      (conditionalRowsProbability P k - (k + 1 : ℝ) * qmax) * (∑ i, x i ^ 2) ≤
        ∑ i, ∑ h, x i * occupationKernel P k i h * x h := by
  have h := occupationKernel_quadratic_lower P k hP x qmax hq
  rw [occupation_dot_centered] at h
  convert h using 1
  ring

private theorem completed_square_lower (a s d : ℝ) (ha : 0 < a) :
    -(d ^ 2 / a) ≤ a * s ^ 2 + 2 * s * d := by
  rw [← neg_div]
  apply (div_le_iff₀ ha).mpr
  nlinarith [sq_nonneg (a * s + d)]

/-- The centered moment costs at most m||qdev||²/(2kq0), with all sign conditions explicit. -/
theorem occupationKernel_spectral_lower {m n : ℕ} (hm : 0 < m) (P : Board m n) (k : ℕ)
    (hk : 0 < k) (hP : ∀ i j, 0 ≤ P i j) (hZ : 0 < columnDistinctMass P k)
    (hq0 : 0 < conditionalRowsProbability P k) (qmax : ℝ)
    (hq : ∀ i, occupationProbability P k i ≤ qmax) (x : Fin m → ℝ) :
    (conditionalRowsProbability P k - (k + 1 : ℝ) * qmax -
      (m : ℝ) * (∑ i, centeredOccupation P k i ^ 2) /
        (2 * k * conditionalRowsProbability P k)) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ h, x i * occupationKernel P k i h * x h := by
  let a : ℝ := 2 * ((k : ℝ) * conditionalRowsProbability P k / m)
  let s : ℝ := ∑ i, x i
  let d : ℝ := ∑ i, centeredOccupation P k i * x i
  let v : ℝ := ∑ i, centeredOccupation P k i ^ 2
  let t : ℝ := ∑ i, x i ^ 2
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have ha : 0 < a := mul_pos (by norm_num) (div_pos (mul_pos hkpos hq0) hmpos)
  have hcs : d ^ 2 ≤ v * t := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hcomplete := completed_square_lower a s d ha
  have hpenalty : -(v / a) * t ≤ a * s ^ 2 + 2 * s * d := by
    calc
      _ = -(v * t / a) := by ring
      _ ≤ -(d ^ 2 / a) := neg_le_neg (div_le_div_of_nonneg_right hcs ha.le)
      _ ≤ _ := hcomplete
  have hq01 := conditionalRowsProbability_le_one P k hP hZ
  have hconstant : 0 ≤ (1 - conditionalRowsProbability P k) * s ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hq01) (sq_nonneg s)
  have hbase := occupationKernel_centered_lower P k hP x qmax hq
  change (1 - conditionalRowsProbability P k + a) * s ^ 2 + 2 * s * d +
    (conditionalRowsProbability P k - (k + 1 : ℝ) * qmax) * t ≤ _ at hbase
  have hratio : v / a = (m : ℝ) * v / (2 * k * conditionalRowsProbability P k) := by
    dsimp [a]
    field_simp
  rw [hratio] at hpenalty
  change (conditionalRowsProbability P k - (k + 1 : ℝ) * qmax -
    (m : ℝ) * v / (2 * k * conditionalRowsProbability P k)) * t ≤ _
  nlinarith

/-- The centered vector minimizes squared distance among all constant shifts. -/
theorem centeredOccupation_sq_le_shift {m n : ℕ} (hm : 0 < m) (P : Board m n) (k : ℕ)
    (c : ℝ) : (∑ i, centeredOccupation P k i ^ 2) ≤
      ∑ i, (occupationProbability P k i - c) ^ 2 := by
  let d : ℝ := (k : ℝ) * conditionalRowsProbability P k / m - c
  have he (i : Fin m) : (occupationProbability P k i - c) ^ 2 =
      centeredOccupation P k i ^ 2 + 2 * d * centeredOccupation P k i + d ^ 2 := by
    dsimp [centeredOccupation, d]
    ring
  have hid : (∑ i, (occupationProbability P k i - c) ^ 2) =
      (∑ i, centeredOccupation P k i ^ 2) + (m : ℝ) * d ^ 2 := by
    simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_centeredOccupation hm P k, mul_zero, add_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hid]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg d))

/-- Dimensionless squared deviation of the row marginal from uniform. -/
noncomputable def rowDispersion {m n : ℕ} (P : Board m n) : ℝ :=
  (m : ℝ) * ∑ i, (rowSum P i - (1 : ℝ) / m) ^ 2

theorem rowDispersion_nonneg {m n : ℕ} (P : Board m n) : 0 ≤ rowDispersion P :=
  mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem rowDispersion_secondMoment {m n : ℕ} (hm : 0 < m) (P : Board m n)
    (hmass : totalMass P = 1) : (m : ℝ) * (∑ i, rowSum P i ^ 2) = 1 + rowDispersion P := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hsum : (∑ i, rowSum P i) = 1 := hmass
  simp only [rowDispersion, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The pointwise occupation error bound gives Eq. (10), including rows of zero mass. -/
theorem centeredOccupation_variance_bound {m n : ℕ} (hm : 0 < m) (P : Board m n) (k : ℕ)
    (hP : IsProbability P) (b ξ : ℝ) (hb : 0 ≤ b) (hξ : 0 ≤ ξ)
    (herr : ∀ i, |occupationProbability P k i - (k : ℝ) * rowSum P i| ≤
      2 * k * b * ξ * rowSum P i) :
    (m : ℝ) * (∑ i, centeredOccupation P k i ^ 2) ≤
      8 * (k : ℝ) ^ 2 * b ^ 2 * ξ ^ 2 * (1 + rowDispersion P) +
        2 * (k : ℝ) ^ 2 * rowDispersion P := by
  let δ : ℝ := 2 * k * b * ξ
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have herror (i : Fin m) : (occupationProbability P k i - (k : ℝ) * rowSum P i) ^ 2 ≤
      δ ^ 2 * rowSum P i ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hδ (rowSum_nonneg hP.1 i))).mpr (herr i)
    simpa only [sq_abs, mul_pow] using h
  have hpoint (i : Fin m) : (occupationProbability P k i - (k : ℝ) / m) ^ 2 ≤
      2 * δ ^ 2 * rowSum P i ^ 2 + 2 * (k : ℝ) ^ 2 * (rowSum P i - (1 : ℝ) / m) ^ 2 := by
    have he : occupationProbability P k i - (k : ℝ) / m =
        (occupationProbability P k i - (k : ℝ) * rowSum P i) +
          (k : ℝ) * (rowSum P i - (1 : ℝ) / m) := by ring
    rw [he]
    nlinarith [herror i, sq_nonneg ((occupationProbability P k i - (k : ℝ) * rowSum P i) -
      (k : ℝ) * (rowSum P i - (1 : ℝ) / m))]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hscaled := mul_le_mul_of_nonneg_left
    ((centeredOccupation_sq_le_shift hm P k ((k : ℝ) / m)).trans hsum) (Nat.cast_nonneg m)
  have hrow := rowDispersion_secondMoment hm P hP.2
  calc
    _ ≤ (m : ℝ) * (2 * δ ^ 2 * (∑ i, rowSum P i ^ 2) +
        2 * (k : ℝ) ^ 2 * ∑ i, (rowSum P i - (1 : ℝ) / m) ^ 2) := hscaled
    _ = _ := by
      rw [← hrow]
      dsimp [δ, rowDispersion]
      ring

/-- The three rational estimates in the large-board occupation argument. -/
theorem occupation_numeric_bounds (k b ξ θ : ℝ) (hk : 2 ≤ k)
    (hb0 : 0 ≤ b) (hb : b ≤ k ^ 2 / 2) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / (64 * k ^ 3))
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / (32 * k)) :
    (k + 1) * (2 * k * ξ) ≤ 3 / 128 ∧
      8 * k * b ^ 2 * ξ ^ 2 * (1 + θ) ≤ 1 / 2048 ∧
      2 * k * θ ≤ 1 / 16 := by
  have hk0 : 0 < k := by linarith
  have hθ1 : θ ≤ 1 := by
    have hbound : (1 : ℝ) / (32 * k) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact hθ.trans hbound
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (k + 1) * (2 * k * (1 / (64 * k ^ 3))) := by gcongr
      _ = (k + 1) / (32 * k ^ 2) := by field_simp; ring
      _ ≤ 3 / 128 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (k - 2)]
  · calc
      _ ≤ 8 * k * (k ^ 2 / 2) ^ 2 * (1 / (64 * k ^ 3)) ^ 2 * 2 := by gcongr; linarith
      _ = 1 / (1024 * k) := by field_simp; ring
      _ ≤ 1 / 2048 := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith
  · calc
      _ ≤ 2 * k * (1 / (32 * k)) := by gcongr
      _ = 1 / 16 := by field_simp; norm_num

/-- The audited rational lower bound follows from the actual occupation controls.
The q0, qi, and error hypotheses are separate probabilistic obligations. -/
theorem occupationKernel_rational_lower_of_control {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (k : ℕ) (hk : 2 ≤ k) (hP : IsProbability P)
    (hZ : 0 < columnDistinctMass P k) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / (64 * (k : ℝ) ^ 3))
    (hθ : rowDispersion P ≤ 1 / (32 * k))
    (hq0 : (1 : ℝ) / 2 ≤ conditionalRowsProbability P k)
    (hq : ∀ i, occupationProbability P k i ≤ 2 * k * ξ)
    (herr : ∀ i, |occupationProbability P k i - (k : ℝ) * rowSum P i| ≤
      2 * k * (k.choose 2 : ℝ) * ξ * rowSum P i) (x : Fin m → ℝ) :
    (847 / 2048 : ℝ) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ h, x i * occupationKernel P k i h * x h := by
  let b : ℝ := k.choose 2
  let θ : ℝ := rowDispersion P
  let v : ℝ := ∑ i, centeredOccupation P k i ^ 2
  let penaltyBound : ℝ := 8 * k * b ^ 2 * ξ ^ 2 * (1 + θ) + 2 * k * θ
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkN : 0 < k := by omega
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have hb : b ≤ (k : ℝ) ^ 2 / 2 := by
    dsimp [b]
    rw [Nat.cast_choose_two]
    nlinarith
  have hθ0 : 0 ≤ θ := rowDispersion_nonneg P
  have hnum := occupation_numeric_bounds (k : ℝ) b ξ θ hkR hb0 hb hξ0 hξ hθ0 hθ
  have hvar := centeredOccupation_variance_bound hm P k hP b ξ hb0 hξ0 herr
  have hq0pos : 0 < conditionalRowsProbability P k := by linarith
  have hden : 0 < 2 * (k : ℝ) * conditionalRowsProbability P k := by positivity
  have hpenaltyBound : 0 ≤ penaltyBound := by dsimp [penaltyBound]; positivity
  have hscaled : (m : ℝ) * v ≤ (k : ℝ) * penaltyBound := by
    convert hvar using 1
    dsimp [penaltyBound, θ]
    ring
  have hpenalty : (m : ℝ) * v / (2 * k * conditionalRowsProbability P k) ≤ penaltyBound := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ (k : ℝ) * penaltyBound := hscaled
      _ ≤ (2 * k * conditionalRowsProbability P k) * penaltyBound :=
        mul_le_mul_of_nonneg_right (by nlinarith) hpenaltyBound
      _ = _ := mul_comm _ _
  have hsmall : penaltyBound ≤ 1 / 2048 + 1 / 16 := by
    exact add_le_add hnum.2.1 hnum.2.2
  have hcoeff : (847 / 2048 : ℝ) ≤ conditionalRowsProbability P k -
      (k + 1 : ℝ) * (2 * k * ξ) -
      (m : ℝ) * v / (2 * k * conditionalRowsProbability P k) := by
    linarith [hnum.1]
  calc
    _ ≤ (conditionalRowsProbability P k - (k + 1 : ℝ) * (2 * k * ξ) -
        (m : ℝ) * v / (2 * k * conditionalRowsProbability P k)) * (∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ _ := occupationKernel_spectral_lower hm P k hkN hP.1 hZ hq0pos (2 * k * ξ) hq x

/-- In particular, the conditional occupation controls imply G/E ≥ (2/5)I. -/
theorem occupationKernel_two_fifths_of_control {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (k : ℕ) (hk : 2 ≤ k) (hP : IsProbability P)
    (hZ : 0 < columnDistinctMass P k) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / (64 * (k : ℝ) ^ 3))
    (hθ : rowDispersion P ≤ 1 / (32 * k))
    (hq0 : (1 : ℝ) / 2 ≤ conditionalRowsProbability P k)
    (hq : ∀ i, occupationProbability P k i ≤ 2 * k * ξ)
    (herr : ∀ i, |occupationProbability P k i - (k : ℝ) * rowSum P i| ≤
      2 * k * (k.choose 2 : ℝ) * ξ * rowSum P i) (x : Fin m → ℝ) :
    (2 / 5 : ℝ) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ h, x i * occupationKernel P k i h * x h := by
  calc
    _ ≤ (847 / 2048 : ℝ) * (∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ _ := occupationKernel_rational_lower_of_control hm P k hk hP hZ ξ hξ0 hξ hθ hq0 hq herr x

end DittertRybin
