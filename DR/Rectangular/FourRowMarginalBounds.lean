import DR.Rectangular.FourRowLeadingKernel

/-! Exact closed-neighborhood marginal estimates for the four-row kernel. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowMarginalVariance (s : Fin 4 → ℝ) : ℝ :=
  ∑ i, (s i - 1 / 4) ^ 2

theorem fourRowMarginalVariance_nonneg (s : Fin 4 → ℝ) :
    0 ≤ fourRowMarginalVariance s := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem fourRowMarginalVariance_squareSum (s : Fin 4 → ℝ) (hsum : ∑ i, s i = 1) :
    ∑ i, s i ^ 2 = 1 / 4 + fourRowMarginalVariance s := by
  unfold fourRowMarginalVariance
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, hsum]
  ring

theorem fourRow_zeroSum_coordinate (d : Fin 4 → ℝ) (hsum : ∑ i, d i = 0) (i : Fin 4) :
    4 * d i ^ 2 ≤ 3 * ∑ j, d j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i) d (fun _ => (1 : ℝ))
  have hlin : ∑ j ∈ Finset.univ.erase i, d j = -d i := by
    have h' := Finset.sum_erase_add Finset.univ d (Finset.mem_univ i)
    rw [hsum] at h'
    linarith
  have hsq : ∑ j ∈ Finset.univ.erase i, d j ^ 2 = (∑ j, d j ^ 2) - d i ^ 2 := by
    have h' := Finset.sum_erase_add Finset.univ (fun j => d j ^ 2) (Finset.mem_univ i)
    linarith
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hlin, hsq] at h
  norm_num at h
  linarith

theorem fourRowMarginalVariance_coordinate (s : Fin 4 → ℝ) (hsum : ∑ i, s i = 1) (i : Fin 4) :
    4 * (s i - 1 / 4) ^ 2 ≤ 3 * fourRowMarginalVariance s := by
  exact fourRow_zeroSum_coordinate (fun j => s j - 1 / 4)
    (by simp [Finset.sum_sub_distrib, hsum]) i

theorem fourRowMarginalVariance_coordinates (s : Fin 4 → ℝ) (hsum : ∑ i, s i = 1)
    (hnear : fourRowMarginalVariance s ≤ 1 / 40) :
    ∀ i, 1 / 10 < s i ∧ s i < 2 / 5 := by
  intro i
  have h := fourRowMarginalVariance_coordinate s hsum i
  constructor <;> nlinarith

/-- The signed product bound follows from two explicit sums of squares. -/
theorem fourRow_product_lower_squareSum (d : Fin 4 → ℝ) :
    -(∑ i, d i ^ 2) ^ 2 / 16 ≤ ∏ i, d i := by
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ]
  nlinarith [sq_nonneg (d 0 ^ 2 + d 1 ^ 2 - d 2 ^ 2 - d 3 ^ 2),
    sq_nonneg (d 0 * d 2 + d 1 * d 3), sq_nonneg (d 0 * d 3 + d 1 * d 2)]

theorem fourRow_product_le_uniform (s : Fin 4 → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hsum : ∑ i, s i = 1) : ∏ i, s i ≤ 1 / 256 := by
  have hsum' : s 0 + s 1 + s 2 + s 3 = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hsum
  let a := s 0 + s 1
  let b := s 2 + s 3
  have ha : 0 ≤ a := add_nonneg (hs 0) (hs 1)
  have hb : 0 ≤ b := add_nonneg (hs 2) (hs 3)
  have hab : a * b ≤ 1 / 4 := by dsimp [a,b]; nlinarith [sq_nonneg (a-b)]
  have hpaira : s 0 * s 1 ≤ a ^ 2 / 4 := by dsimp [a]; nlinarith [sq_nonneg (s 0-s 1)]
  have hpairb : s 2 * s 3 ≤ b ^ 2 / 4 := by dsimp [b]; nlinarith [sq_nonneg (s 2-s 3)]
  have hprod := mul_le_mul hpaira hpairb (mul_nonneg (hs 2) (hs 3))
    (div_nonneg (sq_nonneg a) (by norm_num : (0 : ℝ) ≤ 4))
  have hsq := mul_self_le_mul_self (mul_nonneg ha hb) hab
  simp [Fin.prod_univ_succ]
  nlinarith

theorem fourRow_product_centered (s : Fin 4 → ℝ) (hsum : ∑ i, s i = 1) :
    ∏ i, s i = 1 / 256 - fourRowMarginalVariance s / 32 +
      (∑ i, (s i - 1 / 4) ^ 3) / 12 + ∏ i, (s i - 1 / 4) := by
  have hs3 : s 3 = 1 - s 0 - s 1 - s 2 := by
    simp [Fin.sum_univ_succ] at hsum
    linarith
  simp [fourRowMarginalVariance, Fin.sum_univ_succ, Fin.prod_univ_succ]
  rw [hs3]
  ring

theorem fourRow_cube_lower_of_small_energy (d : Fin 4 → ℝ)
    (henergy : ∑ i, d i ^ 2 ≤ 1 / 40) :
    -(∑ i, d i ^ 2) / 6 ≤ ∑ i, d i ^ 3 := by
  have hlow (i : Fin 4) : -1 / 6 ≤ d i := by
    have h := Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i)
    nlinarith
  calc
    _ = ∑ i, -(d i ^ 2) / 6 := by simp [← Finset.sum_div, ← Finset.sum_neg_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_nonneg (sq_nonneg (d i)) (show 0 ≤ d i + 1 / 6 by linarith [hlow i])]

theorem fourRow_product_lower_of_near (s : Fin 4 → ℝ) (hsum : ∑ i, s i = 1)
    (hnear : fourRowMarginalVariance s ≤ 1 / 40) :
    631 / 230400 ≤ ∏ i, s i := by
  have hcube := fourRow_cube_lower_of_small_energy (fun i => s i - 1 / 4) hnear
  have hprod := fourRow_product_lower_squareSum (fun i => s i - 1 / 4)
  have hV := fourRowMarginalVariance_nonneg s
  have hsq := mul_self_le_mul_self hV hnear
  have hid := fourRow_product_centered s hsum
  change -fourRowMarginalVariance s / 6 ≤ _ at hcube
  change -(fourRowMarginalVariance s) ^ 2 / 16 ≤ _ at hprod
  nlinarith

end DittertRybin
