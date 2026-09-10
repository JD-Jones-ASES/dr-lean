import DR.Endpoint.LongColumnClosure
import DR.Endpoint.LeadingUniform
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- A literal nonuniform deletion, including an unaffected row.
example : (∑ i : Fin 2,
    (1-(2 : ℝ)*(((![1/2,1/2] : Fin 2 → ℝ) i-
      (![1/400,0] : Fin 2 → ℝ) i)/(1-(1/400 : ℝ))))^2) < 1/9 := by
  apply longColumn_deleted_row_sq_lt (by decide)
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num
  · norm_num [Fin.sum_univ_succ]

-- No deletion is also admitted, with the full original row budget.
example {m : ℕ} (hm : 1 ≤ m) (r : Fin m → ℝ)
    (hr : (∑ i, ((m : ℝ)*r i-1)^2) < 1/16) :
    (∑ i, (1-(m : ℝ)*r i)^2) < 1/9 := by
  simpa using longColumn_deleted_row_sq_lt hm r (fun _ => 0) 0
    (by simp) (by simp) (by simp) hr

-- A signed deletion vector with total zero can violate the conclusion.
example : ¬(∑ i : Fin 2,
    (1-(2 : ℝ)*(((![1/2,1/2] : Fin 2 → ℝ) i-
      (![-1,1] : Fin 2 → ℝ) i)/(1-(0 : ℝ))))^2) < 1/9 := by
  norm_num [Fin.sum_univ_succ]

-- The new asymmetric square weights are necessary for this row budget:
-- the older factor-two estimate does not certify the desired1/9 bound.
example : (5/4 : ℝ)*(1/16)+5*(1/10000) < (1/9)*(9801/10000) ∧
    ¬(2 : ℝ)*(1/16)+2*(1/10000) < (1/9)*(9801/10000) := by norm_num

-- Actual retained mass7/8, without falsely calling the retained board a
-- probability board or renormalizing its entries in the averaging kernel.
example {n : ℕ} (hn : 10000*16^2 ≤ n) :
    (averagingKernel ((7/8 : ℝ) • uniformBoard 16 n) (16-2)).PosDef := by
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  let B := (7/8 : ℝ) • uniformBoard 16 n
  have hB : ∀ i j, 0 ≤ B i j := by
    intro i j
    change 0 ≤ (7/8 : ℝ)*uniformBoard 16 n i j
    exact mul_nonneg (by norm_num) ((uniformBoard_isProbability (by decide) hn0).1 i j)
  have hr (i : Fin 16) : rowSum B i = 7/128 := by
    simp [B,rowSum,uniformBoard]
    field_simp
    norm_num
  have hmass : totalMass B = 7/8 := by
    change (∑ i, rowSum B i) = _
    simp only [hr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  have hc (j : Fin n) : colSum B j = (7/8 : ℝ)/(n : ℝ) := by
    simp [B,colSum,uniformBoard]
    field_simp
  apply longColumn_retained_kernel_posDef (by decide) hn B hB
  · rw [hmass]; norm_num
  · simp only [hr,hmass]
    norm_num
  · intro j
    rw [hc]
    exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)

-- Literal uniform input and two erased columns: the retained board has
-- actual zero columns, yet its original averaging kernel is strictly positive.
example {m n : ℕ} (hm : 16 ≤ m) (hn : 10000*m^2 ≤ n)
    (a b : Fin n) (hab : a ≠ b) :
    (averagingKernel (eraseColumns (uniformBoard m n) {a,b}) (m-2)).PosDef ∧
    (∀ i, eraseColumns (uniformBoard m n) {a,b} i a = 0) := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by have hp : 0 < m^2 := pow_pos hm0 2; omega
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  constructor
  · apply longColumn_contender_kernel_of_caps hm hn (uniformBoard_isProbability hm0 hn0) _ _ a b hab
    · rw [endpoint_uniform_row_marginal hm0 hn0]
      simp [hmR]
    · intro j
      have hc : colSum (uniformBoard m n) j = 1/(n : ℝ) := by
        simp [colSum,uniformBoard]
        field_simp
      rw [hc]
      exact div_lt_div_of_pos_right (by norm_num) hnR
  · intro i
    simp [eraseColumns]

-- Actual zero original rows are excluded by the required scaled deviation,
-- not by an unrecorded assumption that every original entry is positive.
example {m n : ℕ} (P : Board m n) (i : Fin m) (hi : rowSum P i=0) :
    ¬(∑ a, ((m : ℝ)*rowSum P a-1)^2) < 1/16 := by
  have h := Finset.single_le_sum (fun a _ => sq_nonneg ((m : ℝ)*rowSum P a-1))
    (Finset.mem_univ i)
  rw [hi] at h
  norm_num at h
  linarith

#print axioms longColumn_deleted_row_sq_scaled_le
#print axioms longColumn_deleted_row_sq_lt
#print axioms longColumn_kept_row_sq_lt
#print axioms longColumn_retained_kernel_posDef
#print axioms longColumn_contender_kernel_of_caps
#print axioms uniform_maximum_endpoint_of_longColumn_caps

end DittertRybin.Tests
