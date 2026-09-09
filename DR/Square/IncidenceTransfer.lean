import DR.Square.WeightedSweep
import DR.Certificates.Gram

/-!
# Transferring a strict edge-Gram bound to the vertex range

A finite Cauchy--Schwarz argument suffices; no numerical eigenvalue or
connectivity assertion is used. The range witness is an explicit hypothesis
to be constructed for the positive weighted path.
-/

namespace DittertRybin

open scoped BigOperators

theorem matrix_range_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ ℝ) (v : κ → ℝ) (f : ι → ℝ)
    (hf : ∀ i, f i = ∑ j, B i j * v j) :
    (∑ j, v j * ∑ i, B i j * f i) = ∑ i, f i ^ 2 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = f i * ∑ j, B i j * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← hf i]; ring

/-- Strict edge coercivity gives strict vertex coercivity on the nonzero range. -/
theorem incidence_strict_bound_transfer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι κ ℝ) (h : ℝ)
    (hGram : ∀ v : κ → ℝ, v ≠ 0 →
      h * (∑ j, v j ^ 2) < ∑ i, (∑ j, B i j * v j) ^ 2)
    (f : ι → ℝ) (hf0 : 0 < ∑ i, f i ^ 2)
    (hrange : ∃ v : κ → ℝ, ∀ i, f i = ∑ j, B i j * v j) :
    h * (∑ i, f i ^ 2) < ∑ j, (∑ i, B i j * f i) ^ 2 := by
  obtain ⟨v, hv⟩ := hrange
  have hv0 : v ≠ 0 := by
    intro heq
    have hf : ∀ i, f i = 0 := by simpa [heq] using hv
    simp_rw [hf] at hf0
    simp at hf0
  have hvpos : 0 < ∑ j, v j ^ 2 := by
    have hvex : ∃ j, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    obtain ⟨j, hj⟩ := hvex
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hj)
      (Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ j))
  have hstrict := hGram v hv0
  simp_rw [← hv] at hstrict
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun j => ∑ i, B i j * f i)
  rw [matrix_range_inner B v f hv] at hcs
  have hmul := mul_lt_mul_of_pos_right hstrict hf0
  nlinarith

end DittertRybin
