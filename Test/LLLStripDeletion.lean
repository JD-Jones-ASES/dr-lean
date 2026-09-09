import DR.Endpoint.LLLStripDeletion

namespace DittertRybin.Tests
open scoped BigOperators

-- An actual nonempty lower-edge instance satisfies all integer guards.
example : 64*(2^22)≤(2^39:ℕ) :=
  endpoint_strip_n_ge (by norm_num) (by norm_num)
example : (2^39:ℕ)≤(2^22)^2 := endpoint_strip_n_le_square (by norm_num)
example : ((2^22:ℕ):ℝ)*(4*((2^22:ℕ):ℝ)/((2^39:ℕ):ℝ))^2≤1/256 :=
  endpoint_strip_cap_sq (by norm_num) (by norm_num)
example : ((2^22:ℕ):ℝ)*(4/((2^39:ℕ):ℝ))≤1/16 :=
  endpoint_strip_deletion_scale (by norm_num) (by norm_num)

-- The nominal lower dimension does not imply the interval is nonempty.
example : ¬∃n:ℕ,4096*128^3≤n^2 ∧ 20*n≤128*(128-1) := by
  rintro ⟨n,hl,hu⟩
  have hn := endpoint_strip_n_ge (by norm_num : 1≤128) hl
  omega

-- Losing the dimension power in the lower edge would invalidate the cap.
example : ¬((128:ℝ)*(4*128/8192)^2≤1/256) := by norm_num

-- Exact normalized-row cap on a board with a zero cell and unequal row mass.
example : colSum (normalizeRows (![![2,0],![0,3]] : Board 2 2)) 0≤3/2 := by
  apply normalizeRows_column_cap_of_row_lower _ (by
    intro i j; fin_cases i <;> fin_cases j <;> norm_num) 2 3 (by norm_num)
  · intro i; fin_cases i <;> norm_num [rowSum,Fin.sum_univ_succ]
  · intro j; fin_cases j <;> norm_num [colSum,Fin.sum_univ_succ]

#print axioms endpoint_strip_n_ge
#print axioms endpoint_strip_n_le_square
#print axioms endpoint_strip_cap_sq
#print axioms endpoint_strip_deletion_scale
#print axioms endpoint_strip_contender_column_cap
#print axioms normalizeRows_column_cap_of_row_lower
#print axioms endpoint_strip_deleted_bounds
end DittertRybin.Tests
