import DR.Rectangular.ThreeRowProperMasses

namespace DittertRybin.Tests
open scoped BigOperators

-- The exact singular boundary x=y>0,z=0 is allowed and forces equal exclusive entries.
example {b e : ℝ} (hb : 0 < b) (he : 0 < e)
    (hL : 3 * e ≤ 3 * b) (hR : 3 * b ≤ 3 * e) : e = b := by
  have h := threeRow_proper_pair_equal_remainders (x := 1) (z := 0) hb he
    (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hL]) (by nlinarith only [hR])
  exact h.2.2

-- A zero individual remainder is valid: no division by x or y is permitted.
example : (0 : ℝ) ^ 2 + 0 * 1 + 1 ^ 2 - 0 ^ 2 > 0 := by
  exact orderThree_proper_pair_D_pos (b := 1) (e := 1) (x := 0) (y := 1) (z := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- Positive z at equal remainders is rejected even though D itself is still positive.
example {b e : ℝ} (hb : 0 < b) (he : 0 < e) : ¬ (5 * e ≤ 2 * b ∧ 5 * b ≤ 2 * e) := by
  rintro ⟨hL, hR⟩
  have h := threeRow_proper_pair_equal_remainders (x := 1) (z := 1) hb he
    (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hL]) (by nlinarith only [hR])
  norm_num at h

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (hproper : ThreeRowProperSupport P) (i h : Fin 3) (a b : Fin n)
    (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b) : rowSum P i = rowSum P h :=
  hmax.threeRow_proper_doublet_row_masses_eq hP hn hproper i h a b ha hb

private noncomputable def properCycle : Board 3 3 := fun i j => if i.val = j.val then 0 else 1 / 6
private theorem properCycle_value : separationProbability properCycle 3 = 7 / 18 := by
  rw [separationProbability_threeRow_cubic]
  norm_num [threeRowSuccessPolynomial, totalMass, rowSum, colSum, properCycle,
    Fin.sum_univ_succ, Fin.add_def]

-- This proper support satisfies full first-order conditions, including at all three zeros.
example (i j : Fin 3) : separationGradient properCycle 3 i j = 7 / 6 := by
  rw [separationGradient_threeRow]
  fin_cases i <;> fin_cases j <;>
    norm_num [threeRowReducedGradient, threeRowPair, totalMass, rowSum, colSum, properCycle,
      Fin.sum_univ_succ, Fin.add_def]

-- Its exclusion uses a strict global value gap, not an incorrect first-order contradiction.
example : ¬ IsSeparationGlobalMax properCycle 3 := by
  intro h
  have hu : separationProbability (uniformBoard 3 3) 3 = 32 / 81 := by
    rw [separationProbability_threeRow_cubic]
    norm_num [threeRowSuccessPolynomial, totalMass, rowSum, colSum, uniformBoard,
      Fin.sum_univ_succ]
  have hb := h _ (uniformBoard_isProbability (by norm_num : 0 < 3) (by norm_num : 0 < 3))
  rw [properCycle_value, hu] at hb
  norm_num at hb

#print axioms IsSeparationGlobalMax.threeRow_doublet_pair_schur
#print axioms IsSeparationGlobalMax.threeRow_doublet_equal_rows
#print axioms threeRow_missing_gradient_sum
#print axioms IsSeparationGlobalMax.threeRow_proper_doublet_row_masses_eq
end DittertRybin.Tests
