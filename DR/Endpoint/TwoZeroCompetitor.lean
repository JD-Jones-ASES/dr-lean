import DR.Endpoint.NearEndpointPaddingCounting
import DR.Square.Permanent
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-! Exact signed permanent formulas with one or two exceptional rows, and an
actual doubly stochastic competitor with two independent zero entries. -/

namespace DittertRybin
open scoped BigOperators

theorem permanent_one_exceptional_row {n : ℕ} (A : Board (n+1) (n+1)) (c : ℝ)
    (hA : ∀ i : Fin n, ∀ j, A i.succ j = c) :
    A.permanent = (n.factorial : ℝ)*c^n*∑ j, A 0 j := by
  rw [permanent_expand_row_zero]
  have heach (j : Fin (n+1)) :
      Matrix.permanent (fun r k : Fin n => A r.succ (j.succAbove k)) =
        (n.factorial : ℝ)*c^n := by
    simp only [hA]
    simpa using (permanent_const (ι := Fin n) c)
  simp only [heach]
  rw [← Finset.sum_mul]
  ring

theorem permanent_two_exceptional_rows {n : ℕ} (A : Board (n+2) (n+2)) (c : ℝ)
    (hA : ∀ i : Fin n, ∀ j, A i.succ.succ j = c) :
    A.permanent = (n.factorial : ℝ)*c^n*
      ((∑ j, A 0 j)*(∑ j, A 1 j)-∑ j, A 0 j*A 1 j) := by
  rw [permanent_expand_row_zero]
  have heach (j : Fin (n+2)) :
      Matrix.permanent (fun r k : Fin (n+1) => A r.succ (j.succAbove k)) =
        (n.factorial : ℝ)*c^n*((∑ k, A 1 k)-A 1 j) := by
    rw [permanent_one_exceptional_row (n := n)
      (fun r k => A r.succ (j.succAbove k)) c (fun i k => hA i (j.succAbove k))]
    congr 1
    have hs := Fin.sum_univ_succAbove (fun k => A 1 k) j
    simp only [Fin.succ_zero_eq_one] at *
    linarith
  simp only [heach]
  calc
    _ = (n.factorial : ℝ)*c^n*∑ j, A 0 j*((∑ k, A 1 k)-A 1 j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]

/-- The uniform board with a mass-preserving checkerboard perturbation on its
first two rows and columns. The two off-diagonal cells are exactly zero. -/
def twoZeroCheckerSign {n : ℕ} (i : Fin (n+2)) : ℝ :=
  if i = 0 then 1 else if i = 1 then -1 else 0

noncomputable def twoZeroCompetitor (n : ℕ) : Board (n+2) (n+2) :=
  fun i j => ((n : ℝ)+2)⁻¹*(1+twoZeroCheckerSign i*twoZeroCheckerSign j)

theorem twoZeroCompetitor_transpose (n : ℕ) :
    (twoZeroCompetitor n).transpose = twoZeroCompetitor n := by
  ext i j
  change ((n : ℝ)+2)⁻¹*(1+twoZeroCheckerSign j*twoZeroCheckerSign i) = _
  simp only [twoZeroCompetitor, mul_comm]

theorem twoZeroCompetitor_nonneg (n : ℕ) (i j : Fin (n+2)) :
    0 ≤ twoZeroCompetitor n i j := by
  unfold twoZeroCompetitor twoZeroCheckerSign
  split_ifs <;> positivity

theorem twoZeroCheckerSign_sum (n : ℕ) :
    (∑ i : Fin (n+2), twoZeroCheckerSign i) = 0 := by
  have h01 : (0 : Fin (n+2)) ≠ 1 := Fin.zero_ne_one'
  have heach (i : Fin (n+2)) : twoZeroCheckerSign i =
      (if i = 0 then 1 else 0)-(if i = 1 then 1 else 0) := by
    unfold twoZeroCheckerSign
    split_ifs <;> simp_all
  simp only [heach, Finset.sum_sub_distrib]
  simp

theorem twoZeroCompetitor_row_sum (n : ℕ) (i : Fin (n+2)) :
    (∑ j, twoZeroCompetitor n i j) = 1 := by
  have hn : (n : ℝ)+2 ≠ 0 := by positivity
  simp only [twoZeroCompetitor, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, twoZeroCheckerSign_sum, mul_zero, add_zero]
  simp [Nat.cast_add, hn]

theorem twoZeroCompetitor_mem_doublyStochastic (n : ℕ) :
    twoZeroCompetitor n ∈ doublyStochastic ℝ (Fin (n+2)) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨twoZeroCompetitor_nonneg n, twoZeroCompetitor_row_sum n, ?_⟩
  intro j
  have h := twoZeroCompetitor_row_sum n j
  have ht := congrArg (fun A : Board (n+2) (n+2) => ∑ i, A j i)
    (twoZeroCompetitor_transpose n)
  simpa [Matrix.transpose_apply] using ht.trans h

theorem twoZeroCompetitor_zeros (n : ℕ) :
    twoZeroCompetitor n 0 1 = 0 ∧ twoZeroCompetitor n 1 0 = 0 := by
  have h01 : (0 : Fin (n+2)) ≠ 1 := Fin.zero_ne_one'
  simp [twoZeroCompetitor, twoZeroCheckerSign, h01.symm]

theorem twoZeroCompetitor_ordinary (n : ℕ) (i : Fin n) (j : Fin (n+2)) :
    twoZeroCompetitor n i.succ.succ j = ((n : ℝ)+2)⁻¹ := by
  simp [twoZeroCompetitor, twoZeroCheckerSign, ← Fin.succ_zero_eq_one,
    -Fin.succ_zero_eq_one']

/-- Exact value of the concrete face competitor, including the two-by-two
boundary where the strict comparison below becomes equality. -/
theorem twoZeroCompetitor_permanent (n : ℕ) :
    (twoZeroCompetitor n).permanent =
      ((n+2).factorial+2*(n.factorial : ℝ))/((n : ℝ)+2)^(n+2) := by
  rw [permanent_two_exceptional_rows _ _ (twoZeroCompetitor_ordinary n),
    twoZeroCompetitor_row_sum, twoZeroCompetitor_row_sum]
  have hdot : (∑ j, twoZeroCompetitor n 0 j*twoZeroCompetitor n 1 j) =
      (n : ℝ)*((n : ℝ)+2)⁻¹^2 := by
    have h01 : (0 : Fin (n+2)) ≠ 1 := Fin.zero_ne_one'
    simp [twoZeroCompetitor, twoZeroCheckerSign, Fin.sum_univ_succ,
      ← Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', pow_two]
  rw [hdot]
  have hc : (n : ℝ)+2 ≠ 0 := by positivity
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [pow_add, inv_pow]
  field_simp
  ring

theorem twoZeroCompetitor_permanent_ratio (n : ℕ) :
    (twoZeroCompetitor n).permanent =
      dittertConstant (n+2)*(1+2/(((n : ℝ)+2)*((n : ℝ)+1))) := by
  rw [twoZeroCompetitor_permanent]
  unfold dittertConstant
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

theorem twoZeroCompetitor_permanent_lt_two {n : ℕ} (hn : 0 < n) :
    (twoZeroCompetitor n).permanent < 2*dittertConstant (n+2) := by
  rw [twoZeroCompetitor_permanent_ratio]
  have hgamma : 0 < dittertConstant (n+2) := by unfold dittertConstant; positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : 2 < ((n : ℝ)+2)*((n : ℝ)+1) := by nlinarith
  have hratio : 2/(((n : ℝ)+2)*((n : ℝ)+1)) < 1 :=
    (div_lt_one (by positivity)).mpr hprod
  nlinarith

end DittertRybin
