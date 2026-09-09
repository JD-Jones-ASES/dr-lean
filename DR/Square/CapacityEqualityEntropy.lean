import DR.Square.CapacityUnivariate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

/-!
# The strict entropy factor in permanent equality

For a probability vector a, the product of (1-a_i)^(1-a_i) is at least
G(n), with equality only at a_i=1/n. Jensen's strict convexity is applied
to x log x on the closed nonnegative half-line. The factor at a_i=1 is
0^0=1, consistently with exp(0 log 0); no division by 1-a_i occurs.
-/

namespace DittertRybin

open scoped BigOperators

noncomputable def matrixEntropyFactor {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∏ i, Real.rpow (1 - a i) (1 - a i)

theorem rpow_self_eq_exp_mul_log {x : ℝ} (hx : 0 ≤ x) :
    Real.rpow x x = Real.exp (x * Real.log x) := by
  rw [Real.rpow_eq_pow]
  by_cases hz : x = 0
  · simp [hz]
  · simpa only [mul_comm] using Real.rpow_def_of_pos (lt_of_le_of_ne hx (Ne.symm hz)) x

theorem matrixEntropyFactor_eq_exp {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, a i ≤ 1) :
    matrixEntropyFactor a = Real.exp (∑ i, (1 - a i) * Real.log (1 - a i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact rpow_self_eq_exp_mul_log (sub_nonneg.mpr (ha i))

theorem capacityFactor_eq_exp {n : ℕ} (hn : 2 ≤ n) :
    capacityFactor n = Real.exp (((n : ℝ) - 1) * Real.log (((n : ℝ) - 1) / n)) := by
  have hnR : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  unfold capacityFactor
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos (by linarith) (by linarith))]
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  congr 1
  ring

/-- Jensen lower bound and its exact equality characterization, before exponentiation. -/
theorem matrixEntropy_log_bound {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    ((n : ℝ) - 1) * Real.log (((n : ℝ) - 1) / n) ≤
      ∑ i, (1 - a i) * Real.log (1 - a i) ∧
    (((n : ℝ) - 1) * Real.log (((n : ℝ) - 1) / n) =
      ∑ i, (1 - a i) * Real.log (1 - a i) ↔ ∀ i, a i = (n : ℝ)⁻¹) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn0 := hnR.ne'
  have hai (i : Fin n) : a i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  let q := ((n : ℝ) - 1) / n
  let S := ∑ i, (1 - a i) * Real.log (1 - a i)
  have hw : (∑ _ : Fin n, (n : ℝ)⁻¹) = 1 := by simp [hn0]
  have hmean : (∑ i, (n : ℝ)⁻¹ * (1 - a i)) = q := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    dsimp [q]
    ring
  have hweighted : (∑ i, (n : ℝ)⁻¹ * ((1 - a i) * Real.log (1 - a i))) = S / n := by
    rw [← Finset.mul_sum]
    dsimp [S]
    ring
  have hj := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := fun i => 1 - a i)
    (fun _ _ => (inv_pos.mpr hnR).le) hw (fun i _ => sub_nonneg.mpr (hai i))
  simp only [smul_eq_mul] at hj
  rw [hmean, hweighted] at hj
  have hmul : (n : ℝ) * (q * Real.log q) = ((n : ℝ) - 1) * Real.log q := by
    dsimp [q]
    field_simp
  have hb : ((n : ℝ) - 1) * Real.log q ≤ S := by
    have h := mul_le_mul_of_nonneg_left hj hnR.le
    rwa [hmul, mul_div_cancel₀ S hn0] at h
  refine ⟨hb, ?_⟩
  constructor
  · intro heq
    have heqJ : q * Real.log q = S / n := by
      apply (mul_left_cancel₀ hn0)
      rw [hmul, mul_div_cancel₀ S hn0]
      exact heq
    have he := (Real.strictConvexOn_mul_log.map_sum_eq_iff
      (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := fun i => 1 - a i)
      (fun _ _ => inv_pos.mpr hnR) hw (fun i _ => sub_nonneg.mpr (hai i)))
    simp only [smul_eq_mul] at he
    rw [hmean, hweighted] at he
    intro i
    have hi := he.mp heqJ i (Finset.mem_univ i)
    dsimp [q] at hi
    apply (mul_left_cancel₀ hn0)
    field_simp at hi ⊢
    nlinarith
  · intro hu
    simp_rw [hu]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have heq : 1 - (n : ℝ)⁻¹ = ((n : ℝ) - 1) / n := by field_simp
    rw [heq]
    dsimp [q] at hmul
    exact hmul.symm

/-- The strict closed-simplex entropy factor used in van der Waerden equality. -/
theorem matrixEntropyFactor_lower_bound {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) : capacityFactor n ≤ matrixEntropyFactor a := by
  have hai (i : Fin n) : a i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  rw [matrixEntropyFactor_eq_exp a hai, capacityFactor_eq_exp hn, Real.exp_le_exp]
  exact (matrixEntropy_log_bound hn a ha hsum).1

/-- Equality, or a reverse inequality, forces every original column entry to be 1/n. -/
theorem matrixEntropyFactor_le_iff {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    matrixEntropyFactor a ≤ capacityFactor n ↔ ∀ i, a i = (n : ℝ)⁻¹ := by
  have hai (i : Fin n) : a i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  rw [matrixEntropyFactor_eq_exp a hai, capacityFactor_eq_exp hn, Real.exp_le_exp]
  obtain ⟨hlo, heq⟩ := matrixEntropy_log_bound hn a ha hsum
  constructor
  · intro h
    exact heq.mp (le_antisymm hlo h)
  · intro h
    exact (heq.mpr h).ge

end DittertRybin
