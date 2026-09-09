import DR.Square.Normalization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Homogeneous lower-order Dittert bounds on arbitrary nonnegative block mass. -/

namespace DittertRybin
open scoped BigOperators

theorem board_eq_zero_of_nonneg_mass_zero {m n : ℕ} (A : Board m n)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 0) : A = 0 := by
  ext i j
  have hc : A i j ≤ rowSum A i :=
    Finset.single_le_sum (fun j _ => hA i j) (Finset.mem_univ j)
  have hr : rowSum A i ≤ totalMass A :=
    Finset.single_le_sum (fun r _ => Finset.sum_nonneg fun c _ => hA r c) (Finset.mem_univ i)
  change A i j = 0
  exact le_antisymm (by linarith) (hA i j)

/-- A mass-n theorem scales to every nonnegative mass, with no omitted zero case. -/
theorem DittertMaximizer.homogeneous {n : ℕ} (hD : DittertMaximizer n)
    (hn : 0 < n) (A : Board n n) (hA : ∀ i j, 0 ≤ A i j) :
    dittertFunctional A ≤ (2-dittertConstant n) * (totalMass A / n)^n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmass : 0 ≤ totalMass A :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA i j
  rcases hmass.eq_or_lt with hm0 | hmpos
  · have hzero := board_eq_zero_of_nonneg_mass_zero A hA hm0.symm
    subst A
    let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    simp [dittertFunctional, totalMass, rowSum, colSum, Nat.ne_of_gt hn]
  · let c : ℝ := n / totalMass A
    have hc : 0 < c := div_pos hnR hmpos
    have hcmass : totalMass (c • A) = n := by
      rw [totalMass_smul]
      exact div_mul_cancel₀ _ hmpos.ne'
    have h := (hD (c • A) (fun i j => mul_nonneg hc.le (hA i j)) hcmass).1
    rw [dittertFunctional_smul] at h
    have hscale : 0 ≤ (totalMass A / n)^n := by positivity
    have hcancel : (totalMass A / n)^n * c^n = 1 := by
      rw [← mul_pow]
      have hbase : totalMass A / n * c = 1 := by
        dsimp [c]
        field_simp [hmpos.ne', hnR.ne']
      rw [hbase, one_pow]
    calc
      dittertFunctional A = (totalMass A / n)^n * (c^n * dittertFunctional A) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ (totalMass A / n)^n * (2-dittertConstant n) :=
        mul_le_mul_of_nonneg_left h hscale
      _ = _ := mul_comm _ _

/-- The exact permanent floor used after deleting rows and columns. -/
theorem DittertMaximizer.permanent_lower {n : ℕ} (hD : DittertMaximizer n)
    (hn : 0 < n) (A : Board n n) (hA : ∀ i j, 0 ≤ A i j) :
    (∏ i, rowSum A i) + (∏ j, colSum A j) -
      (2-dittertConstant n) * (totalMass A / n)^n ≤ A.permanent := by
  have h := hD.homogeneous hn A hA
  unfold dittertFunctional at h
  linarith

end DittertRybin
