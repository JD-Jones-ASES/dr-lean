import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The finite normalized-log-concavity step needed for the k-versus-two bound. -/

namespace DittertRybin

theorem concave_sequence_from_two (f : ℕ → ℝ) {n : ℕ} (h0 : f 0 = 0)
    (hc : ∀ j, j+2 ≤ n → f j+f (j+2) ≤ 2*f (j+1))
    {k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) : 2*f k ≤ (k:ℝ)*f 2 := by
  have hs : ∀ j, 1 ≤ j → j+1 ≤ n → 2*(f (j+1)-f j) ≤ f 2 := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj hjn
      by_cases hz : j = 0
      · subst j
        have h := hc 0 (by omega)
        norm_num only [zero_add,Nat.cast_ofNat] at h ⊢
        rw [h0] at h
        linarith
      · have h := ih (by omega) (by omega)
        have h' := hc j (by omega)
        simpa only [Nat.succ_eq_add_one] using (show 2*(f (j+1+1)-f (j+1)) ≤ f 2 by linarith)
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases htwo : 2 ≤ k
    · have h := ih htwo (by omega)
      have h' := hs k (by omega) hkn
      rw [Nat.cast_succ]
      linarith
    · have heq : k+1 = 2 := by omega
      simpa only [Nat.succ_eq_add_one,heq,Nat.cast_ofNat] using (le_rfl : 2*f 2 ≤ 2*f 2)

theorem positive_newton_power_bound (a : ℕ → ℝ) {n k : ℕ}
    (hpos : ∀ j, j ≤ n → 0 < a j) (h0 : a 0 = 1)
    (hnewton : ∀ j, j+2 ≤ n → a j*a (j+2) ≤ a (j+1)^2)
    (hk : 2 ≤ k) (hkn : k ≤ n) : a k^2 ≤ a 2^k := by
  have hc : ∀ j, j+2 ≤ n → Real.log (a j)+Real.log (a (j+2)) ≤ 2*Real.log (a (j+1)) := by
    intro j hj
    have h := Real.log_le_log (mul_pos (hpos j (by omega)) (hpos (j+2) hj)) (hnewton j hj)
    rw [Real.log_mul (hpos j (by omega)).ne' (hpos (j+2) hj).ne',Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have h := concave_sequence_from_two (fun j => Real.log (a j)) (by rw [h0,Real.log_one]) hc hk hkn
  apply (Real.log_le_log_iff (pow_pos (hpos k hkn) 2) (pow_pos (hpos 2 (by omega)) k)).mp
  simpa only [Real.log_pow,Nat.cast_ofNat] using h

end DittertRybin
