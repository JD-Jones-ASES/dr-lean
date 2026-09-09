import DR.Rectangular.ThreeRowKKT
import DR.Collision.Averaging

/-!
# Same-support averaging of actual global maximizers

The flatness conclusion concerns a maximizer on the full probability simplex.
It does not assert that averaging is monotone at an arbitrary matrix.
-/

namespace DittertRybin
open scoped BigOperators

/-- The mass-preserving direction of a physical column blend. -/
def separationColumnDirection {m n : ℕ} (P : Board m n) (a b : Fin n) : Board m n :=
  fun i j => (if j = a then P i b - P i a else 0) +
    (if j = b then P i a - P i b else 0)

theorem blendColumns_eq_line {m n : ℕ} (P : Board m n) (a b : Fin n) (hab : a ≠ b) (t : ℝ) :
    blendColumns P a b t = fun i j => P i j + separationColumnDirection P a b i j * t := by
  ext i j
  rw [blendColumns_eq_add_corrections P a b hab]
  unfold separationColumnDirection
  split_ifs <;> ring

theorem separationColumnDirection_gradient_dot {m n : ℕ} (P : Board m n)
    (k : ℕ) (a b : Fin n) :
    (∑ i, ∑ j, separationGradient P k i j * separationColumnDirection P a b i j) =
      ∑ i, (separationGradient P k i a - separationGradient P k i b) * (P i b - P i a) := by
  simp only [separationColumnDirection, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasDerivAt_separationProbability_blend {m n : ℕ} (P : Board m n) (k : ℕ)
    (a b : Fin n) (hab : a ≠ b) :
    HasDerivAt (fun t : ℝ => separationProbability (blendColumns P a b t) k)
      (∑ i, (separationGradient P k i a - separationGradient P k i b) * (P i b - P i a)) 0 := by
  simpa only [blendColumns_eq_line P a b hab, separationColumnDirection_gradient_dot] using
    hasDerivAt_separationProbability_line P (separationColumnDirection P a b) k

/-- Exact flatness, derived from full-simplex first-order conditions at the original board. -/
theorem IsSeparationGlobalMax.same_support_blend_flat {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P) (hk : 2 ≤ k)
    (a b : Fin n) (hab : a ≠ b) (hsupport : ∀ i, 0 < P i a ↔ 0 < P i b) (t : ℝ) :
    separationProbability (blendColumns P a b t) k = separationProbability P k := by
  have hdot : (∑ i, (separationGradient P k i a - separationGradient P k i b) *
      (P i b - P i a)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases ha : 0 < P i a
    · have heq := hmax.gradient_eq hP (i, a) (i, b) ha ((hsupport i).mp ha)
      dsimp at heq
      rw [heq, sub_self, zero_mul]
    · have hia : P i a = 0 := le_antisymm (le_of_not_gt ha) (hP.1 i a)
      have hib : P i b = 0 := le_antisymm (le_of_not_gt (mt (hsupport i).mpr ha)) (hP.1 i b)
      simp only [hia, hib, sub_self, mul_zero]
  have hzero := hasDerivAt_separationProbability_blend P k a b hab
  rw [hdot] at hzero
  let L : ℝ := (k.factorial : ℝ) * ∑ i, ∑ h,
    (P i a - P i b) * averagingKernel (eraseColumns P {a, b}) (k - 2) i h * (P h a - P h b)
  have hformula : (fun s : ℝ => separationProbability (blendColumns P a b s) k) =
      fun s => separationProbability P k + s * (1 - s) * L := by
    funext s
    have h := separationProbability_blend_identity_of_two_le P hk a b hab s
    dsimp [L]
    linarith only [h]
  have hderiv : HasDerivAt (fun s : ℝ => separationProbability P k + s * (1 - s) * L) L 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).const_sub 1)).mul_const L).const_add
      (separationProbability P k) using 1 <;> norm_num <;> rfl
  rw [hformula] at hzero
  have hL : L = 0 := hderiv.unique hzero
  have heq := congrFun hformula t
  simpa only [hL, mul_zero, add_zero] using heq

theorem IsSeparationGlobalMax.same_support_blend {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P) (hk : 2 ≤ k)
    (a b : Fin n) (hab : a ≠ b) (hsupport : ∀ i, 0 < P i a ↔ 0 < P i b)
    (t : ℝ) : IsSeparationGlobalMax (blendColumns P a b t) k := by
  intro Q hQ
  rw [hmax.same_support_blend_flat hP hk a b hab hsupport]
  exact hmax Q hQ

/-- A blend preserves a shared positive lower bound, including its endpoint parameters. -/
theorem blendColumns_entry_lower {m n : ℕ} {P : Board m n} (a b : Fin n)
    {t ε : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin m)
    (ha : ε ≤ P i a) (hb : ε ≤ P i b) :
    ε ≤ blendColumns P a b t i a := by
  rw [blendColumns_left]
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1)
  have h2 := mul_le_mul_of_nonneg_left hb ht
  nlinarith only [h1, h2]

end DittertRybin
