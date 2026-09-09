import DR.Collision.Averaging
import DR.Collision.OccupationCollisions
import DR.Collision.OccupationScaling
import DR.Maximizers

/-!
# Uniformity on every sufficiently large rectangle

For every sample order K ≥ 4, dimensions at least the explicit D_K force
the uniform matrix to be the unique maximizer of the actual inclusive-OR
sampling probability. The proof combines collision concentration, normalized
column deletion, occupation-kernel positivity and the exact blend identity.
Applying column rigidity to the transpose forces all entries to be equal.
No square Dittert theorem or permanent lower bound is used.
-/

namespace DittertRybin

open scoped BigOperators

theorem eraseColumns_eq_keepColumns {m n : ℕ} (P : Board m n) (S : Finset (Fin n)) :
    eraseColumns P S = keepColumns P Sᶜ := by
  ext i j
  by_cases hj : j ∈ S <;> simp [eraseColumns, keepColumns, hj]

/-- Every contender has a strictly positive averaging coefficient and a positive quadratic kernel. -/
theorem contender_averagingKernel_lower {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (hk : 4 ≤ k)
    (hsize : largeBoardThreshold k ≤ min m n)
    (hcont : separationProbability (uniformBoard m n) k ≤ separationProbability P k)
    (a b : Fin n) (hab : a ≠ b) :
    0 < averagingCoefficient (eraseColumns P {a, b}) (k - 2) ∧
      ∀ x : Fin m → ℝ,
        averagingCoefficient (eraseColumns P {a, b}) (k - 2) * (2 / 5) * (∑ i, x i ^ 2) ≤
          ∑ i, ∑ h, x i * averagingKernel (eraseColumns P {a, b}) (k - 2) i h * x h := by
  let T := keepColumns P ({a, b}ᶜ)
  have hk2 : 2 ≤ k - 2 := by omega
  obtain ⟨hmass, hprob, hpeak, hrow⟩ := contender_deletion_bounds hm hn hP hk hsize hcont a b hab
  have hμ : 0 < totalMass T := by dsimp [T]; linarith
  have hZnorm := columnDistinctMass_pos_of_small_marginal hm (normalizeBoard T) (k - 2) hk2
    hprob hpeak
  have hZ : 0 < columnDistinctMass T (k - 2) := by
    rw [normalizeBoard_eq_smul, columnDistinctMass_smul] at hZnorm
    exact pos_of_mul_pos_right hZnorm (pow_nonneg (inv_nonneg.mpr hμ.le) _)
  have hE := averagingCoefficient_pos T (k - 2) hZ
  rw [eraseColumns_eq_keepColumns]
  refine ⟨hE, ?_⟩
  intro x
  have hq := occupationKernel_two_fifths hm (normalizeBoard T) (k - 2) hk2 hprob hpeak hrow x
  simp_rw [occupationKernel_normalizeBoard T (k - 2) (ne_of_gt hμ)] at hq
  calc
    _ = averagingCoefficient T (k - 2) * ((2 / 5) * ∑ i, x i ^ 2) := by ring
    _ ≤ averagingCoefficient T (k - 2) *
        (∑ i, ∑ h, x i * occupationKernel T (k - 2) i h * x h) :=
      mul_le_mul_of_nonneg_left hq hE.le
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [averagingKernel_eq_coefficient_occupationKernel T (k - 2) hZ i h]
      ring

/-- A global maximizer above the threshold has identical columns. -/
theorem largeBoard_maximizer_equal_columns {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hk : 4 ≤ k) (hsize : largeBoardThreshold k ≤ min m n)
    (P : Board m n) (hP : IsProbability P)
    (hmax : ∀ Q : Board m n, IsProbability Q → separationProbability Q k ≤ separationProbability P k) :
    ∀ i a b, P i a = P i b := by
  intro i a b
  by_cases hab : a = b
  · rw [hab]
  have hcont := hmax (uniformBoard m n) (uniformBoard_isProbability hm hn)
  obtain ⟨hE, hkernel⟩ := contender_averagingKernel_lower hm hn hP hk hsize hcont a b hab
  let x : Fin m → ℝ := fun j => P j a - P j b
  have hq := hkernel x
  have hmid := hmax (blendColumns P a b (1 / 2))
    (blendColumns_isProbability hP a b hab (1 / 2) (by norm_num) (by norm_num))
  have hid := separationProbability_blend_identity_of_two_le (k := k) P (by omega) a b hab (1 / 2)
  have hfactor : (0 : ℝ) < (1 / 2) * (1 - 1 / 2) * k.factorial := by
    have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
    positivity
  have hquad : (∑ j, ∑ h, x j * averagingKernel (eraseColumns P {a, b}) (k - 2) j h * x h) ≤ 0 := by
    apply nonpos_of_mul_nonpos_right (ha := hfactor)
    change (1 / 2) * (1 - 1 / 2) * (k.factorial : ℝ) *
      (∑ j, ∑ h, (P j a - P j b) * averagingKernel (eraseColumns P {a, b}) (k - 2) j h *
        (P h a - P h b)) ≤ 0
    linarith [hid]
  have hsquares : (∑ j, x j ^ 2) ≤ 0 := by
    exact nonpos_of_mul_nonpos_right (hq.trans hquad) (mul_pos hE (by norm_num))
  have hi : x i ^ 2 ≤ 0 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hsquares
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _)))

/-- Rybin P2 for every K≥4 on all rectangles above the explicit collision threshold. -/
theorem uniform_maximum_large_boards {m n k : ℕ} (hk : 4 ≤ k)
    (hm : largeBoardThreshold k ≤ m) (hn : largeBoardThreshold k ≤ n) :
    UniformMaximizer m n k := by
  have hD : 0 < largeBoardThreshold k := by
    unfold largeBoardThreshold
    have hk2 : 0 < k - 2 := by omega
    positivity
  have hm0 : 0 < m := hD.trans_le hm
  have hn0 : 0 < n := hD.trans_le hn
  apply uniform_maximizer_of_column_rigidity hm0 hn0 k
  · exact largeBoard_maximizer_equal_columns hm0 hn0 hk (le_min hm hn)
  · exact largeBoard_maximizer_equal_columns hn0 hm0 hk (le_min hn hm)

/-- The simpler sufficient threshold min(M,N)≥K^21, with the same unique equality case. -/
theorem uniform_maximum_large_boards_power {m n k : ℕ} (hk : 4 ≤ k)
    (hm : k ^ 21 ≤ m) (hn : k ^ 21 ≤ n) : UniformMaximizer m n k :=
  uniform_maximum_large_boards hk ((largeBoardThreshold_le_power hk).trans hm)
    ((largeBoardThreshold_le_power hk).trans hn)

end DittertRybin
