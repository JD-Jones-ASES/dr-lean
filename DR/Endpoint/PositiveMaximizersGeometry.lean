import DR.Rectangular.ThreeRowSupportNormal
import DR.Rectangular.OrderTwo

/-!
# Squared norm and reverse column averaging

The norm identity holds for signed boards and every real parameter. A positive
probability board admits a negative parameter, while uniform is the unique
minimum of the squared norm on the entire closed probability simplex.
-/

namespace DittertRybin
open scoped BigOperators

/-- Exact squared Frobenius norm change, including negative blend parameters. -/
theorem orderThreeSquareSum_blendColumns {m n : ℕ} (P : Board m n)
    (a b : Fin n) (hab : a ≠ b) (t : ℝ) :
    orderThreeSquareSum (blendColumns P a b t) = orderThreeSquareSum P -
      2 * t * (1 - t) * ∑ i, (P i a - P i b) ^ 2 := by
  have hterm (i : Fin m) (j : Fin n) : blendColumns P a b t i j ^ 2 = P i j ^ 2 +
      (if j = a then ((1 - t) * P i a + t * P i b) ^ 2 - P i a ^ 2 else 0) +
      (if j = b then (t * P i a + (1 - t) * P i b) ^ 2 - P i b ^ 2 else 0) := by
    by_cases ha : j = a <;> by_cases hb : j = b <;> simp_all [blendColumns]
  have hrow (i : Fin m) : (∑ j, blendColumns P a b t i j ^ 2) =
      (∑ j, P i j ^ 2) - 2 * t * (1 - t) * (P i a - P i b) ^ 2 := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp only [orderThreeSquareSum, hrow, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Strict positivity supplies an actual feasible reverse blend, not just a tangent direction. -/
theorem exists_negative_blend_probability {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (hpos : ∀ i j, 0 < P i j)
    (a b : Fin n) (hab : a ≠ b) :
    ∃ t : ℝ, t < 0 ∧ IsProbability (blendColumns P a b t) := by
  obtain ⟨ε, hε, hfloor⟩ := exists_sameSupportFloor P
  refine ⟨-ε / 2, by linarith, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i j
    have ha := (hfloor i a).2 (hpos i a)
    have hb := (hfloor i b).2 (hpos i b)
    have ha1 := hP.entry_le_one i a
    have hb1 := hP.entry_le_one i b
    have hpa := mul_nonneg (le_of_lt hε) (hP.1 i a)
    have hpb := mul_nonneg (le_of_lt hε) (hP.1 i b)
    have hma := mul_le_mul_of_nonneg_left ha1 (le_of_lt hε)
    have hmb := mul_le_mul_of_nonneg_left hb1 (le_of_lt hε)
    unfold blendColumns
    split_ifs
    · nlinarith only [ha, hε, hpa, hmb]
    · nlinarith only [hb, hε, hpb, hma]
    · exact hP.1 i j
  · simpa only [totalMass, rowSum_blendColumns P a b hab] using hP.2

theorem orderThreeSquareSum_uniform {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    orderThreeSquareSum (uniformBoard m n) = ((m : ℝ) * n)⁻¹ := by
  have h := sum_sq_sub_uniformBoard hm hn (uniformBoard_isProbability hm hn)
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at h
  simpa only [Fintype.sum_prod_type, orderThreeSquareSum] using (sub_eq_zero.mp h.symm)

/-- Uniform uniquely minimizes the squared norm, with no positivity assumption on the board. -/
theorem orderThreeSquareSum_le_uniform_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) :
    orderThreeSquareSum P ≤ orderThreeSquareSum (uniformBoard m n) ↔
      P = uniformBoard m n := by
  constructor
  · intro hle
    have h := sum_sq_sub_uniformBoard hm hn hP
    have hnonneg : 0 ≤ ∑ a : Fin m × Fin n,
        (P a.1 a.2 - uniformBoard m n a.1 a.2) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [orderThreeSquareSum_uniform hm hn] at hle
    have hsum : (∑ a : Fin m × Fin n,
        (P a.1 a.2 - uniformBoard m n a.1 a.2) ^ 2) = 0 := by
      have hnested : (∑ a : Fin m × Fin n, P a.1 a.2 ^ 2) = orderThreeSquareSum P :=
        Fintype.sum_prod_type _
      rw [hnested] at h
      linarith
    have heach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (a : Fin m × Fin n) (_ : a ∈ Finset.univ) =>
        sq_nonneg (P a.1 a.2 - uniformBoard m n a.1 a.2))).mp hsum
    ext i j
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (heach (i, j) (Finset.mem_univ _)))
  · rintro rfl
    exact le_rfl

end DittertRybin
