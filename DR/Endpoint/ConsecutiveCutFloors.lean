import DR.Endpoint.BoundaryRook
import DR.Endpoint.MinimumDilation
import DR.Square.ZeroRectangle

/-! The actual permanent floor attached to a minimum-dilation cut. The
complementary zero rectangle lies in the balanced board; original zeros
are retained separately by the one-zero floor. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def endpointConsecutiveRectangleFloor (m n k l : ℕ) : ℝ :=
  dittertConstant (n-m+k)*dittertConstant l/dittertConstant (k+l-m)

noncomputable def endpointConsecutiveCutRookFloor (m n k l : ℕ) : ℝ :=
  distinctUniformProbability n m *
    (if k < m ∧ l < n then max (boundaryPermanentFloor n) (endpointConsecutiveRectangleFloor m n k l)
      else boundaryPermanentFloor n) / dittertConstant n

theorem positive_rectangular_cut_card_sum {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (I : Finset (Fin m)) (J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J) :
    m < I.card+J.card := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hJ : (J.card : ℝ)/n ≤ (J.card : ℝ)/m :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hmR hmnR
  have hp' : 1 < (I.card : ℝ)/m+(J.card : ℝ)/n := by
    dsimp [rectangularCutDemand] at hp
    linarith
  have hs : 1 < ((I.card+J.card : ℕ) : ℝ)/m := by
    rw [Nat.cast_add, add_div]
    linarith
  have h := (lt_div_iff₀ hmR).mp hs
  exact_mod_cast (by simpa only [one_mul] using h : (m : ℝ) < (I.card+J.card : ℕ))

/-- The zero complementary rectangle survives the original-row padding exactly. -/
theorem endpointRookRatio_complement_rectangle_lower_bound {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) {B : Board m n}
    (hB : IsProbability B) (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (I : Finset (Fin m)) (J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J)
    (hzero : cutMass B Iᶜ Jᶜ = 0) :
    distinctUniformProbability n m * endpointConsecutiveRectangleFloor m n I.card J.card /
      dittertConstant n ≤ endpointRookRatio B := by
  have hn : 0 < n := by omega
  have hki : I.card ≤ m := by simpa using I.card_le_univ
  have hlj : J.card ≤ n := by simpa using J.card_le_univ
  have hsum := positive_rectangular_cut_card_sum hm hmn I J hp
  let K := Iᶜ.map (Fin.castLEEmb hmn)
  have hK : K.card = m-I.card := by simp [K, Finset.card_compl]
  have hJ : Jᶜ.card = n-J.card := by simp [Finset.card_compl]
  have hsize : K.card+Jᶜ.card < n := by omega
  have hentry (i : Fin m) (hi : i ∈ Iᶜ) (j : Fin n) (hj : j ∈ Jᶜ) : B i j = 0 := by
    have hrzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Iᶜ) => Finset.sum_nonneg (fun j _ => hB.1 i j))).mp hzero i hi
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Jᶜ) => hB.1 i j)).mp hrzero j hj
  have hzpad : ∀ i ∈ K, ∀ j ∈ Jᶜ, rectangularPadding hmn B i j = 0 := by
    intro i hi j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
    simp only [Fin.coe_castLEEmb, rectangularPadding_original, hentry a ha j hj, mul_zero]
  have hfloor := permanent_lower_bound_of_zero_rectangle
    (rectangularPadding_mem_doublyStochastic hmn hm hn B hB.1 hr hc) K Jᶜ hsize hzpad
  have hleft : n-K.card = n-m+I.card := by omega
  have hright : n-Jᶜ.card = J.card := by omega
  have hremain : n-K.card-Jᶜ.card = I.card+J.card-m := by omega
  rw [hremain, hleft, hright, permanent_rectangularPadding_eq_endpointRookRatio] at hfloor
  have hfac : 0 < ((n-m).factorial : ℝ)/(n : ℝ)^(n-m) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hf : (0 : ℝ) < (n-m).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  apply (mul_le_mul_iff_right₀ hfac).mp
  calc
    ((n-m).factorial : ℝ)/(n : ℝ)^(n-m) *
      (distinctUniformProbability n m*endpointConsecutiveRectangleFloor m n I.card J.card/dittertConstant n) =
      endpointConsecutiveRectangleFloor m n I.card J.card := by
        rw [mul_div_assoc, ← mul_assoc, rectangularPadding_factor_mul_uniform hmn]
        exact mul_div_cancel₀ _ (endpoint_a_pos hn).ne'
    _ ≤ ((n-m).factorial : ℝ)/(n : ℝ)^(n-m)*endpointRookRatio B := hfloor

/-- The maximum of the inherited one-zero and active rectangle floors is valid on the actual board. -/
theorem endpointRookRatio_sized_boundary_lower_bound {m n : ℕ}
    (hm : 0 < m) (hn : 3 ≤ n) (hmn : m ≤ n) {B : Board m n}
    (hB : IsProbability B) (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ)) (hz : ∃ i j, B i j = 0)
    (I : Finset (Fin m)) (J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J)
    (hzero : cutMass B Iᶜ Jᶜ = 0) :
    endpointConsecutiveCutRookFloor m n I.card J.card ≤ endpointRookRatio B := by
  have hbase : distinctUniformProbability n m*boundaryPermanentFloor n/dittertConstant n ≤
      endpointRookRatio B := by
    simpa only [boundaryPermanentRatio, mul_div_assoc] using
      endpointRookRatio_boundary_lower_bound hm hn hmn hB.1 hr hc hz
  have hrectangle := endpointRookRatio_complement_rectangle_lower_bound hm hmn hB hr hc I J hp hzero
  unfold endpointConsecutiveCutRookFloor
  split_ifs
  · rcases le_total (boundaryPermanentFloor n) (endpointConsecutiveRectangleFloor m n I.card J.card) with h | h
    · rw [max_eq_right h]
      exact hrectangle
    · rw [max_eq_left h]
      exact hbase
  · exact hbase

end DittertRybin
