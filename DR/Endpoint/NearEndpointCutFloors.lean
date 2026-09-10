import DR.Endpoint.NearEndpointCuts
import DR.Endpoint.NearEndpointPadding
import DR.Square.ZeroRectangle

/-! The active complementary zero rectangle survives the actual corner-zero
padding. Its sharp permanent floor is combined with any separately proved
permanent floor of that same padded matrix. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def nearEndpointRectangleFloor (n k l : ℕ) : ℝ :=
  dittertConstant (k+1)*dittertConstant (l+1)/dittertConstant (k+l+1-n)

noncomputable def nearEndpointCutRookFloor (n : ℕ) (v : ℝ) (k l : ℕ) : ℝ :=
  distinctUniformProbability n (n-1)*
    (if k<n ∧ l<n then max v (nearEndpointRectangleFloor n k l) else v) /
      boundaryPermanentFloor (n+1)

/-- Any actual padding permanent lower bound transfers with the μ/a factor
proved in the signed identity. -/
theorem nearEndpointRookRatio_lower_of_padding {n : ℕ} (hn : 2 ≤ n)
    (P : Board n n) {v : ℝ} (hv : v ≤ (nearEndpointPadding P).permanent) :
    distinctUniformProbability n (n-1)*v/boundaryPermanentFloor (n+1) ≤ nearEndpointRookRatio P := by
  have ha := distinctUniformProbability_pos (by omega : 0 < n) (Nat.sub_le n 1)
  have hmu := boundaryPermanentFloor_pos (by omega : 3 ≤ n+1)
  have h := mul_le_mul_of_nonneg_left hv
    (div_nonneg ha.le hmu.le)
  rw [permanent_nearEndpointPadding_eq_ratio (by omega)] at h
  convert h using 1 <;> first | rfl | field_simp

/-- The original complement becomes a physical zero rectangle in the padded
square, with sizes n−k and n−l and residual order k+l+1−n. -/
theorem nearEndpointPadding_complement_rectangle_lower {n : ℕ} (hn : 1 ≤ n)
    {B : Board n n} (hB : IsProbability B)
    (hr : ∀ i, rowSum B i = 1/(n : ℝ)) (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (I J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J)
    (hzero : cutMass B Iᶜ Jᶜ = 0) :
    nearEndpointRectangleFloor n I.card J.card ≤ (nearEndpointPadding B).permanent := by
  have hIc : I.card ≤ n := by simpa using I.card_le_univ
  have hJc : J.card ≤ n := by simpa using J.card_le_univ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rectangularCutDemand_square I J (by omega)] at hp
  have hsum : n < I.card+J.card := by
    have hraw := (div_pos_iff_of_pos_right hnR).mp hp
    have h : (n : ℝ) < I.card+J.card := by linarith
    exact_mod_cast h
  let K := Iᶜ.map (Fin.succEmb n)
  let L := Jᶜ.map (Fin.succEmb n)
  have hK : K.card = n-I.card := by simp [K,Finset.card_compl]
  have hL : L.card = n-J.card := by simp [L,Finset.card_compl]
  have hsize : K.card+L.card < n+1 := by omega
  have hentry (i : Fin n) (hi : i ∈ Iᶜ) (j : Fin n) (hj : j ∈ Jᶜ) : B i j = 0 := by
    have hrzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Iᶜ) => Finset.sum_nonneg (fun j _ => hB.1 i j))).mp hzero i hi
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Jᶜ) => hB.1 i j)).mp hrzero j hj
  have hpad : ∀ i ∈ K, ∀ j ∈ L, nearEndpointPadding B i j = 0 := by
    intro i hi j hj
    obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨c,hc,rfl⟩ := Finset.mem_map.mp hj
    simp only [Fin.coe_succEmb,nearEndpointPadding_original,hentry r hr c hc,mul_zero]
  have hfloor := permanent_lower_bound_of_zero_rectangle
    (nearEndpointPadding_mem_doublyStochastic (by omega) hB.1 hr hc) K L hsize hpad
  have hk : n+1-K.card = I.card+1 := by omega
  have hl : n+1-L.card = J.card+1 := by omega
  have hd : n+1-K.card-L.card = I.card+J.card+1-n := by omega
  rw [hd,hk,hl] at hfloor
  exact hfloor

/-- Combining independently justified floors uses the actual padded matrix;
the input v is explicit until its separate two-zero theorem is supplied. -/
theorem nearEndpointRookRatio_sized_lower_bound {n : ℕ} (hn : 2 ≤ n)
    {B : Board n n} (hB : IsProbability B)
    (hr : ∀ i, rowSum B i = 1/(n : ℝ)) (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (I J : Finset (Fin n)) (hp : 0 < rectangularCutDemand I J)
    (hzero : cutMass B Iᶜ Jᶜ = 0) {v : ℝ} (hv : v ≤ (nearEndpointPadding B).permanent) :
    nearEndpointCutRookFloor n v I.card J.card ≤ nearEndpointRookRatio B := by
  unfold nearEndpointCutRookFloor
  apply nearEndpointRookRatio_lower_of_padding hn B
  split_ifs
  · exact max_le hv (nearEndpointPadding_complement_rectangle_lower (by omega) hB hr hc I J hp hzero)
  · exact hv

end DittertRybin
