import DR.Endpoint.MarginalDiscrepancy
import DR.Endpoint.BoundaryScalingParameters
import DR.Endpoint.CutDeficit
import DR.Endpoint.BoundaryRook
import DR.Endpoint.PositiveMaximizers
import DR.Rectangular.OrderThreeLarge

/-! Full rectangular endpoint uniqueness from the arithmetic boundary-scaling
criterion. Every contender is treated on the closed simplex, including zero
cells and zero rook deficit. The transport, padding and permanent bounds are
actual proved inputs, not a gauge assumption. -/

namespace DittertRybin
open scoped BigOperators

theorem endpoint_boundary_contender_impossible_of_arithmetic {m n g : ℕ}
    (hm : 3 ≤ m) (hn : 18 ≤ n) (hmn : m ≤ n) (hg : 1 ≤ g)
    (hgm : g ∣ m) (hgn : g ∣ n)
    (hcriterion : distinctUniformProbability n m+((n : ℝ)-1)*dittertConstant m <
      (512/289)*(g : ℝ)^2/((m : ℝ)^3*(n : ℝ)^2*((n : ℝ)-1)^2))
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    (hz : ∃ i j, P i j = 0) : False := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have ha := endpoint_a_pos (by omega : 0 < m)
  have hb := distinctUniformProbability_pos (by omega : 0 < n) hmn
  have hgmle : (g : ℝ) ≤ m := by
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < m) hgm
  let L : ℝ := (2*(m : ℝ)*(n : ℝ)^2/(3*(g : ℝ)^2))*
    (1+((n : ℝ)-1)*dittertConstant m/distinctUniformProbability n m)
  obtain ⟨hb4, hL, hLb, hscalar⟩ := endpoint_scaling_parameter_bounds
    (by exact_mod_cast hm) (by exact_mod_cast hn) (by exact_mod_cast hg) hgmle ha hb hcriterion
  change 0 < L at hL
  change L*distinctUniformProbability n m < 1 at hLb
  change (m : ℝ)^2*distinctUniformProbability n m*L/4 <
    (16/17 : ℝ)^2/(3*((n : ℝ)-1)^2) at hscalar
  obtain ⟨_hdr, _hdc, _hbudget, hd, hdb⟩ :=
    endpoint_contender_deficit_budget (by omega) hmn hP hcont
  let t : ℝ := Real.sqrt (L*endpointRookDeficit P)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t^2 = L*endpointRookDeficit P := Real.sq_sqrt (mul_nonneg hL.le hd)
  have ht1 : t < 1 := by
    have h := (mul_le_mul_of_nonneg_left hdb hL.le).trans_lt hLb
    nlinarith only [htsq, h, ht]
  have hdev (I : Finset (Fin m)) (J : Finset (Fin n)) :
      |(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)| +
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)| ≤ t*(g : ℝ)/((m : ℝ)*n) := by
    have hs := endpoint_contender_subset_discrepancy_sq hm hmn hP hcont hb4.le I J
    have hid : (t*(g : ℝ)/((m : ℝ)*n))^2 =
        (2/(3*(m : ℝ)))*(1+((n : ℝ)-1)*dittertConstant m/distinctUniformProbability n m)*
          endpointRookDeficit P := by
      calc
        _ = t^2*(g : ℝ)^2/((m : ℝ)^2*(n : ℝ)^2) := by ring
        _ = _ := by
          rw [htsq]
          dsimp [L]
          field_simp
    have hright : 0 ≤ t*(g : ℝ)/((m : ℝ)*n) := by positivity
    nlinarith only [hs, hid, hright]
  obtain ⟨B, hB, hr, hc, hdom⟩ := exists_balanced_dominated_of_subset_discrepancy
    (by omega) (by omega) hgm hgn hP ht ht1 hdev
  have hrook := endpointRookRatio_boundary_lower_bound_of_boundary_domination
    (by omega) (by omega) hmn hB.1 hr hc hz ht1 hdom
  have hk : 0 < boundaryPermanentRatio n :=
    div_pos (boundaryPermanentFloor_pos (by omega)) (endpoint_a_pos (by omega))
  apply endpoint_boundary_scaling_contradiction hb hk hL.le hd ht ht1.le htsq
    (hscalar.trans (boundaryPermanentRatio_gap hn))
  simpa only [endpointRookDeficit, sub_sub_cancel] using hrook

/-- Full sharp endpoint inequality and uniform iff equality under a common-divisor criterion. -/
theorem uniform_maximum_endpoint_of_arithmetic_criterion {m n g : ℕ}
    (hm : 3 ≤ m) (hn : 18 ≤ n) (hmn : m ≤ n) (hg : 1 ≤ g)
    (hgm : g ∣ m) (hgn : g ∣ n)
    (hcriterion : distinctUniformProbability n m+((n : ℝ)-1)*dittertConstant m <
      (512/289)*(g : ℝ)^2/((m : ℝ)^3*(n : ℝ)^2*((n : ℝ)-1)^2)) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  have hmain : UniformMaximizer m n m := by
    apply uniform_maximizer_of_all_global_positive (by omega) le_rfl hmn
    intro P hP hmax i j
    by_contra hnot
    have hz : P i j = 0 := le_antisymm (le_of_not_gt hnot) (hP.1 i j)
    have hcont := hmax (uniformBoard m n) (uniformBoard_isProbability (by omega) (by omega))
    rw [separationProbability_uniform (by omega) (by omega)] at hcont
    exact endpoint_boundary_contender_impossible_of_arithmetic hm hn hmn hg hgm hgn
      hcriterion hP hcont ⟨i,j,hz⟩
  exact ⟨hmain, hmain.transpose⟩

theorem uniform_maximum_endpoint_of_boundary_criterion {m n : ℕ}
    (hm : 3 ≤ m) (hn : 18 ≤ n) (hmn : m ≤ n)
    (hcriterion : distinctUniformProbability n m+((n : ℝ)-1)*dittertConstant m <
      (512/289)/((m : ℝ)^3*(n : ℝ)^2*((n : ℝ)-1)^2)) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  apply uniform_maximum_endpoint_of_arithmetic_criterion hm hn hmn
    (by decide : 1 ≤ 1) (one_dvd m) (one_dvd n)
  simpa only [Nat.cast_one, one_pow, mul_one] using hcriterion

end DittertRybin
