import DR.Endpoint.RowCollisionLocalLemma
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The refined local-lemma product gives the exact logarithmic collision
bound from P0174 ENDPOINT_ALL_ASPECT_RATIOS_LARGE_M, equation (10). The
denominator 1-5d is retained. No Poisson approximation is assumed. -/

namespace DittertRybin
open scoped BigOperators

/-- An exact scalar upper bound for the complement logarithm. -/
theorem neg_log_one_sub_le_div (x : ℝ) (hx : x < 1) :
    -Real.log (1-x) ≤ x/(1-x) := by
  have hp : 0 < 1-x := sub_pos.mpr hx
  have h := neg_le_neg (Real.one_sub_inv_le_log_of_pos hp)
  apply h.trans_eq
  field_simp
  ring

/-- A finite product estimate with a uniform upper bound on each x. -/
theorem neg_log_product_one_sub_le {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (a : ℝ) (ha : a < 1) (hx : ∀ e ∈ S, 0 ≤ x e ∧ x e ≤ a) :
    -Real.log (∏ e ∈ S, (1-x e)) ≤ (∑ e ∈ S, x e)/(1-a) := by
  have hp (e) (he : e ∈ S) : 0 < 1-x e := sub_pos.mpr ((hx e he).2.trans_lt ha)
  rw [Real.log_prod (fun e he => (hp e he).ne'),← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro e he
  apply (neg_log_one_sub_le_div (x e) ((hx e he).2.trans_lt ha)).trans
  exact div_le_div_of_nonneg_left (hx e he).1 (sub_pos.mpr ha) (by linarith [(hx e he).2])

/-- Actual collision avoidance satisfies the source's logarithmic bound.
The local load is small; the total collision intensity may be arbitrarily large. -/
theorem neg_log_rowAvoidance_le {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 1/8)
    (hload : ∀ i, rowCollisionLoad X i ≤ d) :
    -Real.log (rowAvoidance X) ≤ rowCollisionIntensity X/(1-5*d) := by
  have hq : 0 < 1-4*d := by linarith
  have hr : 0 < 1-5*d := by linarith
  obtain ⟨hc,hcd,hguard⟩ := rowCollision_refined_guards d hd0 hd
  have ha : d/(1-4*d) < 1 := by simpa only [one_div_mul_eq_div] using hcd
  have hx (e : SampleIndexPair m) : 0 ≤ rowCollisionProbability X e.val.1 e.val.2/(1-4*d) ∧
      rowCollisionProbability X e.val.1 e.val.2/(1-4*d) ≤ d/(1-4*d) := by
    exact ⟨div_nonneg (rowCollisionProbability_nonneg X hX _ _) hq.le,
      div_le_div_of_nonneg_right ((rowCollisionProbability_le_load X hX e).trans (hload _)) hq.le⟩
  have hp : 0 < ∏ e : SampleIndexPair m,
      (1-rowCollisionProbability X e.val.1 e.val.2/(1-4*d)) :=
    Finset.prod_pos (fun e _ => sub_pos.mpr ((hx e).2.trans_lt ha))
  have hl := neg_le_neg (Real.log_le_log hp (rowAvoidance_lower_refinedProduct X hX hs d hd0 hd hload))
  have hb := neg_log_product_one_sub_le Finset.univ
    (fun e : SampleIndexPair m => rowCollisionProbability X e.val.1 e.val.2/(1-4*d))
    (d/(1-4*d)) ha (fun e _ => hx e)
  rw [← Finset.sum_div,← rowCollisionIntensity_eq_sum_edges] at hb
  have heq : (rowCollisionIntensity X/(1-4*d))/(1-d/(1-4*d)) =
      rowCollisionIntensity X/(1-5*d) := by
    field_simp
    ring
  exact (hl.trans hb).trans_eq heq

/-- Equivalent exponential lower bound, for the actual row-avoidance event. -/
theorem exp_neg_collisionIntensity_le_rowAvoidance {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 1/8)
    (hload : ∀ i, rowCollisionLoad X i ≤ d) :
    Real.exp (-rowCollisionIntensity X/(1-5*d)) ≤ rowAvoidance X := by
  have hpos := rowAvoidance_pos_of_collisionLoad X hX hs (fun i => (hload i).trans hd)
  have h := neg_log_rowAvoidance_le X hX hs d hd0 hd hload
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith

end DittertRybin
