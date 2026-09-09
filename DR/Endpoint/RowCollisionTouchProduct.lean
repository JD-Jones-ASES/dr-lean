import DR.Endpoint.RowCollisionSelectedEvents
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Exact touching-edge product bounds for selected-row collision patterns.
Concavity supplies the closed chord bound on [0,1/4]; finite incidence
counting then gives a constant depending on the number of selected rows,
not on the total collision intensity. -/

namespace DittertRybin
open scoped BigOperators

/-- The closed chord bound used for the local-lemma parameters. -/
theorem log_one_sub_chord_quarter (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/4) :
    4*x*Real.log (3/4) ≤ Real.log (1-x) := by
  have h : (4*x)*Real.log (3/4)+(1-4*x)*Real.log 1 ≤
      Real.log ((4*x)*(3/4)+(1-4*x)*1) :=
    strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by ring)
  simp only [Real.log_one,mul_zero,add_zero] at h
  convert h using 1
  congr 1
  ring

/-- A complement product with x<=1/4 and sum x<=s/4 is at least (3/4)^s. -/
theorem product_one_sub_ge_three_quarters_pow {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (s : ℕ) (hx : ∀ e ∈ S, 0 ≤ x e ∧ x e ≤ 1/4)
    (hs : (∑ e ∈ S, x e) ≤ (s:ℝ)/4) :
    (3/4:ℝ)^s ≤ ∏ e ∈ S, (1-x e) := by
  have hp (e) (he : e ∈ S) : 0 < 1-x e := by linarith [(hx e he).2]
  have hprod : 0 < ∏ e ∈ S, (1-x e) := Finset.prod_pos hp
  apply (Real.log_le_log_iff (pow_pos (by norm_num) s) hprod).mp
  rw [Real.log_pow,Real.log_prod (fun e he => (hp e he).ne')]
  have hl : Real.log (3/4:ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hsum := Finset.sum_le_sum (fun e he => log_one_sub_chord_quarter (x e) (hx e he).1 (hx e he).2)
  have hs' : 4*(∑ e ∈ S, x e) ≤ (s:ℝ) := by linarith
  have hmul := mul_le_mul_of_nonpos_right hs' hl
  calc
    (s:ℝ)*Real.log (3/4) ≤ (4*(∑ e ∈ S, x e))*Real.log (3/4) := hmul
    _ = ∑ e ∈ S, 4*x e*Real.log (3/4) := by rw [← Finset.sum_mul,← Finset.mul_sum]
    _ ≤ _ := hsum

/-- The full touching-edge product depends only on the selected row count. -/
theorem rowCollisionTouch_product_lower {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hd : ∀ i, rowCollisionLoad X i ≤ 1/8)
    (V : Finset (Fin m)) :
    (3/4:ℝ)^V.card ≤
      ∏ e ∈ rowCollisionTouch V, (1-2*rowCollisionProbability X e.val.1 e.val.2) := by
  have hcap (e : SampleIndexPair m) : 0 ≤ 2*rowCollisionProbability X e.val.1 e.val.2 ∧
      2*rowCollisionProbability X e.val.1 e.val.2 ≤ 1/4 := by
    have hp := rowCollisionProbability_nonneg X hX e.val.1 e.val.2
    have he := (rowCollisionProbability_le_load X hX e).trans (hd e.val.1)
    constructor <;> linarith
  apply product_one_sub_ge_three_quarters_pow (rowCollisionTouch V)
    (fun e => 2*rowCollisionProbability X e.val.1 e.val.2) V.card (fun e _ => hcap e)
  rw [← Finset.mul_sum]
  have hl := rowCollisionTouch_load_le X hX V
  have hs : (∑ i ∈ V, rowCollisionLoad X i) ≤ (V.card:ℝ)/8 := by
    calc
      _ ≤ ∑ _i ∈ V, (1/8:ℝ) := Finset.sum_le_sum (fun i _ => hd i)
      _ = _ := by simp; ring
  linarith

/-- A prescribed selected-row event with removed internal edges has a
relative probability bounded by (4/3) to the selected row count. -/
theorem rowSelectedEvent_removed_edges_ratio {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (V : Finset (Fin m))
    (A : Set ({i // i ∈ V} → Fin n)) (L : Finset (SampleIndexPair m))
    (hL : L ⊆ rowCollisionTouch V) :
    rowAssignmentEvent X {z | RowSelectedEvent V A z ∧ ∀ e ∈ Finset.univ \ L, ¬RowCollisionEvent e z}/
      rowAvoidance X ≤ (4/3:ℝ)^V.card*rowAssignmentEvent X {z | RowSelectedEvent V A z} := by
  have h := rowSelectedEvent_removed_edges_bound X hX hs hd V A L hL
  have hp := rowCollisionTouch_product_lower X hX hd V
  have hn := rowAssignmentEvent_nonneg X hX
    {z | RowSelectedEvent V A z ∧ ∀ e ∈ Finset.univ \ L, ¬RowCollisionEvent e z}
  have hscaled := (mul_le_mul_of_nonneg_left hp hn).trans h
  have hav := rowAvoidance_pos_of_collisionLoad X hX hs hd
  have hfactor : (4/3:ℝ)^V.card*(3/4:ℝ)^V.card=1 := by
    rw [← mul_pow]
    norm_num
  apply (div_le_iff₀ hav).mpr
  have hfactorpos : 0 < (4/3:ℝ)^V.card := pow_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hscaled hfactorpos.le
  calc
    _ = ((4/3:ℝ)^V.card*(3/4:ℝ)^V.card)*
        rowAssignmentEvent X {z | RowSelectedEvent V A z ∧ ∀ e ∈ Finset.univ \ L, ¬RowCollisionEvent e z} := by
      rw [hfactor,one_mul]
    _ = (4/3:ℝ)^V.card*(rowAssignmentEvent X
        {z | RowSelectedEvent V A z ∧ ∀ e ∈ Finset.univ \ L, ¬RowCollisionEvent e z}*(3/4:ℝ)^V.card) := by ring
    _ ≤ _ := by simpa only [mul_assoc] using hmul

end DittertRybin
