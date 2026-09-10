import DR.Endpoint.ElementaryLowerBound
import DR.Endpoint.RowProduct
import DR.Collision.Averaging

/-! A linear collision lower bound for the actual elementary coefficient
after two column labels have been removed. The ordered-injection recurrence
retains every empty and zero-coordinate case. -/
namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem endpoint_embedding_sum_le_one {d k : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i,0≤x i) (hs : ∑ i,x i≤1) :
    (∑ e : Fin k ↪ Fin d,∏ i,x (e i))≤1 := by
  change rowAvoidance (fun _ : Fin k => x)≤1
  rw [rowAvoidance_eq_event]
  have h := rowAssignmentEvent_le_total (fun _ : Fin k => x) (fun _ j => hx j)
    {z | Function.Injective z}
  apply h.trans
  simp only [rowSum,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact pow_le_one₀ (Finset.sum_nonneg (fun i _ => hx i)) hs

/-- Linear union estimate for distinct samples from a subprobability vector. -/
theorem endpoint_elementary_lower_two_lost {d k : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i,0≤x i) {C : ℝ} (hC : 0≤C) (hc : ∀ i,x i≤C)
    (hs : ∑ i,x i≤1) (hlo : 1-2*C≤∑ i,x i) :
    1-((k:ℝ)*((k:ℝ)+3)/2)*C≤(k.factorial:ℝ)*elementarySymmetric x k := by
  rw [← sum_embeddings_eq_factorial_elementary]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_embeddings_successor]
    have hstep : (∑ e : Fin k ↪ Fin d,∏ i,x (e i))*(1-((k:ℝ)+2)*C)≤
        ∑ e : Fin k ↪ Fin d,(∏ i,x (e i))*((∑ a,x a)-(∑ i,x (e i))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => hx (e i)))
      have he : (∑ i,x (e i))≤(k:ℝ)*C := by
        simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
          using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hc (e i))
      linarith
    have hupper := endpoint_embedding_sum_le_one (k:=k) x hx hs
    have hterm : 0≤((k:ℝ)+2)*C := by positivity
    have hmul := mul_le_mul_of_nonneg_left hupper hterm
    have hcoeff : (((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+3)/2)=
        (k:ℝ)*((k:ℝ)+3)/2+((k:ℝ)+2) := by push_cast; ring
    rw [hcoeff]
    nlinarith only [ih,hstep,hmul]

/-- Removing two actual columns loses at most twice the original coordinate cap. -/
theorem endpoint_deleted_elementary_lower {d k : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i,0≤x i) (hs : ∑ i,x i=1) {C : ℝ} (hC : 0≤C) (hc : ∀ i,x i≤C)
    (a b : Fin d) (hab : a≠b) :
    1-((k:ℝ)*((k:ℝ)+3)/2)*C≤
      (k.factorial:ℝ)*elementarySymmetric (fun i => if i∈({a,b}:Finset (Fin d)) then 0 else x i) k := by
  classical
  let y : Fin d → ℝ := fun i => if i∈({a,b}:Finset (Fin d)) then 0 else x i
  have he : (∑ i,y i)=1-x a-x b := by
    have hi (i : Fin d) : y i=x i-(if i=a then x a else 0)-(if i=b then x b else 0) := by
      by_cases ha : i=a <;> by_cases hb : i=b <;> simp_all [y]
    simp only [hi,Finset.sum_sub_distrib,hs,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  apply endpoint_elementary_lower_two_lost y
  · intro i
    dsimp [y]
    split_ifs
    · exact le_rfl
    · exact hx i
  · exact hC
  · intro i
    dsimp [y]
    split_ifs
    · exact hC
    · exact hc i
  · rw [he]
    linarith [hx a,hx b]
  · rw [he]
    linarith [hc a,hc b]

end DittertRybin
