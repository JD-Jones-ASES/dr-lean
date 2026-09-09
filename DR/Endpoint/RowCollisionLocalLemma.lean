import DR.Endpoint.RowCollisionGraph
import DR.Endpoint.FiniteLocalLemma

/-! The finite local lemma applied to the actual independent row law.
The neighborhood condition is derived from collision loads. Sparse rows
and zero collision probabilities remain in the event family. -/

namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Elementary complement-product lower bound, including closed endpoints. -/
theorem rowCollision_one_sub_sum_le_product_one_sub {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ e ∈ S, 0 ≤ x e ∧ x e ≤ 1) :
    1 - ∑ e ∈ S, x e ≤ ∏ e ∈ S, (1 - x e) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert e S he ih =>
    have heX := hx e (Finset.mem_insert_self e S)
    have hSX : ∀ f ∈ S, 0 ≤ x f ∧ x f ≤ 1 := fun f hf => hx f (Finset.mem_insert_of_mem hf)
    have hsum : 0 ≤ ∑ f ∈ S, x f := Finset.sum_nonneg fun f hf => (hSX f hf).1
    have hmul := mul_le_mul_of_nonneg_left (ih hSX) (sub_nonneg.mpr heX.2)
    rw [Finset.sum_insert he,Finset.prod_insert he]
    nlinarith [mul_nonneg heX.1 hsum]

/-- The scaled edge parameters satisfy the asymmetric local-lemma condition.
The numerical premises are scalar load guards, not probability conclusions. -/
theorem rowCollision_scaled_parameters {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (d c : ℝ)
    (hd : ∀ i, rowCollisionLoad X i ≤ d) (hc : 0 ≤ c)
    (hcd : c*d < 1) (hguard : 1 ≤ c*(1-2*c*d)) :
    (∀ e : SampleIndexPair m, 0 ≤ c*rowCollisionProbability X e.val.1 e.val.2 ∧
      c*rowCollisionProbability X e.val.1 e.val.2 < 1) ∧
    (∀ e : SampleIndexPair m, rowCollisionProbability X e.val.1 e.val.2 ≤
      (c*rowCollisionProbability X e.val.1 e.val.2)*
        (∏ f ∈ rowCollisionNeighbors e, (1-c*rowCollisionProbability X f.val.1 f.val.2))) := by
  have hx (e : SampleIndexPair m) : 0 ≤ c*rowCollisionProbability X e.val.1 e.val.2 ∧
      c*rowCollisionProbability X e.val.1 e.val.2 < 1 := by
    refine ⟨mul_nonneg hc (rowCollisionProbability_nonneg X hX _ _),?_⟩
    exact (mul_le_mul_of_nonneg_left
      ((rowCollisionProbability_le_load X hX e).trans (hd e.val.1)) hc).trans_lt hcd
  refine ⟨hx,?_⟩
  intro e
  have hsum : (∑ f ∈ rowCollisionNeighbors e,
      c*rowCollisionProbability X f.val.1 f.val.2) ≤ 2*c*d := by
    rw [← Finset.mul_sum]
    have h := (rowCollisionNeighbors_load_le X hX e).trans (add_le_add (hd _) (hd _))
    nlinarith [mul_le_mul_of_nonneg_left h hc]
  have hprod := rowCollision_one_sub_sum_le_product_one_sub (rowCollisionNeighbors e)
    (fun f => c*rowCollisionProbability X f.val.1 f.val.2) (fun f _ => ⟨(hx f).1,(hx f).2.le⟩)
  have hlow : 1-2*c*d ≤ ∏ f ∈ rowCollisionNeighbors e,
      (1-c*rowCollisionProbability X f.val.1 f.val.2) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hguard (rowCollisionProbability_nonneg X hX e.val.1 e.val.2)
  have h2 := mul_le_mul_of_nonneg_left hlow (hx e).1
  nlinarith

/-- Under the scalar guards, every actual avoidance family has positive
mass and every remaining edge obeys its conditional bound. -/
theorem rowCollision_local_lemma_scaled {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1) (d c : ℝ)
    (hd : ∀ i, rowCollisionLoad X i ≤ d) (hc : 0 ≤ c)
    (hcd : c*d < 1) (hguard : 1 ≤ c*(1-2*c*d))
    (S : Finset (SampleIndexPair m)) :
    0 < rowAssignmentEvent X {z | ∀ e ∈ S, ¬RowCollisionEvent e z} ∧
      ∀ e ∉ S, rowAssignmentEvent X {z | RowCollisionEvent e z ∧ ∀ f ∈ S, ¬RowCollisionEvent f z} ≤
        (c*rowCollisionProbability X e.val.1 e.val.2)*
          rowAssignmentEvent X {z | ∀ f ∈ S, ¬RowCollisionEvent f z} := by
  classical
  obtain ⟨hx,hlll⟩ := rowCollision_scaled_parameters X hX d c hd hc hcd hguard
  have hmass : ∑ z, rowAssignmentMass X z=1 := by
    rw [sum_rowAssignmentMass]
    simp only [hs,Finset.prod_const_one]
  have h := FiniteEvents.finite_conditional_local_lemma Finset.univ (rowAssignmentMass X)
    RowCollisionEvent rowCollisionNeighbors (fun e => c*rowCollisionProbability X e.val.1 e.val.2)
    (fun z _ => rowAssignmentMass_nonneg X hX z) hmass hx
    (rowCollision_joint_independence X hs)
    (by intro e; rw [rowCollisionEvent_mass]; exact hlll e) S
  simpa only [rowAssignmentEvent_eq_finiteMass,Set.mem_ofPred_eq,
    FiniteEvents.avoidanceMass,FiniteEvents.hitAvoidanceMass] using h

/-- The local load bound one eighth supplies actual conditional collision
bounds with parameter twice the unconditioned edge probability. -/
theorem rowCollision_local_lemma {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) (S : Finset (SampleIndexPair m)) :
    0 < rowAssignmentEvent X {z | ∀ e ∈ S, ¬RowCollisionEvent e z} ∧
      ∀ e ∉ S, rowAssignmentEvent X {z | RowCollisionEvent e z ∧ ∀ f ∈ S, ¬RowCollisionEvent f z} ≤
        (2*rowCollisionProbability X e.val.1 e.val.2)*
          rowAssignmentEvent X {z | ∀ f ∈ S, ¬RowCollisionEvent f z} :=
  rowCollision_local_lemma_scaled X hX hs (1/8) 2 hd (by norm_num) (by norm_num) (by norm_num) S

/-- Collision avoidance is positive without any small-total-intensity
assumption. Only the maximum local row load is controlled. -/
theorem rowAvoidance_pos_of_collisionLoad {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) : 0 < rowAvoidance X := by
  have h := (rowCollision_local_lemma X hX hs hd Finset.univ).1
  simpa only [Finset.mem_univ,forall_const,rowCollision_avoid_all_iff,
    ← rowAvoidance_eq_event] using h

/-- The product lower bound for every actual avoidance family. -/
theorem rowCollision_avoidance_product_scaled {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1) (d c : ℝ)
    (hd : ∀ i, rowCollisionLoad X i ≤ d) (hc : 0 ≤ c)
    (hcd : c*d < 1) (hguard : 1 ≤ c*(1-2*c*d))
    (S : Finset (SampleIndexPair m)) :
    (∏ e ∈ S, (1-c*rowCollisionProbability X e.val.1 e.val.2)) ≤
      rowAssignmentEvent X {z | ∀ e ∈ S, ¬RowCollisionEvent e z} := by
  classical
  obtain ⟨hx,hlll⟩ := rowCollision_scaled_parameters X hX d c hd hc hcd hguard
  have hmass : ∑ z, rowAssignmentMass X z=1 := by
    rw [sum_rowAssignmentMass]
    simp only [hs,Finset.prod_const_one]
  have h := FiniteEvents.finite_local_lemma_product Finset.univ (rowAssignmentMass X)
    RowCollisionEvent rowCollisionNeighbors (fun e => c*rowCollisionProbability X e.val.1 e.val.2)
    (fun z _ => rowAssignmentMass_nonneg X hX z) hmass hx
    (rowCollision_joint_independence X hs)
    (by intro e; rw [rowCollisionEvent_mass]; exact hlll e) S
  simpa only [rowAssignmentEvent_eq_finiteMass,Set.mem_ofPred_eq,
    FiniteEvents.avoidanceMass] using h

/-- An explicit positive product lower bound at the one-eighth local threshold. -/
theorem rowAvoidance_lower_collisionProduct {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (hd : ∀ i, rowCollisionLoad X i ≤ 1/8) :
    (∏ e : SampleIndexPair m, (1-2*rowCollisionProbability X e.val.1 e.val.2)) ≤
      rowAvoidance X := by
  have h := rowCollision_avoidance_product_scaled X hX hs (1/8) 2 hd
    (by norm_num) (by norm_num) (by norm_num) Finset.univ
  simpa only [Finset.mem_univ,forall_const,rowCollision_avoid_all_iff,
    ← rowAvoidance_eq_event] using h

/-- Exact guards for the transition parameter c=1/(1-4d), including d=0. -/
theorem rowCollision_refined_guards (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 1/8) :
    0 ≤ 1/(1-4*d) ∧ (1/(1-4*d))*d < 1 ∧
      1 ≤ (1/(1-4*d))*(1-2*(1/(1-4*d))*d) := by
  have hq : 0 < 1-4*d := by linarith
  have hmul : (1/(1-4*d))*(1-4*d)=1 := by field_simp
  have hc : 0 < 1/(1-4*d) := one_div_pos.mpr hq
  have hcd : (1/(1-4*d))*d < 1 := by
    have h := mul_lt_mul_of_pos_left (show d < 1-4*d by linarith) hc
    rwa [hmul] at h
  refine ⟨hc.le,hcd,?_⟩
  have hi : ((1/(1-4*d))*(1-2*(1/(1-4*d))*d)-1)*(1-4*d)^2 =
      2*d*(1-8*d) := by field_simp; ring
  have hn : 0 ≤ 2*d*(1-8*d) := mul_nonneg (by linarith) (by linarith)
  have hp := sq_pos_of_pos hq
  nlinarith

/-- The sharper local-lemma product, used before taking logarithms in the
transition range. No smallness assumption on the total intensity appears. -/
theorem rowAvoidance_lower_refinedProduct {m n : ℕ} (X : Board m n)
    (hX : ∀ i j, 0 ≤ X i j) (hs : ∀ i, rowSum X i=1)
    (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 1/8)
    (hload : ∀ i, rowCollisionLoad X i ≤ d) :
    (∏ e : SampleIndexPair m, (1-rowCollisionProbability X e.val.1 e.val.2/(1-4*d))) ≤
      rowAvoidance X := by
  obtain ⟨hc,hcd,hguard⟩ := rowCollision_refined_guards d hd0 hd
  have h := rowCollision_avoidance_product_scaled X hX hs d (1/(1-4*d)) hload hc hcd hguard Finset.univ
  simpa only [Finset.mem_univ,forall_const,rowCollision_avoid_all_iff,
    ← rowAvoidance_eq_event,one_div_mul_eq_div] using h

end DittertRybin
