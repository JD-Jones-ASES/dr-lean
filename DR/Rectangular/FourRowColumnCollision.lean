import DR.Collision.FirstMoment
import Mathlib.Analysis.Real.Sqrt

/-! The unrestricted four-sample column-collision correction, including all equality patterns. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def fourSampleEqualPairCount {α : Type*} [DecidableEq α] (s : Fin 4 → α) : ℝ :=
  ∑ e : SampleIndexPair 4, if s e.val.1 = s e.val.2 then 1 else 0

noncomputable def fourSampleCollisionExcess {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ := by
  classical
  exact ∑ s : Fin 4 → α, sampleMass p s *
    (fourSampleEqualPairCount s - if Function.Injective s then 0 else 1)

private theorem fourSampleEqualPairCount_expand {α : Type*} [DecidableEq α] (s : Fin 4 → α) :
    fourSampleEqualPairCount s =
      (if s 0=s 1 then 1 else 0)+(if s 0=s 2 then 1 else 0)+(if s 0=s 3 then 1 else 0)+
      (if s 1=s 2 then 1 else 0)+(if s 1=s 3 then 1 else 0)+(if s 2=s 3 then 1 else 0) := by
  let e : Fin 6 → SampleIndexPair 4 :=
    ![⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(0,3),by decide⟩,
      ⟨(1,2),by decide⟩,⟨(1,3),by decide⟩,⟨(2,3),by decide⟩]
  have he : Function.Bijective e := by decide
  rw [fourSampleEqualPairCount, ← (Equiv.ofBijective e he).sum_comp]
  simp only [Equiv.ofBijective_apply, e, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  simp only [add_assoc]
  by_cases h01 : s 0=s 1 <;> by_cases h02 : s 0=s 2 <;> by_cases h03 : s 0=s 3 <;>
    by_cases h12 : s 1=s 2 <;> by_cases h13 : s 1=s 3 <;> by_cases h23 : s 2=s 3 <;>
    simp only [h01,h02,h03,h12,h13,h23,if_true,if_false]

private theorem injective_four_iff {α : Type*} (s : Fin 4 → α) :
    Function.Injective s ↔ s 0≠s 1 ∧ s 0≠s 2 ∧ s 0≠s 3 ∧ s 1≠s 2 ∧ s 1≠s 3 ∧ s 2≠s 3 := by
  constructor
  · intro h
    exact ⟨h.ne (by decide),h.ne (by decide),h.ne (by decide),h.ne (by decide),h.ne (by decide),h.ne (by decide)⟩
  · rintro ⟨h01,h02,h03,h12,h13,h23⟩ i j he
    fin_cases i <;> fin_cases j <;> simp_all

/-- The six-pair count minus the collision indicator equals twice the four triple
indicators plus the three matching indicators minus six times the all-equal indicator. -/
theorem fourSample_collision_excess_indicator {α : Type*} [DecidableEq α] (s : Fin 4 → α) :
    (fourSampleEqualPairCount s - if Function.Injective s then 0 else 1) =
    2*((if s 0=s 1 ∧ s 0=s 2 then (1:ℝ) else 0)+
      (if s 0=s 1 ∧ s 0=s 3 then 1 else 0)+
      (if s 0=s 2 ∧ s 0=s 3 then 1 else 0)+
      (if s 1=s 2 ∧ s 1=s 3 then 1 else 0))+
    ((if s 0=s 1 ∧ s 2=s 3 then 1 else 0)+
      (if s 0=s 2 ∧ s 1=s 3 then 1 else 0)+
      (if s 0=s 3 ∧ s 1=s 2 then 1 else 0))-
    6*(if s 0=s 1 ∧ s 0=s 2 ∧ s 0=s 3 then 1 else 0) := by
  classical
  simp only [fourSampleEqualPairCount_expand, injective_four_iff]
  by_cases h01 : s 0=s 1 <;> by_cases h02 : s 0=s 2 <;> by_cases h03 : s 0=s 3 <;>
    by_cases h12 : s 1=s 2 <;> by_cases h13 : s 1=s 3 <;> by_cases h23 : s 2=s 3 <;>
    simp_all [eq_comm]
  all_goals norm_num

/-- The excess is pointwise nonnegative, without any probability hypothesis. -/
theorem fourSample_collision_excess_nonneg {α : Type*} [DecidableEq α] (s : Fin 4 → α) :
    0 ≤ fourSampleEqualPairCount s - if Function.Injective s then 0 else 1 := by
  classical
  simp only [fourSampleEqualPairCount_expand, injective_four_iff]
  by_cases h01 : s 0=s 1 <;> by_cases h02 : s 0=s 2 <;> by_cases h03 : s 0=s 3 <;>
    by_cases h12 : s 1=s 2 <;> by_cases h13 : s 1=s 3 <;> by_cases h23 : s 2=s 3 <;>
    simp_all [eq_comm]
  all_goals norm_num

private def sampleFourEquiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun s := (s 0,s 1,s 2,s 3)
  invFun a := ![a.1,a.2.1,a.2.2.1,a.2.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

private theorem sum_sample_four {α : Type*} [Fintype α] (f : (Fin 4 → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := by
  rw [← (sampleFourEquiv α).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem sum_four_triple_pattern {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, if a=b ∧ a=c then p a*p b*p c*p d else 0) =
      (∑ a, p a^3)*(∑ d, p d) := by
  have he (a b c d : α) : (if a=b ∧ a=c then p a*p b*p c*p d else 0) =
      (if a=b ∧ a=c then p a*p b*p c else 0)*p d := by split_ifs <;> simp
  simp_rw [he, ← Finset.mul_sum, ← Finset.sum_mul]
  simp [ite_and, pow_succ]

/-- Exact signed homogeneous formula; the cubic moment retains its total-mass factor. -/
theorem fourSampleCollisionExcess_formula {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) :
    fourSampleCollisionExcess p = 8*(∑ a,p a)*(∑ a,p a^3)+3*(∑ a,p a^2)^2-6*(∑ a,p a^4) := by
  classical
  unfold fourSampleCollisionExcess
  simp_rw [fourSample_collision_excess_indicator]
  rw [sum_sample_four]
  simp only [sampleMass, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    mul_sub, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- Reduce equality constraints before summing the unrestricted coordinates.
  simp [ite_and, ← Finset.mul_sum, ← Finset.sum_mul, pow_succ]
  ring_nf
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  simp only [← Finset.mul_sum]
  ring

/-- The correction is the actual weighted six-pair count minus the actual collision event mass. -/
theorem fourSampleCollisionExcess_eq_sum_sub_eventMass {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : fourSampleCollisionExcess p =
      (∑ s : Fin 4 → α, sampleMass p s * fourSampleEqualPairCount s) -
        eventMass p {s : Fin 4 → α | ¬ Function.Injective s} := by
  classical
  simp only [fourSampleCollisionExcess, mul_sub, Finset.sum_sub_distrib,
    eventMass, Set.mem_ofPred_eq, mul_ite, mul_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Function.Injective s <;> simp only [hs, not_true_eq_false, not_false_eq_true, if_true, if_false]

/-- Weighted Cauchy gives the cubic-moment bound, including zero weights and zero total mass. -/
theorem fourSample_squareMoment_sq_le {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    (∑ a,p a^2)^2 ≤ (∑ a,p a^3)*(∑ a,p a) := by
  have hf (a : α) : (p a * Real.sqrt (p a))^2 = p a^3 := by
    rw [mul_pow, Real.sq_sqrt (hp a)]
    ring
  have hg (a : α) : Real.sqrt (p a)^2 = p a := Real.sq_sqrt (hp a)
  have hprod (a : α) : (p a * Real.sqrt (p a))*Real.sqrt (p a) = p a^2 := by
    rw [mul_assoc, ← pow_two, hg]
    ring
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => p a * Real.sqrt (p a)) (fun a => Real.sqrt (p a))
  simpa only [hf,hg,hprod] using h

/-- For every finite probability law, the unrestricted column correction lies in [0,11∑p³]. -/
theorem fourSampleCollisionExcess_bounds {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a,p a=1) :
    0 ≤ fourSampleCollisionExcess p ∧ fourSampleCollisionExcess p ≤ 11*(∑ a,p a^3) := by
  classical
  constructor
  · unfold fourSampleCollisionExcess
    exact Finset.sum_nonneg fun s _ => mul_nonneg (sampleMass_nonneg p hp s)
      (fourSample_collision_excess_nonneg s)
  · rw [fourSampleCollisionExcess_formula, hmass]
    have hsecond := fourSample_squareMoment_sq_le p hp
    rw [hmass,mul_one] at hsecond
    have hfour : 0 ≤ ∑ a,p a^4 := Finset.sum_nonneg fun a _ => pow_nonneg (hp a) 4
    nlinarith only [hsecond,hfour]

end DittertRybin
