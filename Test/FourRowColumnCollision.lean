import DR.Rectangular.FourRowColumnCollision

namespace DittertRybin.Tests
open scoped BigOperators

-- Five partition shapes: distinct, one pair, two pairs, a triple, and all four equal.
example : fourSampleEqualPairCount (![0,1,2,3] : Fin 4 → Fin 4) -
    (if Function.Injective (![0,1,2,3] : Fin 4 → Fin 4) then 0 else 1) = 0 := by
  rw [fourSample_collision_excess_indicator]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

example : fourSampleEqualPairCount (![0,0,1,2] : Fin 4 → Fin 4) -
    (if Function.Injective (![0,0,1,2] : Fin 4 → Fin 4) then 0 else 1) = 0 := by
  rw [fourSample_collision_excess_indicator]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

example : fourSampleEqualPairCount (![0,0,1,1] : Fin 4 → Fin 4) -
    (if Function.Injective (![0,0,1,1] : Fin 4 → Fin 4) then 0 else 1) = 1 := by
  rw [fourSample_collision_excess_indicator]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

example : fourSampleEqualPairCount (![0,0,0,1] : Fin 4 → Fin 4) -
    (if Function.Injective (![0,0,0,1] : Fin 4 → Fin 4) then 0 else 1) = 2 := by
  rw [fourSample_collision_excess_indicator]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

example : fourSampleEqualPairCount (![0,0,0,0] : Fin 4 → Fin 4) -
    (if Function.Injective (![0,0,0,0] : Fin 4 → Fin 4) then 0 else 1) = 5 := by
  rw [fourSample_collision_excess_indicator]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff]

-- A negative unnormalized single weight detects omission of the total-mass factor.
example : fourSampleCollisionExcess (fun _ : Unit => (-2 : ℝ)) = 80 := by
  rw [fourSampleCollisionExcess_formula]
  norm_num

example : fourSampleCollisionExcess (fun _ : Fin 4 => (1/4 : ℝ)) = 19/32 := by
  rw [fourSampleCollisionExcess_formula]
  norm_num

example : fourSampleCollisionExcess (fun _ : Fin 0 => (3 : ℝ)) = 0 := by
  rw [fourSampleCollisionExcess_formula]
  norm_num

-- Zero outcome weights remain valid in the probability bound.
example : 0 ≤ fourSampleCollisionExcess (fun i : Fin 2 => if i.val=0 then (1:ℝ) else 0) ∧
    fourSampleCollisionExcess (fun i : Fin 2 => if i.val=0 then (1:ℝ) else 0) ≤ 11 := by
  have h := fourSampleCollisionExcess_bounds (fun i : Fin 2 => if i.val=0 then (1:ℝ) else 0)
    (by intro i; split <;> norm_num) (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ] using h

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a,p a=1) :
    (∑ s : Fin 4 → α, sampleMass p s * fourSampleEqualPairCount s) -
      eventMass p {s : Fin 4 → α | ¬ Function.Injective s} ≤ 11*(∑ a,p a^3) := by
  rw [← fourSampleCollisionExcess_eq_sum_sub_eventMass]
  exact (fourSampleCollisionExcess_bounds p hp hmass).2

#print axioms fourSample_collision_excess_indicator
#print axioms fourSampleCollisionExcess_formula
#print axioms fourSampleCollisionExcess_eq_sum_sub_eventMass
#print axioms fourSampleCollisionExcess_bounds
end DittertRybin.Tests
