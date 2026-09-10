import DR.Endpoint.UniformAvoidanceBound
import DR.Endpoint.LeadingEvent

/-! The exact uniform first-collision remainder. A finite scalar Bonferroni
inequality is applied to the genuine falling-factorial product. The result
retains the uniform correction needed in the contender comparison. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_product_bonferroni {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i∈S,0≤x i) (hx1 : ∀ i∈S,x i≤1) :
    1-S.sum x≤S.prod (fun i => 1-x i) ∧
    S.prod (fun i => 1-x i)≤1-S.sum x+((S.sum x)^2-S.sum (fun i => (x i)^2))/2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have h0 := hx a (Finset.mem_insert_self a S)
    have h1 := hx1 a (Finset.mem_insert_self a S)
    have hrest := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi => hx1 i (Finset.mem_insert_of_mem hi))
    have hsum : 0≤∑ i∈S,x i := Finset.sum_nonneg (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hlo := mul_le_mul_of_nonneg_left hrest.1 (sub_nonneg.mpr h1)
    have hsub := mul_le_mul_of_nonneg_left hrest.1 h0
    simp only [Finset.sum_insert ha,Finset.prod_insert ha]
    constructor
    · nlinarith only [hlo,mul_nonneg h0 hsum]
    · nlinarith only [hrest.2,hsub]

theorem endpoint_choose_two_real {m : ℕ} (hm : 2≤m) :
    (m.choose 2:ℝ)=(m:ℝ)*((m:ℝ)-1)/2 := by
  have h := congrArg (fun a : ℕ => (a:ℝ)) (Nat.descFactorial_eq_factorial_mul_choose m 2)
  simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,
    Nat.cast_mul,Nat.cast_sub (by omega : 1≤m),Nat.cast_one,mul_one] at h
  norm_num [Nat.factorial] at h
  linarith

theorem endpoint_pair_overlap_coefficient {m : ℕ} (hm : 2≤m) :
    (m.choose 2:ℝ)-1=((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)/2 := by
  rw [endpoint_choose_two_real hm,Nat.cast_sub hm]
  norm_num
  ring

/-- Both sides of the actual uniform collision remainder, with its exact denominator. -/
theorem endpoint_uniform_collision_remainder {m n : ℕ} (hm : 2≤m) (hn : 0<n) (hmn : m≤n) :
    0≤(m.choose 2:ℝ)/(n:ℝ)-(1-distinctUniformProbability n m) ∧
    (m.choose 2:ℝ)/(n:ℝ)-(1-distinctUniformProbability n m)≤
      (m.choose 2:ℝ)*(((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)/2)/(2*(n:ℝ)^2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have h := endpoint_product_bonferroni (Finset.range m) (fun i => (i:ℝ)/(n:ℝ))
    (fun i _ => by positivity) (fun i hi => by
      apply (div_le_one hnR).mpr
      exact_mod_cast (show i≤n by have := Finset.mem_range.mp hi; omega))
  have hs : (∑ i∈Finset.range m,(i:ℝ)/(n:ℝ))=(m.choose 2:ℝ)/(n:ℝ) := by
    rw [← Finset.sum_div,sum_range_real_eq_half,endpoint_choose_two_real hm]
  have hsq : (m.choose 2:ℝ)/(n:ℝ)^2≤∑ i∈Finset.range m,((i:ℝ)/(n:ℝ))^2 := by
    have hsum : (m.choose 2:ℝ)≤∑ i∈Finset.range m,(i:ℝ)^2 := by
      rw [endpoint_choose_two_real hm,← sum_range_real_eq_half]
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast (show i ≤ i ^ 2 by simpa only [pow_two] using Nat.le_mul_self i)
    have hd := div_le_div_of_nonneg_right hsum (sq_nonneg (n:ℝ))
    simpa only [Finset.sum_div,div_pow] using hd
  rw [hs,← distinctUniformProbability_eq_product hn hmn] at h
  constructor
  · linarith only [h.1]
  · have he : ((m.choose 2:ℝ)/(n:ℝ))^2-(m.choose 2:ℝ)/(n:ℝ)^2=
        (m.choose 2:ℝ)*((m.choose 2:ℝ)-1)/(n:ℝ)^2 := by
      field_simp
    rw [endpoint_pair_overlap_coefficient hm] at he
    have hdiv := (div_le_div_of_nonneg_right hsq (by norm_num : (0:ℝ)≤2))
    have he' : (m.choose 2:ℝ)*(((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)/2)/(2*(n:ℝ)^2)=
        (((m.choose 2:ℝ)/(n:ℝ))^2-(m.choose 2:ℝ)/(n:ℝ)^2)/2 := by
      rw [he]
      field_simp
    rw [he']
    linarith only [h.2,hdiv]

end DittertRybin
