import DR.Certificates.Gram
import Mathlib.Algebra.BigOperators.Field

/-! Ordered-pair weights for unordered multiplier certificates. Repeated cells
receive weight one and distinct ordered cells receive weight one half. -/
namespace DittertRybin.Certificates
open scoped BigOperators

noncomputable def unorderedPairWeight {α : Type*} [DecidableEq α] (a b : α) : ℝ :=
  if a=b then 1 else 1/2

theorem unorderedPairWeight_nonneg {α : Type*} [DecidableEq α] (a b : α) :
    0≤unorderedPairWeight a b := by
  unfold unorderedPairWeight
  split_ifs <;> norm_num

/-- Signed homogeneous identity, including an empty outcome type. -/
theorem sum_unorderedPairWeight {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) :
    (∑ a,∑ b,unorderedPairWeight a b*p a*p b)=((∑ a,p a)^2+(∑ a,p a^2))/2 := by
  have ht (a b : α) : unorderedPairWeight a b*p a*p b=
      (p a*p b+(if a=b then p a^2 else 0))/2 := by
    by_cases hab : a=b
    · subst b
      simp only [unorderedPairWeight,if_true]
      ring
    · simp only [unorderedPairWeight,if_neg hab]
      ring
  simp only [ht,← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_ite_eq,
    Finset.mem_univ,if_true,← Finset.mul_sum,← Finset.sum_mul]
  ring

/-- A common real quadratic floor gives half that stability constant at total mass one. -/
theorem weightedPair_quadratic_lower {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ a,0≤p a) (hmass : ∑ a,p a=1)
    (Q : α → α → Matrix α α ℝ) (x : α → ℝ) (c E : ℝ) (hc : 0≤c) (hE : 0≤E)
    (hQ : ∀ a b,c*E≤quadraticValue (Q a b) x) :
    (c/2)*E≤∑ a,∑ b,unorderedPairWeight a b*p a*p b*quadraticValue (Q a b) x := by
  have hm : (1/2:ℝ)≤∑ a,∑ b,unorderedPairWeight a b*p a*p b := by
    rw [sum_unorderedPairWeight,hmass]
    have hs : 0≤∑ a,p a^2 := Finset.sum_nonneg fun a _ => sq_nonneg _
    linarith only [hs]
  have hmul := mul_le_mul_of_nonneg_right hm (mul_nonneg hc hE)
  calc
    _ ≤ (∑ a,∑ b,unorderedPairWeight a b*p a*p b)*(c*E) := by nlinarith only [hmul]
    _ = ∑ a,∑ b,unorderedPairWeight a b*p a*p b*(c*E) := by
      simp only [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_left (hQ a b)
        (mul_nonneg (mul_nonneg (unorderedPairWeight_nonneg a b) (hp a)) (hp b))

end DittertRybin.Certificates
