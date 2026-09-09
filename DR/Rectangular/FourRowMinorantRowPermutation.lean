import DR.Rectangular.FourRowMinorantRowCurve

/-! Row-permutation transport of the actual fixed-q feasible maximum. -/

namespace DittertRybin
open scoped BigOperators

theorem fourRowMinorantSquareSum_permute (r : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) :
    fourRowMinorantSquareSum (r ∘ e)=fourRowMinorantSquareSum r := by
  exact Equiv.sum_comp e (fun i => r i^2)

theorem fourRowMinorantStationary_permute (r : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    fourRowMinorantStationary (r ∘ e) i=fourRowMinorantStationary r (e i) := by
  simp only [fourRowMinorantStationary,fourRowMinorantDelta,
    fourRowMinorantSquareSum_permute,Function.comp_apply]

theorem fourRowMinorantE3_moments (r : Fin 4 → ℝ) :
    fourRowMinorantE3 r=((∑ i,r i)^3-3*(∑ i,r i)*(∑ i,r i^2)+2*(∑ i,r i^3))/6 := by
  rw [fourRowMinorantE3_expand]
  simp only [Fin.sum_univ_four]
  ring

theorem fourRowMinorantE3_permute (r : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) :
    fourRowMinorantE3 (r ∘ e)=fourRowMinorantE3 r := by
  rw [fourRowMinorantE3_moments,fourRowMinorantE3_moments]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e r,Equiv.sum_comp e (fun i => r i^2),Equiv.sum_comp e (fun i => r i^3)]

theorem fourRowMinorantRowObjective_permute (γ : ℝ) (r : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) :
    fourRowMinorantRowObjective γ (r ∘ e)=fourRowMinorantRowObjective γ r := by
  rw [fourRowMinorantRowObjective,fourRowMinorantE3_permute]
  simp only [Function.comp_apply]
  rw [Equiv.prod_comp]
  rfl

theorem IsFourRowMinorantRowMaximum.permute {γ : ℝ} {r : Fin 4 → ℝ}
    (hmax : IsFourRowMinorantRowMaximum γ r) (e : Equiv.Perm (Fin 4)) :
    IsFourRowMinorantRowMaximum γ (r ∘ e) := by
  intro u hu hus huq huv
  have hs : (∑ i,(u ∘ e.symm) i)=1 := (Equiv.sum_comp e.symm u).trans hus
  have hq : fourRowMinorantSquareSum (u ∘ e.symm)=fourRowMinorantSquareSum r := by
    rw [fourRowMinorantSquareSum_permute,huq,fourRowMinorantSquareSum_permute]
  have hv : ∀ i,0≤fourRowMinorantStationary (u ∘ e.symm) i := by
    intro i
    rw [fourRowMinorantStationary_permute]
    exact huv (e.symm i)
  have h := hmax (u ∘ e.symm) (fun i => hu (e.symm i)) hs hq hv
  simpa only [fourRowMinorantRowObjective_permute] using h

/-- Move the smallest, second-largest and largest sorted entries into the active triple. -/
def fourRowMinorantTriplePermutation : Equiv.Perm (Fin 4) where
  toFun i := ![0,2,3,1] i
  invFun i := ![0,3,1,2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Move a repeated largest pair and the smallest entry into the active triple. -/
def fourRowMinorantLargestPermutation : Equiv.Perm (Fin 4) where
  toFun i := ![2,3,0,1] i
  invFun i := ![2,3,0,1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

end DittertRybin
