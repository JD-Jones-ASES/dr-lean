import DR.Certificates.FourByFiveThreeDefinitions
import DR.Uniform

/-! Exact mass and Frobenius-distance bookkeeping for the closed 4x5 simplex. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

def fourByFiveThreeFlat (P : Board 4 5) (e : Fin 20) : ℝ :=
  P (fourByFiveThreeCell.symm e).1 (fourByFiveThreeCell.symm e).2

noncomputable def fourByFiveThreeEnergy (P : Board 4 5) : ℝ :=
  ∑ i,∑ j,(P i j-1/20)^2

theorem fourByFiveThree_sum_flat (P : Board 4 5) :
    (∑ e,fourByFiveThreeFlat P e)=totalMass P := by
  rw [← fourByFiveThreeCell.sum_comp]
  simp [fourByFiveThreeFlat,Fintype.sum_prod_type,totalMass,rowSum]

theorem fourByFiveThree_energy_flat (P : Board 4 5) :
    (∑ e,(fourByFiveThreeFlat P e-1/20)^2)=fourByFiveThreeEnergy P := by
  rw [← fourByFiveThreeCell.sum_comp]
  simp [fourByFiveThreeFlat,Fintype.sum_prod_type,fourByFiveThreeEnergy]

theorem fourByFiveThree_centered_sum (p : Fin 20 → ℝ) (hp : ∑ i,p i=1) :
    (∑ i,p i^2)-(∑ i,p i)^2/20=∑ i,(p i-1/20)^2 := by
  have ht (i : Fin 20) : (p i-1/20)^2=p i^2-(1/10)*p i+1/400 := by ring
  simp only [ht,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem fourByFiveThreeEnergy_nonneg (P : Board 4 5) : 0≤fourByFiveThreeEnergy P :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (P i j-1/20)

/-- No sign or normalization premise is needed for the exact zero-distance criterion. -/
theorem fourByFiveThreeEnergy_eq_zero_iff (P : Board 4 5) :
    fourByFiveThreeEnergy P=0 ↔ P=uniformBoard 4 5 := by
  constructor
  · intro hzero
    ext i j
    have hpart : (P i j-1/20)^2≤fourByFiveThreeEnergy P := by
      apply le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (P i j-1/20)) (Finset.mem_univ j))
      exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (P i j-1/20))
        (Finset.mem_univ i)
    rw [hzero] at hpart
    have hij := sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hpart (sq_nonneg _)))
    convert hij using 1
    norm_num [uniformBoard]
  · intro heq
    rw [heq]
    norm_num [fourByFiveThreeEnergy,uniformBoard]

theorem fourByFiveThree_uniform_value :
    separationProbability (uniformBoard 4 5) 3=(27/40:ℝ) := by
  rw [separationProbability_uniform (by norm_num) (by norm_num)]
  norm_num [uniformSeparationValue,distinctUniformProbability]

end DittertRybin
