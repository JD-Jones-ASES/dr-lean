import DR.Collision.FirstMoment
import DR.Endpoint.UniformCollisionRemainder
import DR.Endpoint.Normalization

/-! A repeated complete cell in two specified draws is an actual failure
witness. Its marginal probability supplies an initial column cap on every
endpoint contender, including all zero-entry boundaries. -/
namespace DittertRybin
open scoped BigOperators

theorem cellSquareSum_le_failure {m n k : ℕ} (hk : 2≤k) (P : Board m n)
    (hP : IsProbability P) : cellSquareSum P≤1-separationProbability P k := by
  let ij : SampleIndexPair k := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by simp⟩
  rw [← collisionEvent_mass_of_same_pair hP ij,← collision_union_mass hP]
  apply eventMass_mono (fun a : Fin m × Fin n => P a.1 a.2) (fun a => hP.1 a.1 a.2)
  intro s hs
  exact ⟨(ij,ij),hs⟩

theorem colSum_sq_le_cellSquareSum {m n : ℕ} (P : Board m n) (j : Fin n) :
    (colSum P j)^2≤(m:ℝ)*cellSquareSum P := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => P i j)
    (fun _ : Fin m => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcs
  have hpart : (∑ i,(P i j)^2)≤cellSquareSum P := by
    unfold cellSquareSum
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    exact Finset.single_le_sum (fun t _ => Finset.sum_nonneg fun i _ => sq_nonneg (P i t))
      (Finset.mem_univ j)
  change (colSum P j)^2≤_ at hcs
  nlinarith only [hcs,mul_le_mul_of_nonneg_left hpart (Nat.cast_nonneg m)]

theorem endpoint_contender_repeatedCell_column_sq {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    (P : Board m n) (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) (j : Fin n) :
    (colSum P j)^2≤(m:ℝ)*(m.choose 2:ℝ)/(n:ℝ) := by
  have hn : 0<n := by omega
  have ha0 := (dittertConstant_pos (by omega : 0<m)).le
  have hq0 : 0≤1-distinctUniformProbability n m := by
    exact sub_nonneg.mpr (distinctUniformProbability_lt_one hn hm).le
  have hfail : 1-separationProbability P m≤1-distinctUniformProbability n m := by
    rw [uniformSeparationValue_rectangular_endpoint] at hcont
    nlinarith only [hcont,mul_nonneg ha0 hq0]
  have hrem := (endpoint_uniform_collision_remainder hm hn hmn).1
  have hcell := (cellSquareSum_le_failure hm P hP).trans hfail
  have hcol := colSum_sq_le_cellSquareSum P j
  have hmR : 0≤(m:ℝ) := Nat.cast_nonneg m
  have hmultiply := mul_le_mul_of_nonneg_left hcell hmR
  have hupper := mul_le_mul_of_nonneg_left (show 1-distinctUniformProbability n m≤(m.choose 2:ℝ)/(n:ℝ) by linarith only [hrem]) hmR
  have he : (m:ℝ)*((m.choose 2:ℝ)/(n:ℝ))=(m:ℝ)*(m.choose 2:ℝ)/(n:ℝ) := by ring
  rw [← he]
  linarith only [hcol,hmultiply,hupper]

end DittertRybin
