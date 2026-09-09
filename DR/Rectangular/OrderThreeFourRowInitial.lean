import DR.Rectangular.OrderThreeFourRowLeading

/-! Initial concentration from an actual three-sample contender on a four-row strip. -/
namespace DittertRybin
open scoped BigOperators

/-- Any fixed repeated cell pair forces three-sample failure. -/
theorem orderThree_cellSquareSum_le_failure {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) : cellSquareSum P≤1-separationProbability P 3 := by
  let ij : SampleIndexPair 3 := ⟨(0,1),by decide⟩
  rw [← collisionEvent_mass_of_same_pair hP ij,← collision_union_mass hP]
  apply eventMass_mono _ (fun a : Fin m × Fin n => hP.1 a.1 a.2)
  intro s hs
  exact ⟨(ij,ij),hs⟩

theorem orderThreeFourRow_failure_uniform {n : ℕ} (hn : 3≤n) :
    1-separationProbability (uniformBoard 4 n) 3 = 15/(8*(n:ℝ))-5/(4*(n:ℝ)^2) := by
  have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  rw [separationProbability_uniform (by norm_num) (by omega)]
  norm_num [uniformSeparationValue,distinctUniformProbability,Nat.descFactorial_succ,
    Nat.cast_sub (show 1≤n by omega),Nat.cast_sub (show 2≤n by omega)]
  field_simp
  ring

theorem orderThreeFourRow_colSum_sq_le (P : Board 4 n) (j : Fin n) :
    colSum P j^2≤4*cellSquareSum P := by
  have hcol : colSum P j^2≤4*(∑ i,P i j^2) := by
    simpa [colSum,mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin 4 => P i j) (fun _=>(1:ℝ))
  have hpart : (∑ i,P i j^2)≤cellSquareSum P := by
    unfold cellSquareSum
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    exact Finset.single_le_sum (fun c _ => Finset.sum_nonneg fun i _ => sq_nonneg (P i c)) (Finset.mem_univ j)
  linarith only [hcol,hpart]

/-- The rational initial cap is strong enough for the later centered-cubic estimate. -/
theorem orderThreeFourRow_contender_initial_cap {n : ℕ} (hn : 960≤n) {P : Board 4 n}
    (hP : IsProbability P) (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3)
    (j : Fin n) : colSum P j<177/2000 ∧ orderThreeFourRowColumnGauge P j<177/2000 := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hnreal : (960:ℝ)≤n := by exact_mod_cast hn
  have hcell := (orderThree_cellSquareSum_le_failure hP).trans (sub_le_sub_left hcont 1)
  rw [orderThreeFourRow_failure_uniform (by omega)] at hcell
  have hpart := orderThreeFourRow_colSum_sq_le P j
  have hsub : 0≤5/(4*(n:ℝ)^2) := by positivity
  have hdim : 15/(8*(n:ℝ))≤1/512 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hnreal]
  have hc : colSum P j<177/2000 := by nlinarith only [hcell,hpart,hsub,hdim]
  exact ⟨hc,((orderThreeFourRowColumnGauge_bounds P hP j).2.1).trans_lt hc⟩

end DittertRybin
