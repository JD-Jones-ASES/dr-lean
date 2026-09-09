import DR.Rectangular.OrderThreeFourRowCopositive

/-! The actual K=3 failure functional dominates a rational cubic in the four-row column gauges. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def orderThreeFourRowColumnGauge {n : ℕ} (P : Board 4 n) (j : Fin n) : ℝ :=
  ∑ i,P i j*orderThreeFourRowWeight (rowSum P i)

theorem orderThreeFourRowColumnGauge_bounds {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (j : Fin n) : 0≤orderThreeFourRowColumnGauge P j ∧
      orderThreeFourRowColumnGauge P j≤colSum P j ∧
      colSum P j^2≤3*orderThreeFourRowColumnGauge P j^2 := by
  have hri (i : Fin 4) : rowSum P i≤1 := by
    calc
      _ ≤ ∑ k,rowSum P k := Finset.single_le_sum (fun k _ => rowSum_nonneg hP.1 k) (Finset.mem_univ i)
      _ = 1 := hP.2
  have hw (i : Fin 4) := orderThreeFourRowWeight_bounds (rowSum_nonneg hP.1 i) (hri i)
  have ha0 : 0≤orderThreeFourRowColumnGauge P j :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hP.1 i j) (Real.sqrt_nonneg _)
  have ha1 : orderThreeFourRowColumnGauge P j≤colSum P j := by
    apply Finset.sum_le_sum
    intro i _
    exact (mul_le_mul_of_nonneg_left (hw i).2 (hP.1 i j)).trans_eq (mul_one _)
  have hl : Real.sqrt (1/3)*colSum P j≤orderThreeFourRowColumnGauge P j := by
    simp only [colSum,Finset.mul_sum,orderThreeFourRowColumnGauge]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hw i).1 (hP.1 i j)
  have hs := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (colSum_nonneg hP.1 j)) hl 2
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤1/3)] at hs
  exact ⟨ha0,ha1,by nlinarith only [hs]⟩

theorem orderThreeFourRowColumnGauge_sum {n : ℕ} (P : Board 4 n) :
    (∑ j,orderThreeFourRowColumnGauge P j)=∑ i,orderThreeFourRowGauge (rowSum P i) := by
  simp only [orderThreeFourRowColumnGauge,orderThreeFourRowGauge]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,rowSum]

theorem orderThreeFourRowColumnGauge_sum_le_one {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    (∑ j,orderThreeFourRowColumnGauge P j)≤1 := by
  calc
    _ ≤ ∑ j,colSum P j := Finset.sum_le_sum fun j _ => (orderThreeFourRowColumnGauge_bounds P hP j).2.1
    _ = 1 := (totalMass_eq_sum_colSum P).symm.trans hP.2

/-- A rational coefficient 11 safely bounds twice the actual cubic column mass. -/
theorem orderThreeFourRowColumnGauge_cube {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (j : Fin n) : 2*colSum P j^3≤11*orderThreeFourRowColumnGauge P j^3 := by
  obtain ⟨ha0,_,hsq⟩ := orderThreeFourRowColumnGauge_bounds P hP j
  have hc0 := colSum_nonneg hP.1 j
  have hcap : colSum P j≤(7/4)*orderThreeFourRowColumnGauge P j := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [sq_nonneg (orderThreeFourRowColumnGauge P j)]
  have hcube := pow_le_pow_left₀ hc0 hcap 3
  have hpow : 0≤orderThreeFourRowColumnGauge P j^3 := pow_nonneg ha0 _
  nlinarith only [hcube,hpow]

/-- Newton's identity on four entries, retaining the third elementary symmetric remainder. -/
theorem orderThreeFourRow_column_cubic (v : Fin 4 → ℝ) :
    4*(∑ i,v i^3)-6*(∑ i,v i)*(∑ i,v i^2) =
      -2*(∑ i,v i)^3+12*orderThreeFourRowE3 v := by
  simp only [orderThreeFourRowE3,orderThreeFourRowCofactor,Fin.sum_univ_four,Fin.reduceAdd]
  ring

/-- The normalized failure polynomial is the sum of the literal four-entry column costs. -/
theorem orderThreeFailurePolynomial_four_columns {n : ℕ} (P : Board 4 n) (hmass : totalMass P=1) :
    orderThreeFailurePolynomial P = ∑ j,
      (3*orderThreeFourRowQuadratic (rowSum P) (fun i=>P i j)+4*(∑ i,P i j^3)-6*colSum P j*(∑ i,P i j^2)) := by
  have hcomm (f : Fin 4 → Fin n → ℝ) : (∑ i,∑ j,f i j)=(∑ j,∑ i,f i j) := Finset.sum_comm
  calc
    _ = ∑ j,(3*(∑ i,P i j^2)+6*(∑ i,P i j*rowSum P i*colSum P j)-
      6*(∑ i,P i j^2*(rowSum P i+colSum P j))+4*(∑ i,P i j^3)) := by
      unfold orderThreeFailurePolynomial
      rw [hmass]
      simp_rw [hcomm]
      simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [orderThreeFourRowQuadratic,colSum,Fin.sum_univ_four]
      ring

/-- Every four-row probability matrix satisfies the actual rational cubic gauge minorant. -/
theorem orderThreeFourRow_failure_ge_gauge_cubic {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    (∑ j,(3*orderThreeFourRowColumnGauge P j^2-11*orderThreeFourRowColumnGauge P j^3))≤
      1-separationProbability P 3 := by
  rw [one_sub_separationProbability_three hP,orderThreeFailurePolynomial_four_columns P hP.2]
  apply Finset.sum_le_sum
  intro j _
  have hq := orderThreeFourRowQuadratic_lower (rowSum P) (fun i=>P i j)
    (rowSum_nonneg hP.1) hP.2 (fun i=>hP.1 i j)
  change orderThreeFourRowColumnGauge P j^2≤_ at hq
  have hc := orderThreeFourRowColumnGauge_cube P hP j
  have hn := orderThreeFourRow_column_cubic (fun i=>P i j)
  have he : 0≤orderThreeFourRowE3 (fun i=>P i j) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hP.1 (i+1) j) (hP.1 (i+2) j)) (hP.1 (i+3) j)
  change 4*(∑ i,P i j^3)-6*colSum P j*(∑ i,P i j^2) = -2*colSum P j^3+12*orderThreeFourRowE3 (fun i=>P i j) at hn
  linarith only [hq,hc,hn,he]

end DittertRybin
