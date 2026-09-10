import DR.Endpoint.RowClusterKernel
import DR.Endpoint.RowCollisionBounds
import DR.Endpoint.LongColumnCoefficientFive
import DR.Endpoint.DeletedRowBalance

/-! A strengthened retained-board closure for every row dimension m>=5.
The common collision-cluster argument follows LongColumnKernel; the actual
elementary coefficient now uses the proved half-factorial lower bound.
The board, its row normalization and its collision law are all literal.
The upstream gauge bootstrap supplies only the stated quantitative bounds. -/

namespace DittertRybin
open scoped BigOperators

theorem longColumn_five_retained_kernel_posDef {m n : ℕ} (hm : 5 ≤ m)
    (hn : 10000*m^2 ≤ n) (P : Board m n) (hP : ∀ i j, 0 ≤ P i j)
    (hh : (3/4 : ℝ) < totalMass P)
    (hs : (∑ i, (1-(m : ℝ)*(rowSum P i/totalMass P))^2) < 1/9)
    (hc : ∀ j, colSum P j ≤ 25/(n : ℝ)) :
    (averagingKernel P (m-2)).PosDef := by
  let h := totalMass P
  have hm0 : 0 < m := by omega
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR0 : (0 : ℝ) < m := by linarith
  have hnR : (10000 : ℝ)*(m : ℝ)^2 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by nlinarith
  have hh0 : 0 < h := by dsimp [h]; linarith
  have hlo (i : Fin m) : ((2/3 : ℝ)/(m : ℝ))*h < rowSum P i :=
    (lt_div_iff₀ hh0).mp (endpoint_row_lower_of_sq hm0 _ hs i)
  have hr (i : Fin m) : 0 < rowSum P i :=
    (by positivity : (0 : ℝ) < ((2/3 : ℝ)/(m : ℝ))*h).trans (hlo i)
  have hinv (i : Fin m) : 1/rowSum P i ≤ 3*(m : ℝ)/(2*h) := by
    apply (div_le_div_iff₀ (hr i) (by positivity : 0 < 2*h)).mpr
    have hi := hlo i
    have hmul := mul_lt_mul_of_pos_left hi hmR0
    have heq : (m : ℝ)*(((2/3 : ℝ)/(m : ℝ))*h) = (2/3 : ℝ)*h := by field_simp
    rw [heq] at hmul
    nlinarith only [hmul]
  have hsum : (∑ i, 1/rowSum P i) ≤ 3*(m : ℝ)^2/(2*h) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hinv i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    exact hh.trans_eq (by ring)
  have hD := normalizedRow_collisionIntensity_le P hP hr hc
  have hDb : rowCollisionIntensity (normalizeRows P) ≤ (1/12 : ℝ) := by
    apply hD.trans
    apply (mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (25/(n : ℝ))/2)).trans
    have heq : ((25/(n : ℝ))/2)*(3*(m : ℝ)^2/(2*h)) =
        75*(m : ℝ)^2/(4*(n : ℝ)*h) := by ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 4*(n : ℝ)*h)).mpr
    have hh' : (3/4 : ℝ) < h := hh
    have hprod := mul_le_mul_of_nonneg_left hh'.le hn0.le
    nlinarith only [hprod, hnR, sq_nonneg (m : ℝ)]
  have hnorm := normalizeRows_rowSum P (fun i => (hr i).ne')
  have hbad := one_sub_rowAvoidance_le_intensity (normalizeRows P)
    (normalizeRows_nonneg P hP) hnorm
  have hp : 0 < rowAvoidance (normalizeRows P) := by linarith
  have hpge : (11/12 : ℝ) ≤ rowAvoidance (normalizeRows P) := by linarith
  have hcoef := longColumn_five_coefficient_ratio hm hn P hP hr hh hp hc
  let G := (∏ i, rowSum P i)/h^2
  have hG : 0 < G := div_pos (Finset.prod_pos (fun i _ => hr i)) (sq_pos_of_pos hh0)
  have hmult : 4*(m : ℝ)^2*(G*rowAvoidance (normalizeRows P)) ≤ averagingCoefficient P (m-2) :=
    (le_div_iff₀ (mul_pos hG hp)).mp hcoef
  have hretain : 2*(m : ℝ)^2*G ≤ 4*(m : ℝ)^2*(G*rowAvoidance (normalizeRows P)) := by
    have hmul := mul_le_mul_of_nonneg_left hpge (show 0 ≤ (m : ℝ)^2*G by positivity)
    nlinarith only [hmul, mul_nonneg (sq_nonneg (m : ℝ)) hG.le]
  exact averagingKernel_cluster_posDef P hP hr h hh0 hs.le hDb (hretain.trans hmult)

end DittertRybin
