import DR.Rectangular.OrderThreeFourRowAveraging
import DR.Rectangular.ThreeRowPositive

/-! The complete four-row K=3 infinite strip, with equality on the closed simplex. -/
namespace DittertRybin
open scoped BigOperators

theorem IsSeparationGlobalMax.orderThreeFourRow_positive {n : ℕ} {P : Board 4 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 960≤n) :
    ∀ i j,0<P i j := by
  intro i j
  have hrow := hmax.row_mass_pos hP (by norm_num : 3≤4) i
  have he (a : Fin n) : P i a=P i j := hmax.orderThreeFourRow_equal_columns hP hn i a j
  have hid : rowSum P i=(n:ℝ)*P i j := by
    simp only [rowSum,he,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hid] at hrow
  exact pos_of_mul_pos_right hrow (Nat.cast_nonneg n)

theorem IsSeparationGlobalMax.orderThreeFourRow_eq_uniform {n : ℕ} {P : Board 4 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 960≤n) :
    P=uniformBoard 4 n :=
  hmax.eq_uniform_of_positive_three hP (by norm_num) (by omega)
    (hmax.orderThreeFourRow_positive hP hn)

/-- Every four-row rectangle with at least 960 columns has the unique uniform maximum. -/
theorem uniformMaximizer_orderThree_four_rows {n : ℕ} (hn : 960≤n) :
    UniformMaximizer 4 n 3 := by
  apply uniform_maximizer_of_unique_global (by norm_num) (by omega) 3
  intro P hP hmax
  exact IsSeparationGlobalMax.orderThreeFourRow_eq_uniform hmax hP hn

/-- Transposition preserves the entire simplex and equality case. -/
theorem uniformMaximizer_orderThree_four_columns {m : ℕ} (hm : 960≤m) :
    UniformMaximizer m 4 3 := by
  apply uniform_maximizer_of_unique_global (by omega) (by norm_num) 3
  intro P hP hmax
  have hmax' : IsSeparationGlobalMax P 3 := hmax
  have heq := hmax'.transpose.orderThreeFourRow_eq_uniform hP.transpose hm
  funext i j
  have hij := congrFun (congrFun heq j) i
  simpa only [Matrix.transpose_apply,uniformBoard,mul_comm] using hij

end DittertRybin
