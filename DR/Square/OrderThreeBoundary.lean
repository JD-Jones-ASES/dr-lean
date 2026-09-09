import DR.Square.OrderThree

/-! Exact boundary-support exclusions for the order-three endpoint. -/

open scoped BigOperators
open Finset

namespace DittertRybin

/-- The triangular board containing a singleton and a containing doubleton. -/
def orderThreeSingletonBoard (a b c x y z : ℝ) : Board 3 3 :=
  ![![a, b, x], ![0, c, y], ![0, 0, z]]

theorem orderThree_singleton_pair_elimination {a b c x y z : ℝ}
    (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z)
    (hcommon : (x + y + z) * (a - b) = (x + y) * c)
    (hmiss : (x + y + z) * c ≤ (x + y) * (a - b)) : False := by
  have hE : 0 < x + y + z := by linarith
  have h1 := mul_le_mul_of_nonneg_left hmiss hE.le
  have h2 := congrArg (fun q : ℝ => (x + y) * q) hcommon
  have h3 := mul_pos hc (mul_pos hz (show 0 < 2 * (x + y) + z by linarith))
  nlinarith

/-- A singleton and a doubleton containing its row are incompatible with
full-simplex stationarity when the remaining row has positive mass. -/
theorem orderThree_singleton_containing_not_stationary {a b c x y z : ℝ}
    (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z)
    (hcommon : orderThreeGradient (orderThreeSingletonBoard a b c x y z) 0 0 =
      orderThreeGradient (orderThreeSingletonBoard a b c x y z) 0 1)
    (hmiss : orderThreeGradient (orderThreeSingletonBoard a b c x y z) 1 0 ≤
      orderThreeGradient (orderThreeSingletonBoard a b c x y z) 1 1) : False := by
  norm_num [orderThreeGradient, orderThreePair, orderThreeSingletonBoard, rowSum, colSum,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hcommon hmiss
  apply orderThree_singleton_pair_elimination (a := a) (b := b) hc hx hy hz <;> nlinarith

/-- Two singleton columns in different rows cannot occur at a maximizer with
the third row positive. The other column may have boundary entries. -/
theorem orderThree_two_singletons_not_stationary {a b x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < z)
    (hmiss0 : orderThreeGradient (orderThreeSingletonBoard a 0 b x y z) 1 0 ≤
      orderThreeGradient (orderThreeSingletonBoard a 0 b x y z) 0 0)
    (hmiss1 : orderThreeGradient (orderThreeSingletonBoard a 0 b x y z) 0 1 ≤
      orderThreeGradient (orderThreeSingletonBoard a 0 b x y z) 1 1) : False := by
  norm_num [orderThreeGradient, orderThreePair, orderThreeSingletonBoard, rowSum, colSum,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hmiss0 hmiss1
  have hpos := mul_pos (add_pos ha hb) hz
  nlinarith

/-- The disjoint 1-by-1 and 2-by-2 support, including all its boundary faces. -/
def orderThreeDisjointSquareBoard (a b c d e : ℝ) : Board 3 3 :=
  ![![a, 0, 0], ![0, b, c], ![0, d, e]]

theorem orderThree_disjoint_square_bound {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hmass : a + b + c + d + e = 3) :
    dittertFunctional (orderThreeDisjointSquareBoard a b c d e) ≤ 3 / 2 := by
  have hsum : 8 * (b*c + b*d + b*e + c*d + c*e + d*e) ≤ 3 * (b+c+d+e)^2 := by
    nlinarith [sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (b-e),
      sq_nonneg (c-d), sq_nonneg (c-e), sq_nonneg (d-e)]
  have h1 := mul_le_mul_of_nonneg_left hsum ha
  have h2 := mul_nonneg (sq_nonneg (a-1)) (show 0 ≤ 4-a by linarith)
  have h3 : a * (b+c+d+e)^2 ≤ 4 := by
    have hs : b+c+d+e = 3-a := by linarith
    rw [hs]
    nlinarith
  rw [dittert_three_cubic]
  norm_num [orderThreeDisjointSquareBoard, rowSum, colSum, orderThreePair,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith

/-- The disjoint 1-by-2 and 2-by-1 support, including every zero boundary. -/
def orderThreeDisjointCrossBoard (a b c d : ℝ) : Board 3 3 :=
  ![![a, b, 0], ![0, 0, c], ![0, 0, d]]

theorem orderThree_disjoint_cross_bound {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hmass : a + b + c + d = 3) :
    dittertFunctional (orderThreeDisjointCrossBoard a b c d) ≤ 27 / 16 := by
  have h1 := mul_nonneg (add_nonneg ha hb) (sq_nonneg (c-d))
  have h2 := mul_nonneg (add_nonneg hc hd) (sq_nonneg (a-b))
  have h3 : (a+b)*(c+d) ≤ 9/4 := by nlinarith [sq_nonneg (a+b-c-d)]
  have hid : (a+b)*(c+d)^2 + (a+b)^2*(c+d) = 3*(a+b)*(c+d) := by
    calc
      _ = (a+b)*(c+d)*(a+b+c+d) := by ring
      _ = _ := by rw [hmass]; ring
  rw [dittert_three_cubic]
  norm_num [orderThreeDisjointCrossBoard, rowSum, colSum, orderThreePair,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith

end DittertRybin
