import DR.Square.OrderThreeFaces
import DR.Square.OrderThreeSymmetry

/-! Actual canonical matrix exclusions for the finite order-three support audit. -/

namespace DittertRybin

def orderThreeZeroBlock11 (a b c : ℝ) : Board 3 3 :=
  ![![0, a, a], ![b, c, c], ![b, c, c]]

def orderThreeZeroBlock12 (a b c : ℝ) : Board 3 3 :=
  ![![0, 0, a], ![b, b, c], ![b, b, c]]

def orderThreeZeroBlock22 (a b c : ℝ) : Board 3 3 :=
  ![![0, 0, a], ![0, 0, a], ![b, b, c]]

def orderThreeSingletonOppositeFull (a b c d : ℝ) : Board 3 3 :=
  ![![a, 0, c], ![0, b, d], ![0, b, d]]

theorem orderThree_zero_block11_not_globalMax {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmass : totalMass (orderThreeZeroBlock11 a b c) = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional (orderThreeZeroBlock11 a b c)) : False := by
  have hA : ∀ i j, 0 ≤ orderThreeZeroBlock11 a b c i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [orderThreeZeroBlock11] <;> positivity
  have hleft := dittert_three_globalMax_gradient_eq hA hmass hmax (0, 1) (1, 1) ha hc
  have hright := dittert_three_globalMax_gradient_eq hA hmass hmax (1, 0) (1, 1) hb hc
  have hzero := dittert_three_globalMax_gradient_le hA hmass hmax (0, 0) (1, 1) hc
  norm_num [orderThreeGradient, orderThreePair, orderThreeZeroBlock11, rowSum, colSum,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hleft hright hzero
  apply orderThree_zero_rectangle_one_one ha hb hc <;> nlinarith

theorem orderThree_zero_block12_not_globalMax {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmass : totalMass (orderThreeZeroBlock12 a b c) = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional (orderThreeZeroBlock12 a b c)) : False := by
  have hA : ∀ i j, 0 ≤ orderThreeZeroBlock12 a b c i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [orderThreeZeroBlock12] <;> positivity
  have hcommon := dittert_three_globalMax_gradient_eq hA hmass hmax (1, 0) (1, 2) hb hc
  have hzero := dittert_three_globalMax_gradient_le hA hmass hmax (0, 0) (1, 2) hc
  norm_num [orderThreeGradient, orderThreePair, orderThreeZeroBlock12, rowSum, colSum,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hcommon hzero
  apply orderThree_zero_rectangle_one_two (a := a) hb hc <;> nlinarith

theorem orderThree_zero_block22_not_globalMax {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hmass : totalMass (orderThreeZeroBlock22 a b c) = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional (orderThreeZeroBlock22 a b c)) : False := by
  have hA : ∀ i j, 0 ≤ orderThreeZeroBlock22 a b c i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [orderThreeZeroBlock22] <;> positivity
  have hleft := dittert_three_globalMax_gradient_eq hA hmass hmax (0, 2) (2, 2) ha hc
  have hright := dittert_three_globalMax_gradient_eq hA hmass hmax (2, 0) (2, 2) hb hc
  norm_num [orderThreeGradient, orderThreePair, orderThreeZeroBlock22, rowSum, colSum,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hleft hright
  apply orderThree_zero_rectangle_two_two ha hb hc <;> nlinarith

theorem orderThree_singleton_opposite_full_not_globalMax {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hmass : totalMass (orderThreeSingletonOppositeFull a b c d) = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional (orderThreeSingletonOppositeFull a b c d)) : False := by
  have hA : ∀ i j, 0 ≤ orderThreeSingletonOppositeFull a b c d i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [orderThreeSingletonOppositeFull] <;> positivity
  have hcommon := dittert_three_globalMax_gradient_eq hA hmass hmax (0, 0) (0, 2) ha hc
  have hmisscol := dittert_three_globalMax_gradient_le hA hmass hmax (1, 0) (1, 1) hb
  have hmissrow := dittert_three_globalMax_gradient_le hA hmass hmax (1, 0) (0, 0) ha
  norm_num [orderThreeGradient, orderThreePair, orderThreeSingletonOppositeFull, rowSum, colSum,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hcommon hmisscol hmissrow
  apply orderThree_singleton_opposite_full (a := a) hb hc hd <;> nlinarith

theorem orderThree_cycle_not_globalMax {a b e f x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hf : 0 < f) (hx : 0 < x) (hy : 0 < y)
    (hmass : totalMass (orderThreeTwoProperBoard a b e f x y 0) = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional (orderThreeTwoProperBoard a b e f x y 0)) : False := by
  have hA : ∀ i j, 0 ≤ orderThreeTwoProperBoard a b e f x y 0 i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [orderThreeTwoProperBoard] <;> positivity
  have hcommon := dittert_three_globalMax_gradient_eq hA hmass hmax (1, 0) (1, 1) ha hf
  have hleft := dittert_three_globalMax_gradient_le hA hmass hmax (0, 0) (0, 1) he
  have hright := dittert_three_globalMax_gradient_le hA hmass hmax (2, 1) (2, 0) hb
  have hmiss0 := dittert_three_globalMax_gradient_le hA hmass hmax (0, 0) (2, 0) hb
  have hmiss2 := dittert_three_globalMax_gradient_le hA hmass hmax (2, 1) (0, 1) he
  have hlast0 := dittert_three_globalMax_gradient_eq hA hmass hmax (1, 0) (2, 0) ha hb
  have hlast1 := dittert_three_globalMax_gradient_eq hA hmass hmax (0, 1) (0, 2) he hx
  norm_num [orderThreeGradient, orderThreePair, orderThreeTwoProperBoard, rowSum, colSum,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hcommon hleft hright hmiss0 hmiss2 hlast0 hlast1
  obtain ⟨hxy, hbe, haf⟩ := orderThree_cycle_pair_equal ha hb he hf hx hy
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  subst y
  subst e
  subst f
  obtain ⟨hab, hxb⟩ := orderThree_cycle_last_equal (a := a) hb hx (by nlinarith) (by nlinarith)
  subst a
  subst x
  norm_num [totalMass, rowSum, orderThreeTwoProperBoard, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hmass
  have hbval : b = 1 / 2 := by linarith
  subst b
  have hcont := dittert_globalMax_isContender (by decide : 0 < 3) _ hmax
  rw [dittert_three_cubic] at hcont
  norm_num [dittertConstant, rowSum, colSum, orderThreePair, orderThreeTwoProperBoard,
    Fin.sum_univ_succ, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] at hcont

end DittertRybin
