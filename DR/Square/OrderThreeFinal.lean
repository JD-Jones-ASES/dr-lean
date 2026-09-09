import DR.Square.OrderThreeSupport
import DR.Square.OrderThreeAveragedFaces
import DR.Square.OrderThreeRelabel
import DR.Square.Maximizers

/-! The unconditional order-three Dittert endpoint and its unique equality case. -/

open scoped BigOperators

namespace DittertRybin

noncomputable def orderThreeSupportMatrix (A : Board 3 3) : Fin 3 → Fin 3 → Bool :=
  fun i j => decide (0 < A i j)

theorem orderThreeSupportMatrix_pos (A : Board 3 3) (i j : Fin 3) :
    orderThreeSupportMatrix A i j = true ↔ 0 < A i j := by
  simp [orderThreeSupportMatrix]

theorem orderThreeSupportMatrix_zero {A : Board 3 3} (hA : ∀ i j, 0 ≤ A i j) (i j : Fin 3) :
    orderThreeSupportMatrix A i j = false ↔ A i j = 0 := by
  simp only [orderThreeSupportMatrix, decide_eq_false_iff_not, not_lt]
  exact ⟨fun h => le_antisymm h (hA i j), fun h => h.le⟩

/-- Each canonical support has now been treated by a real-valued proof. -/
theorem orderThree_canonical_support_globalMax_uniform {A : Board 3 3}
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A)
    (k : OrderThreeSupportKind) (hs : OrderThreeFitsSupport (orderThreeSupportMatrix A) k) :
    A = uniformDittertMatrix 3 := by
  have hp (i j : Fin 3) := (orderThreeSupportMatrix_pos A i j).mp
  have hz (i j : Fin 3) := (orderThreeSupportMatrix_zero hA i j).mp
  have hcont : (16/9:ℝ) ≤ dittertFunctional A := by
    have h := dittert_globalMax_isContender (by decide : 0 < 3) A hmax
    norm_num [dittertConstant] at h
    exact h
  cases k with
  | full =>
    exact orderThree_positive_globalMax_uniform (fun i j => hp i j (hs i j)) hmass hmax
  | zero11 =>
    dsimp only [OrderThreeFitsSupport] at hs
    exfalso
    apply orderThree_zero11_not_globalMax hA hmass hmax
    · exact hz 0 0 (by rw [hs]; rfl)
    · intro j
      constructor <;> apply hp <;> rw [hs] <;> fin_cases j <;> rfl
    · intro i
      constructor <;> apply hp <;> rw [hs] <;> fin_cases i <;> rfl
  | zero12 =>
    dsimp only [OrderThreeFitsSupport] at hs
    exfalso
    apply orderThree_zero12_not_globalMax hA hmass hmax
    · exact hz 0 0 (by rw [hs]; rfl)
    · exact hz 0 1 (by rw [hs]; rfl)
    · exact hp 0 2 (by rw [hs]; rfl)
    · intro j
      constructor <;> apply hp <;> rw [hs] <;> fin_cases j <;> rfl
  | zero22 =>
    dsimp only [OrderThreeFitsSupport] at hs
    exfalso
    apply orderThree_zero22_not_globalMax hA hmass hmax
    · exact hz 0 0 (by rw [hs]; rfl)
    · exact hz 0 1 (by rw [hs]; rfl)
    · exact hz 1 0 (by rw [hs]; rfl)
    · exact hz 1 1 (by rw [hs]; rfl)
    · intro i
      apply hp
      rw [hs]
      fin_cases i <;> rfl
    · constructor <;> apply hp <;> rw [hs] <;> rfl
  | twoProper =>
    dsimp only [OrderThreeFitsSupport] at hs
    have h00 := hz 0 0 (by rw [hs]; rfl)
    have h21 := hz 2 1 (by rw [hs]; rfl)
    have heq : A = orderThreeTwoProperBoard (A 1 0) (A 2 0) (A 0 1) (A 1 1) (A 0 2) (A 2 2) (A 1 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [orderThreeTwoProperBoard, h00, h21]
    exfalso
    apply orderThree_two_proper_not_globalMax
      (hp 1 0 (by rw [hs]; rfl)) (hp 2 0 (by rw [hs]; rfl))
      (hp 0 1 (by rw [hs]; rfl)) (hp 1 1 (by rw [hs]; rfl))
      (hp 0 2 (by rw [hs]; rfl)) (hp 2 2 (by rw [hs]; rfl))
      (hp 1 2 (by rw [hs]; rfl))
    · simpa only [← heq] using hmass
    · simpa only [← heq] using hmax
  | cycle =>
    dsimp only [OrderThreeFitsSupport] at hs
    have h00 := hz 0 0 (by rw [hs]; rfl)
    have h21 := hz 2 1 (by rw [hs]; rfl)
    have h12 := hz 1 2 (by rw [hs]; rfl)
    have heq : A = orderThreeTwoProperBoard (A 1 0) (A 2 0) (A 0 1) (A 1 1) (A 0 2) (A 2 2) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [orderThreeTwoProperBoard, h00, h21, h12]
    exfalso
    apply orderThree_cycle_not_globalMax
      (hp 1 0 (by rw [hs]; rfl)) (hp 2 0 (by rw [hs]; rfl))
      (hp 0 1 (by rw [hs]; rfl)) (hp 1 1 (by rw [hs]; rfl))
      (hp 0 2 (by rw [hs]; rfl)) (hp 2 2 (by rw [hs]; rfl))
    · simpa only [← heq] using hmass
    · simpa only [← heq] using hmax
  | singletonOpposite =>
    dsimp only [OrderThreeFitsSupport] at hs
    exfalso
    apply orderThree_singleton_opposite_not_globalMax hA hmass hmax
    · exact hz 0 1 (by rw [hs]; rfl)
    · exact hz 1 0 (by rw [hs]; rfl)
    · exact hz 2 0 (by rw [hs]; rfl)
    · exact hp 0 0 (by rw [hs]; rfl)
    · exact hp 0 2 (by rw [hs]; rfl)
    · intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · constructor <;> apply hp <;> rw [hs] <;> rfl
      · constructor <;> apply hp <;> rw [hs] <;> rfl
  | containing =>
    rcases hs with ⟨hp00, hp01, hp11, hp22, hz10, hz20, hz21⟩
    have h10 := hz 1 0 hz10
    have h20 := hz 2 0 hz20
    have h21 := hz 2 1 hz21
    have heq : A = orderThreeSingletonBoard (A 0 0) (A 0 1) (A 1 1) (A 0 2) (A 1 2) (A 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [orderThreeSingletonBoard, h10, h20, h21]
    have hcommon := dittert_three_globalMax_gradient_eq hA hmass hmax (0,0) (0,1)
      (hp 0 0 hp00) (hp 0 1 hp01)
    have hmiss := dittert_three_globalMax_gradient_le hA hmass hmax (1,0) (1,1) (hp 1 1 hp11)
    rw [heq] at hcommon hmiss
    exact (orderThree_singleton_containing_not_stationary (hp 1 1 hp11) (hA 0 2) (hA 1 2)
      (hp 2 2 hp22) hcommon hmiss).elim
  | twoSingletons =>
    rcases hs with ⟨hp00, hp11, hp22, hz01, hz10, hz20, hz21⟩
    have h01 := hz 0 1 hz01
    have h10 := hz 1 0 hz10
    have h20 := hz 2 0 hz20
    have h21 := hz 2 1 hz21
    have heq : A = orderThreeSingletonBoard (A 0 0) 0 (A 1 1) (A 0 2) (A 1 2) (A 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [orderThreeSingletonBoard, h01, h10, h20, h21]
    have hmiss0 := dittert_three_globalMax_gradient_le hA hmass hmax (1,0) (0,0) (hp 0 0 hp00)
    have hmiss1 := dittert_three_globalMax_gradient_le hA hmass hmax (0,1) (1,1) (hp 1 1 hp11)
    rw [heq] at hmiss0 hmiss1
    exact (orderThree_two_singletons_not_stationary (hp 0 0 hp00) (hp 1 1 hp11) (hp 2 2 hp22)
      hmiss0 hmiss1).elim
  | disjointSquare =>
    rcases hs with ⟨hz01, hz02, hz10, hz20⟩
    have h01 := hz 0 1 hz01
    have h02 := hz 0 2 hz02
    have h10 := hz 1 0 hz10
    have h20 := hz 2 0 hz20
    have heq : A = orderThreeDisjointSquareBoard (A 0 0) (A 1 1) (A 1 2) (A 2 1) (A 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [orderThreeDisjointSquareBoard, h01, h02, h10, h20]
    have hm : A 0 0+A 1 1+A 1 2+A 2 1+A 2 2 = 3 := by
      simpa [totalMass, rowSum, Fin.sum_univ_succ, h01, h02, h10, h20, add_assoc] using hmass
    have hbound := orderThree_disjoint_square_bound (hA 0 0) (hA 1 1) (hA 1 2) (hA 2 1) (hA 2 2) hm
    rw [← heq] at hbound
    exfalso
    linarith
  | disjointCross =>
    rcases hs with ⟨hz02, hz10, hz11, hz20, hz21⟩
    have h02 := hz 0 2 hz02
    have h10 := hz 1 0 hz10
    have h11 := hz 1 1 hz11
    have h20 := hz 2 0 hz20
    have h21 := hz 2 1 hz21
    have heq : A = orderThreeDisjointCrossBoard (A 0 0) (A 0 1) (A 1 2) (A 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [orderThreeDisjointCrossBoard, h02, h10, h11, h20, h21]
    have hm : A 0 0+A 0 1+A 1 2+A 2 2 = 3 := by
      simpa [totalMass, rowSum, Fin.sum_univ_succ, h02, h10, h11, h20, h21, add_assoc] using hmass
    have hbound := orderThree_disjoint_cross_bound (hA 0 0) (hA 0 1) (hA 1 2) (hA 2 2) hm
    rw [← heq] at hbound
    exfalso
    linarith

/- The support classification is applied only after deriving positive marginals
from global maximality on the entire nonnegative mass-three simplex. -/
theorem orderThree_globalMax_uniform (A : Board 3 3)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 3)
    (hmax : ∀ B : Board 3 3, (∀ i j, 0 ≤ B i j) → totalMass B = 3 →
      dittertFunctional B ≤ dittertFunctional A) : A = uniformDittertMatrix 3 := by
  have hcont := dittert_globalMax_isContender (by decide : 0 < 3) A hmax
  obtain ⟨hr, hc⟩ := dittert_contender_marginals_pos (by decide : 2 ≤ 3) A hA hmass hcont
  have hrow (i : Fin 3) : ∃ j, orderThreeSupportMatrix A i j = true := by
    obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hA i j)).mp (hr i)
    exact ⟨j, (orderThreeSupportMatrix_pos A i j).mpr hj⟩
  have hcol (j : Fin 3) : ∃ i, orderThreeSupportMatrix A i j = true := by
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hA i j)).mp (hc j)
    exact ⟨i, (orderThreeSupportMatrix_pos A i j).mpr hi⟩
  obtain ⟨r, c, t, k, hk⟩ := orderThree_boolean_support_classification (orderThreeSupportMatrix A) hrow hcol
  let er := orderThreeAxisEquiv r
  let ec := orderThreeAxisEquiv c
  have hperm : totalMass (A.submatrix er ec) = 3 := (totalMass_permuted_square A er ec).trans hmass
  have hp : ∀ i j, 0 ≤ (A.submatrix er ec) i j := fun i j => hA (er i) (ec j)
  have hg := dittert_globalMax_permuted_square hmax er ec
  cases t
  · change OrderThreeFitsSupport (orderThreeSupportMatrix (A.submatrix er ec)) k at hk
    exact square_uniform_of_permuted_uniform er ec
      (orderThree_canonical_support_globalMax_uniform hp hperm hg k hk)
  · change OrderThreeFitsSupport (orderThreeSupportMatrix (A.submatrix er ec).transpose) k at hk
    have hu := orderThree_canonical_support_globalMax_uniform (fun i j => hp j i)
      ((totalMass_matrix_transpose _).trans hperm) (dittert_globalMax_transpose hg) k hk
    apply square_uniform_of_permuted_uniform er ec
    ext i j
    exact congrFun (congrFun hu j) i

/-- Dittert's inequality at order three on the full nonnegative mass-three
domain, with the uniform matrix as the unique equality case. -/
theorem dittert_order_three : DittertMaximizer 3 :=
  dittertMaximizer_of_globalMax_uniform (by decide) orderThree_globalMax_uniform

/-- The equivalent iid-cell separation endpoint, including unique equality. -/
theorem uniformMaximizer_three_three_three : UniformMaximizer 3 3 3 :=
  (uniformMaximizer_iff_dittertMaximizer (by decide : 0 < 3)).mpr dittert_order_three

end DittertRybin
