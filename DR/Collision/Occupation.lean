import DR.Semimatching
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Row occupation conditional on distinct columns

All quantities are finite sums over the actual ordered iid cell samples.
The conditional weights are divided by the mass of distinct columns. Their
algebraic identities are meaningful even when this denominator vanishes;
normalization to a probability law requires it to be positive.

The occupation vector is zero unless all rows are distinct. Otherwise it
has exactly k entries equal to one. This gives the exact first-moment identity
and the quadratic-moment bound. The normalized avoidance kernel retains its
essential diagonal correction.
-/

namespace DittertRybin

open scoped BigOperators

/-- The rows that occur in an ordered sample. -/
def occupiedRows {m n k : ℕ} (s : Fin k → Fin m × Fin n) : Finset (Fin m) :=
  Finset.univ.image (fun t => (s t).1)

/-- Indicator that all sampled rows are distinct. -/
noncomputable def distinctRowsIndicator {m n k : ℕ} (s : Fin k → Fin m × Fin n) : ℝ := by
  classical
  exact if RowsDistinct s then 1 else 0

/-- Indicator that rows are distinct and row i is occupied. -/
noncomputable def rowOccupation {m n k : ℕ} (s : Fin k → Fin m × Fin n) (i : Fin m) : ℝ := by
  classical
  exact if RowsDistinct s ∧ i ∈ occupiedRows s then 1 else 0

/-- Indicator that rows are distinct and both specified rows are absent. -/
noncomputable def rowsAbsentIndicator {m n k : ℕ} (s : Fin k → Fin m × Fin n)
    (i h : Fin m) : ℝ := by
  classical
  exact if RowsDistinct s ∧ i ∉ occupiedRows s ∧ h ∉ occupiedRows s then 1 else 0

noncomputable def columnDistinctMass {m n : ℕ} (P : Board m n) (k : ℕ) : ℝ :=
  eventMass (fun a : Fin m × Fin n => P a.1 a.2) {s : Fin k → Fin m × Fin n | ColsDistinct s}

/-- The actual conditional weight of a sample after requiring distinct columns. -/
noncomputable def columnConditionedWeight {m n : ℕ} (P : Board m n) (k : ℕ)
    (s : Fin k → Fin m × Fin n) : ℝ := by
  classical
  exact (if ColsDistinct s then sampleMass (fun a : Fin m × Fin n => P a.1 a.2) s else 0) /
    columnDistinctMass P k

noncomputable def columnConditionalExpectation {m n : ℕ} (P : Board m n) (k : ℕ)
    (f : (Fin k → Fin m × Fin n) → ℝ) : ℝ :=
  ∑ s, columnConditionedWeight P k s * f s

/-- q0 = the conditional probability of distinct rows given distinct columns. -/
noncomputable def conditionalRowsProbability {m n : ℕ} (P : Board m n) (k : ℕ) : ℝ :=
  columnConditionalExpectation P k distinctRowsIndicator

/-- qi = the conditional first moment of the row-i occupation indicator. -/
noncomputable def occupationProbability {m n : ℕ} (P : Board m n) (k : ℕ) (i : Fin m) : ℝ :=
  columnConditionalExpectation P k (fun s => rowOccupation s i)

/-- Conditional second moment E[Zi Zh | distinct columns]. -/
noncomputable def occupationSecondMoment {m n : ℕ} (P : Board m n) (k : ℕ)
    (i h : Fin m) : ℝ :=
  columnConditionalExpectation P k (fun s => rowOccupation s i * rowOccupation s h)

noncomputable def conditionalRowsAbsent {m n : ℕ} (P : Board m n) (k : ℕ)
    (i h : Fin m) : ℝ :=
  columnConditionalExpectation P k (fun s => rowsAbsentIndicator s i h)

/-- The normalized G/E probability kernel: diagonal one, and conditional avoidance off diagonal. -/
noncomputable def occupationKernel {m n : ℕ} (P : Board m n) (k : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i h => if i = h then 1 else 1 - conditionalRowsAbsent P k i h

theorem occupiedRows_card {m n k : ℕ} (s : Fin k → Fin m × Fin n)
    (hR : RowsDistinct s) : (occupiedRows s).card = k := by
  simpa [occupiedRows] using Finset.card_image_of_injective Finset.univ hR

theorem rowOccupation_nonneg {m n k : ℕ} (s : Fin k → Fin m × Fin n) (i : Fin m) :
    0 ≤ rowOccupation s i := by
  classical
  unfold rowOccupation
  split_ifs <;> norm_num

theorem rowOccupation_sq {m n k : ℕ} (s : Fin k → Fin m × Fin n) (i : Fin m) :
    rowOccupation s i * rowOccupation s i = rowOccupation s i := by
  classical
  unfold rowOccupation
  split_ifs <;> norm_num

/-- Pointwise, the occupation vector has k ones or is the zero vector. -/
theorem sum_rowOccupation {m n k : ℕ} (s : Fin k → Fin m × Fin n) :
    (∑ i, rowOccupation s i) = (k : ℝ) * distinctRowsIndicator s := by
  classical
  by_cases hR : RowsDistinct s
  · simp [rowOccupation, distinctRowsIndicator, hR,
      occupiedRows_card s hR]
  · simp [rowOccupation, distinctRowsIndicator, hR]

/-- Pointwise Cauchy--Schwarz uses the occupied k coordinates, without an ambient-dimension loss. -/
theorem rowOccupation_quadratic_bound {m n k : ℕ} (s : Fin k → Fin m × Fin n)
    (x : Fin m → ℝ) :
    (∑ i, rowOccupation s i * x i) ^ 2 ≤ (k : ℝ) * ∑ i, rowOccupation s i * x i ^ 2 := by
  classical
  by_cases hR : RowsDistinct s
  · have h := sq_sum_le_card_mul_sum_sq (s := occupiedRows s) (f := x)
    simpa [rowOccupation, hR, ite_mul, ← Finset.sum_filter, occupiedRows_card s hR] using h
  · simp [rowOccupation, hR]

theorem rowsAbsentIndicator_eq {m n k : ℕ} (s : Fin k → Fin m × Fin n) (i h : Fin m) :
    rowsAbsentIndicator s i h = distinctRowsIndicator s - rowOccupation s i - rowOccupation s h +
      rowOccupation s i * rowOccupation s h := by
  classical
  by_cases hR : RowsDistinct s <;> by_cases hi : i ∈ occupiedRows s <;>
    by_cases hh : h ∈ occupiedRows s <;>
    norm_num [rowsAbsentIndicator, distinctRowsIndicator, rowOccupation, hR, hi, hh]

theorem columnDistinctMass_nonneg {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ columnDistinctMass P k :=
  eventMass_nonneg (fun a : Fin m × Fin n => P a.1 a.2) (fun a => hP a.1 a.2) _

theorem columnConditionedWeight_nonneg {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (s : Fin k → Fin m × Fin n) :
    0 ≤ columnConditionedWeight P k s := by
  classical
  apply div_nonneg _ (columnDistinctMass_nonneg P k hP)
  by_cases hD : ColsDistinct s
  · simpa [hD] using sampleMass_nonneg (fun a : Fin m × Fin n => P a.1 a.2)
      (fun a => hP a.1 a.2) s
  · simp [hD]

theorem sum_columnConditionedWeight {m n : ℕ} (P : Board m n) (k : ℕ)
    (hZ : 0 < columnDistinctMass P k) : (∑ s, columnConditionedWeight P k s) = 1 := by
  classical
  simp only [columnConditionedWeight, ← Finset.sum_div]
  change columnDistinctMass P k / columnDistinctMass P k = 1
  exact div_self hZ.ne'

theorem columnConditionalExpectation_mono {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) {f g : (Fin k → Fin m × Fin n) → ℝ}
    (hfg : ∀ s, f s ≤ g s) : columnConditionalExpectation P k f ≤ columnConditionalExpectation P k g :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hfg s)
    (columnConditionedWeight_nonneg P k hP s)

/-- The exact conditional first-moment identity sum qi = k q0. -/
theorem sum_occupationProbability {m n : ℕ} (P : Board m n) (k : ℕ) :
    (∑ i, occupationProbability P k i) = (k : ℝ) * conditionalRowsProbability P k := by
  simp only [occupationProbability, conditionalRowsProbability, columnConditionalExpectation]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_rowOccupation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem occupationSecondMoment_diagonal {m n : ℕ} (P : Board m n) (k : ℕ) (i : Fin m) :
    occupationSecondMoment P k i i = occupationProbability P k i := by
  simp only [occupationSecondMoment, occupationProbability, rowOccupation_sq]

/-- The exact conditional quadratic bound E[(Z dot x)^2] ≤ k sum qi xi^2. -/
theorem occupation_quadratic_bound {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (x : Fin m → ℝ) :
    columnConditionalExpectation P k (fun s => (∑ i, rowOccupation s i * x i) ^ 2) ≤
      (k : ℝ) * ∑ i, occupationProbability P k i * x i ^ 2 := by
  calc
    _ ≤ columnConditionalExpectation P k
        (fun s => (k : ℝ) * ∑ i, rowOccupation s i * x i ^ 2) :=
      columnConditionalExpectation_mono P k hP (fun s => rowOccupation_quadratic_bound s x)
    _ = _ := by
      simp only [columnConditionalExpectation, occupationProbability]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

theorem conditionalRowsAbsent_eq {m n : ℕ} (P : Board m n) (k : ℕ) (i h : Fin m) :
    conditionalRowsAbsent P k i h = conditionalRowsProbability P k - occupationProbability P k i -
      occupationProbability P k h + occupationSecondMoment P k i h := by
  simp only [conditionalRowsAbsent, conditionalRowsProbability, occupationProbability,
    occupationSecondMoment, columnConditionalExpectation, rowsAbsentIndicator_eq,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The diagonal term is required: omitting it changes every diagonal entry of G/E. -/
theorem occupationKernel_eq {m n : ℕ} (P : Board m n) (k : ℕ) (i h : Fin m) :
    occupationKernel P k i h = 1 - conditionalRowsProbability P k + occupationProbability P k i +
      occupationProbability P k h - occupationSecondMoment P k i h +
        if i = h then conditionalRowsProbability P k - occupationProbability P k i else 0 := by
  by_cases he : i = h
  · subst h
    rw [occupationKernel, if_pos rfl, occupationSecondMoment_diagonal, if_pos rfl]
    ring
  · rw [occupationKernel, if_neg he, conditionalRowsAbsent_eq, if_neg he]
    ring

theorem columnConditionalExpectation_const {m n : ℕ} (P : Board m n) (k : ℕ)
    (hZ : 0 < columnDistinctMass P k) (c : ℝ) :
    columnConditionalExpectation P k (fun _ => c) = c := by
  simp only [columnConditionalExpectation, ← Finset.sum_mul]
  rw [sum_columnConditionedWeight P k hZ, one_mul]

open Classical in
/-- Conditional indicators agree exactly with the ratio of the corresponding actual event masses. -/
theorem columnConditionalExpectation_indicator {m n : ℕ} (P : Board m n) (k : ℕ)
    (E : Set (Fin k → Fin m × Fin n)) :
    columnConditionalExpectation P k (fun s => if s ∈ E then 1 else 0) =
      eventMass (fun a : Fin m × Fin n => P a.1 a.2)
        {s : Fin k → Fin m × Fin n | ColsDistinct s ∧ s ∈ E} / columnDistinctMass P k := by
  classical
  unfold columnConditionalExpectation eventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hD : ColsDistinct s <;> by_cases hE : s ∈ E <;>
    simp [columnConditionedWeight, hD, hE]

theorem conditionalRowsProbability_eq_eventMass {m n : ℕ} (P : Board m n) (k : ℕ) :
    conditionalRowsProbability P k =
      eventMass (fun a : Fin m × Fin n => P a.1 a.2)
        {s : Fin k → Fin m × Fin n | ColsDistinct s ∧ RowsDistinct s} / columnDistinctMass P k := by
  classical
  unfold conditionalRowsProbability
  convert columnConditionalExpectation_indicator P k {s | RowsDistinct s} using 1
  · apply congrArg (columnConditionalExpectation P k)
    funext s
    by_cases hR : RowsDistinct s <;> simp [distinctRowsIndicator, hR]
  · rfl

theorem conditionalRowsAbsent_eq_eventMass {m n : ℕ} (P : Board m n) (k : ℕ) (i h : Fin m) :
    conditionalRowsAbsent P k i h =
      eventMass (fun a : Fin m × Fin n => P a.1 a.2)
        {s : Fin k → Fin m × Fin n | ColsDistinct s ∧ RowsDistinct s ∧
          i ∉ occupiedRows s ∧ h ∉ occupiedRows s} / columnDistinctMass P k := by
  classical
  unfold conditionalRowsAbsent
  convert columnConditionalExpectation_indicator P k
    {s | RowsDistinct s ∧ i ∉ occupiedRows s ∧ h ∉ occupiedRows s} using 1
  · apply congrArg (columnConditionalExpectation P k)
    funext s
    by_cases hs : RowsDistinct s ∧ i ∉ occupiedRows s ∧ h ∉ occupiedRows s <;>
      simp [rowsAbsentIndicator, hs]
  · rfl

theorem conditionalRowsProbability_nonneg {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ conditionalRowsProbability P k := by
  classical
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg (columnConditionedWeight_nonneg P k hP s)
  unfold distinctRowsIndicator
  split_ifs <;> norm_num

theorem conditionalRowsProbability_le_one {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (hZ : 0 < columnDistinctMass P k) :
    conditionalRowsProbability P k ≤ 1 := by
  classical
  calc
    _ ≤ columnConditionalExpectation P k (fun _ => 1) := by
      apply columnConditionalExpectation_mono P k hP
      intro s
      unfold distinctRowsIndicator
      split_ifs <;> norm_num
    _ = _ := columnConditionalExpectation_const P k hZ 1

theorem occupationProbability_nonneg {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (i : Fin m) : 0 ≤ occupationProbability P k i :=
  Finset.sum_nonneg fun s _ => mul_nonneg
    (columnConditionedWeight_nonneg P k hP s) (rowOccupation_nonneg s i)

theorem occupationProbability_le_q0 {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (i : Fin m) :
    occupationProbability P k i ≤ conditionalRowsProbability P k := by
  classical
  apply columnConditionalExpectation_mono P k hP
  intro s
  by_cases hR : RowsDistinct s <;> by_cases hi : i ∈ occupiedRows s <;>
    simp [rowOccupation, distinctRowsIndicator, hR, hi]

theorem columnConditionalExpectation_sum {m n : ℕ} (P : Board m n) (k : ℕ)
    {ι : Type*} [Fintype ι] (f : ι → (Fin k → Fin m × Fin n) → ℝ) :
    columnConditionalExpectation P k (fun s => ∑ i, f i s) =
      ∑ i, columnConditionalExpectation P k (f i) := by
  simp only [columnConditionalExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem columnConditionalExpectation_const_mul {m n : ℕ} (P : Board m n) (k : ℕ)
    (c : ℝ) (f : (Fin k → Fin m × Fin n) → ℝ) :
    columnConditionalExpectation P k (fun s => c * f s) = c * columnConditionalExpectation P k f := by
  simp only [columnConditionalExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem columnConditionalExpectation_mul_const {m n : ℕ} (P : Board m n) (k : ℕ)
    (f : (Fin k → Fin m × Fin n) → ℝ) (c : ℝ) :
    columnConditionalExpectation P k (fun s => f s * c) = columnConditionalExpectation P k f * c := by
  simp only [columnConditionalExpectation, Finset.sum_mul, mul_assoc]

/-- The second-moment matrix represents the conditional quadratic moment exactly. -/
theorem occupationSecondMoment_quadratic {m n : ℕ} (P : Board m n) (k : ℕ) (x : Fin m → ℝ) :
    (∑ i, ∑ h, x i * occupationSecondMoment P k i h * x h) =
      columnConditionalExpectation P k (fun s => (∑ i, rowOccupation s i * x i) ^ 2) := by
  have he (s : Fin k → Fin m × Fin n) : (∑ i, rowOccupation s i * x i) ^ 2 =
      ∑ i, ∑ h, x i * (rowOccupation s i * rowOccupation s h) * x h := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro h _
    ring
  simp_rw [he, columnConditionalExpectation_sum, columnConditionalExpectation_mul_const,
    columnConditionalExpectation_const_mul]
  rfl

theorem occupationSecondMoment_quadratic_le {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (x : Fin m → ℝ) :
    (∑ i, ∑ h, x i * occupationSecondMoment P k i h * x h) ≤
      (k : ℝ) * ∑ i, occupationProbability P k i * x i ^ 2 := by
  rw [occupationSecondMoment_quadratic]
  exact occupation_quadratic_bound P k hP x

/-- The kernel's quadratic form keeps the diagonal contribution q0 minus qi. -/
theorem occupationKernel_quadratic_identity {m n : ℕ} (P : Board m n) (k : ℕ)
    (x : Fin m → ℝ) :
    (∑ i, ∑ h, x i * occupationKernel P k i h * x h) =
      (1 - conditionalRowsProbability P k) * (∑ i, x i) ^ 2 +
      2 * (∑ i, x i) * (∑ i, occupationProbability P k i * x i) -
      (∑ i, ∑ h, x i * occupationSecondMoment P k i h * x h) +
      conditionalRowsProbability P k * (∑ i, x i ^ 2) -
      ∑ i, occupationProbability P k i * x i ^ 2 := by
  have he (i h : Fin m) : x i * occupationKernel P k i h * x h =
      (1 - conditionalRowsProbability P k) * x i * x h +
      (occupationProbability P k i * x i) * x h +
      x i * (occupationProbability P k h * x h) -
      x i * occupationSecondMoment P k i h * x h +
      if i = h then (conditionalRowsProbability P k - occupationProbability P k i) * x i ^ 2 else 0 := by
    by_cases hih : i = h
    · subst h
      rw [occupationKernel, if_pos rfl, occupationSecondMoment_diagonal, if_pos rfl]
      ring
    · rw [occupationKernel_eq]
      simp only [if_neg hih]
      ring
  have hd : (∑ i, (conditionalRowsProbability P k - occupationProbability P k i) * x i ^ 2) =
      conditionalRowsProbability P k * (∑ i, x i ^ 2) -
        ∑ i, occupationProbability P k i * x i ^ 2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hd]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Bounding every qi by qmax gives the uncentered quadratic lower bound used in column averaging. -/
theorem occupationKernel_quadratic_lower {m n : ℕ} (P : Board m n) (k : ℕ)
    (hP : ∀ i j, 0 ≤ P i j) (x : Fin m → ℝ) (qmax : ℝ)
    (hq : ∀ i, occupationProbability P k i ≤ qmax) :
    (1 - conditionalRowsProbability P k) * (∑ i, x i) ^ 2 +
      2 * (∑ i, x i) * (∑ i, occupationProbability P k i * x i) +
      (conditionalRowsProbability P k - (k + 1 : ℝ) * qmax) * (∑ i, x i ^ 2) ≤
        ∑ i, ∑ h, x i * occupationKernel P k i h * x h := by
  have hmoment := occupationSecondMoment_quadratic_le P k hP x
  have hsum : (∑ i, occupationProbability P k i * x i ^ 2) ≤ qmax * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hq i) (sq_nonneg (x i))
  have hsum' := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ k + 1 by positivity)
  rw [occupationKernel_quadratic_identity]
  nlinarith

end DittertRybin
