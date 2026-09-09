import DR.Square.Normalization
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Stationarity under a normalized row scaling

At a global Dittert maximum, multiply one row by exp(t), then renormalize
the total mass. This curve stays in the same support face for every real t.
Its derivative gives the row stationarity equation directly, without
asserting derivative equality at zero cells or choosing permanent minors.
-/

namespace DittertRybin

open scoped BigOperators

/-- Multiply one row by a scalar; this preserves every zero cell. -/
def scaleOneRow {m n : ℕ} (A : Board m n) (i : Fin m) (c : ℝ) : Board m n :=
  fun r j => (if r = i then c else 1) * A r j

theorem rowSum_scaleOneRow {m n : ℕ} (A : Board m n) (i r : Fin m) (c : ℝ) :
    rowSum (scaleOneRow A i c) r = (if r = i then c else 1) * rowSum A r := by
  simp [rowSum, scaleOneRow, Finset.mul_sum]

theorem colSum_scaleOneRow {m n : ℕ} (A : Board m n) (i : Fin m) (c : ℝ) (j : Fin n) :
    colSum (scaleOneRow A i c) j = colSum A j + (c - 1) * A i j := by
  have h (r : Fin m) : (if r = i then c else 1) * A r j =
      A r j + if r = i then (c - 1) * A i j else 0 := by
    split_ifs with hr
    · subst r; ring
    · ring
  simp [colSum, scaleOneRow, h, Finset.sum_add_distrib]

theorem totalMass_scaleOneRow {m n : ℕ} (A : Board m n) (i : Fin m) (c : ℝ) :
    totalMass (scaleOneRow A i c) = totalMass A + (c - 1) * rowSum A i := by
  rw [totalMass_eq_sum_colSum, totalMass_eq_sum_colSum A]
  simp only [colSum_scaleOneRow, Finset.sum_add_distrib, ← Finset.mul_sum, rowSum]

theorem permanent_scaleOneRow {n : ℕ} (A : Board n n) (i : Fin n) (c : ℝ) :
    (scaleOneRow A i c).permanent = c * A.permanent := by
  change Matrix.permanent (fun r j => (if r = i then c else 1) * A r j) = _
  rw [permanent_scale_rows]
  simp

theorem dittertFunctional_scaleOneRow {n : ℕ} (A : Board n n) (i : Fin n) (c : ℝ) :
    dittertFunctional (scaleOneRow A i c) =
      c * (∏ r, rowSum A r) +
      (∏ j, (colSum A j + (c - 1) * A i j)) - c * A.permanent := by
  simp only [dittertFunctional, rowSum_scaleOneRow, colSum_scaleOneRow,
    permanent_scaleOneRow, Finset.prod_mul_distrib]
  simp

/-- Derivative of a finite product in logarithmic-derivative form, at nonzero values. -/
theorem hasDerivAt_product_of_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (d : ι → ℝ) (x : ℝ)
    (hd : ∀ i, HasDerivAt (f i) (d i) x) (hn : ∀ i, f i x ≠ 0) :
    HasDerivAt (fun t => ∏ i, f i t)
      ((∏ i, f i x) * ∑ i, d i / f i x) x := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd i)
  convert! h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [smul_eq_mul]
  field_simp [hn i]

/-- The actual derivative of the unnormalized positive row tilt. -/
theorem hasDerivAt_dittert_rowExp {n : ℕ} (A : Board n n) (i : Fin n)
    (hc : ∀ j, colSum A j ≠ 0) :
    HasDerivAt (fun t => dittertFunctional (scaleOneRow A i (Real.exp t)))
      ((∏ r, rowSum A r) - A.permanent + (∏ j, colSum A j) *
        ∑ j, A i j / colSum A j) 0 := by
  have he : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have hprod := hasDerivAt_product_of_ne_zero
    (fun j t => colSum A j + (Real.exp t - 1) * A i j) (fun j => A i j) 0
    (fun j => by simpa using ((he.sub_const 1).mul_const (A i j)).const_add (colSum A j))
    (fun j => by simpa using hc j)
  have hd := ((he.mul_const (∏ r, rowSum A r)).add hprod).sub
    (he.mul_const A.permanent)
  simp only [Real.exp_zero, sub_self, zero_mul, add_zero, one_mul] at hd
  convert! hd using 1
  · funext t
    exact dittertFunctional_scaleOneRow A i (Real.exp t)
  · ring

/-- Renormalized exponential row scaling on the mass-n simplex. -/
noncomputable def normalizedRowExp {n : ℕ} (A : Board n n) (i : Fin n) (t : ℝ) : Board n n :=
  ((n : ℝ) / (n + (Real.exp t - 1) * rowSum A i)) • scaleOneRow A i (Real.exp t)

theorem normalizedRowExp_zero {n : ℕ} (hn : 0 < n) (A : Board n n) (i : Fin n) :
    normalizedRowExp A i 0 = A := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  ext r j
  simp [normalizedRowExp, Real.exp_zero, hn0, scaleOneRow]

theorem normalizedRowExp_feasible {n : ℕ} (A : Board n n) (i : Fin n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n) (hri : 0 < rowSum A i) (t : ℝ) :
    (∀ r j, 0 ≤ normalizedRowExp A i t r j) ∧ totalMass (normalizedRowExp A i t) = n := by
  have hri_le : rowSum A i ≤ n := by
    rw [← hmass]
    exact Finset.single_le_sum (fun r _ => rowSum_nonneg hA r) (Finset.mem_univ i)
  have hd : 0 < (n : ℝ) + (Real.exp t - 1) * rowSum A i := by
    nlinarith [mul_pos (Real.exp_pos t) hri]
  constructor
  · intro r j
    apply mul_nonneg (div_nonneg (Nat.cast_nonneg n) hd.le)
    apply mul_nonneg _ (hA r j)
    split_ifs <;> positivity
  · rw [normalizedRowExp, totalMass_smul, totalMass_scaleOneRow, hmass]
    exact div_mul_cancel₀ _ hd.ne'

theorem hasDerivAt_rowExp_normalizer_power {n : ℕ} (hn : 0 < n) (r : ℝ) :
    HasDerivAt (fun t : ℝ => ((n : ℝ) / (n + (Real.exp t - 1) * r)) ^ n) (-r) 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have hd : HasDerivAt (fun t => (n : ℝ) + (Real.exp t - 1) * r) r 0 := by
    simpa using ((he.sub_const 1).mul_const r).const_add (n : ℝ)
  have hquot := (hasDerivAt_const (0 : ℝ) (n : ℝ)).div hd (by simpa using hn0)
  have hp := hquot.pow n
  convert! hp using 1
  simp only [Pi.div_apply, Real.exp_zero, sub_self, zero_mul, add_zero, div_self hn0, one_pow,
    zero_mul, zero_sub]
  field_simp

/-- The row stationarity equation at an actual global maximum, including boundary support. -/
theorem dittert_globalMax_row_identity {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hr : ∀ r, 0 < rowSum A r) (hc : ∀ j, 0 < colSum A j)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (i : Fin n) :
    dittertFunctional A * rowSum A i = (∏ r, rowSum A r) - A.permanent +
      (∏ j, colSum A j) * ∑ j, A i j / colSum A j := by
  have hderiv := (hasDerivAt_rowExp_normalizer_power hn (rowSum A i)).mul
    (hasDerivAt_dittert_rowExp A i (fun j => (hc j).ne'))
  have hrow1 : scaleOneRow A i 1 = A := by
    ext r j; simp [scaleOneRow]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [Real.exp_zero, hrow1, sub_self, zero_mul, add_zero, div_self hn0,
    one_pow, one_mul] at hderiv
  have hd : HasDerivAt (fun t => dittertFunctional (normalizedRowExp A i t))
      (-rowSum A i * dittertFunctional A + ((∏ r, rowSum A r) - A.permanent +
        (∏ j, colSum A j) * ∑ j, A i j / colSum A j)) 0 := by
    convert! hderiv using 1
    funext t
    exact dittertFunctional_smul _ _
  have hlocal : IsLocalMax (fun t => dittertFunctional (normalizedRowExp A i t)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change dittertFunctional (normalizedRowExp A i t) ≤ dittertFunctional (normalizedRowExp A i 0)
    rw [normalizedRowExp_zero hn]
    obtain ⟨hpos, hmass'⟩ := normalizedRowExp_feasible A i hA hmass (hr i) t
    exact hmax _ hpos hmass'
  have hz := hlocal.hasDerivAt_eq_zero hd
  linarith

theorem dittertFunctional_transpose {n : ℕ} (A : Board n n) :
    dittertFunctional A.transpose = dittertFunctional A := by
  simp [dittertFunctional, rowSum, colSum, Matrix.transpose_apply, add_comm]

/-- The column counterpart follows from the same feasible curve on the transpose. -/
theorem dittert_globalMax_col_identity {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hr : ∀ r, 0 < rowSum A r) (hc : ∀ j, 0 < colSum A j)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (j : Fin n) :
    dittertFunctional A * colSum A j = (∏ r, colSum A r) - A.permanent +
      (∏ i, rowSum A i) * ∑ i, A i j / rowSum A i := by
  have hmassT : totalMass A.transpose = n := by
    change (∑ j, colSum A j) = n
    rw [← totalMass_eq_sum_colSum, hmass]
  have hmaxT (B : Board n n) (hB : ∀ i j, 0 ≤ B i j) (hM : totalMass B = n) :
      dittertFunctional B ≤ dittertFunctional A.transpose := by
    rw [dittertFunctional_transpose]
    have hBT : totalMass B.transpose = n := by
      change (∑ j, colSum B j) = n
      rw [← totalMass_eq_sum_colSum, hM]
    simpa only [dittertFunctional_transpose] using hmax B.transpose (fun i j => hB j i) hBT
  simpa only [dittertFunctional_transpose, rowSum, colSum, Matrix.transpose_apply,
    Matrix.permanent_transpose] using
    dittert_globalMax_row_identity hn A.transpose (fun r j => hA j r) hmassT hc hr hmaxT j

theorem sum_row_column_deviation {n : ℕ} (A : Board n n) (i : Fin n)
    (hc : ∀ j, colSum A j ≠ 0) :
    (∑ j, A i j * (colSum A j - 1) / colSum A j) =
      rowSum A i - ∑ j, A i j / colSum A j := by
  rw [rowSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hc j]

/-- The exact first stationary equation used to construct the spectral pair. -/
theorem dittert_globalMax_row_deviation {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hr : ∀ r, 0 < rowSum A r) (hc : ∀ j, 0 < colSum A j)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (i : Fin n) :
    (((∏ r, rowSum A r) - A.permanent) / (∏ j, colSum A j)) * (rowSum A i - 1) =
      -(∑ j, A i j * (colSum A j - 1) / colSum A j) := by
  have hid := dittert_globalMax_row_identity hn A hA hmass hr hc hmax i
  have hC : (∏ j, colSum A j) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun j _ => hc j))
  rw [sum_row_column_deviation A i (fun j => (hc j).ne')]
  unfold dittertFunctional at hid
  apply (mul_right_cancel₀ hC)
  field_simp
  nlinarith [hid]

/-- The second stationary equation is the transpose of the first. -/
theorem dittert_globalMax_col_deviation {n : ℕ} (hn : 0 < n) (A : Board n n)
    (hA : ∀ r j, 0 ≤ A r j) (hmass : totalMass A = n)
    (hr : ∀ r, 0 < rowSum A r) (hc : ∀ j, 0 < colSum A j)
    (hmax : ∀ B : Board n n, (∀ r j, 0 ≤ B r j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (j : Fin n) :
    (((∏ r, colSum A r) - A.permanent) / (∏ i, rowSum A i)) * (colSum A j - 1) =
      -(∑ i, A i j * (rowSum A i - 1) / rowSum A i) := by
  have hid := dittert_globalMax_col_identity hn A hA hmass hr hc hmax j
  have hR : (∏ i, rowSum A i) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hr i))
  have hsum := sum_row_column_deviation A.transpose j (fun i => (hr i).ne')
  change (∑ i, A i j * (rowSum A i - 1) / rowSum A i) =
    colSum A j - ∑ i, A i j / rowSum A i at hsum
  rw [hsum]
  unfold dittertFunctional at hid
  apply (mul_right_cancel₀ hR)
  field_simp
  nlinarith [hid]

end DittertRybin
