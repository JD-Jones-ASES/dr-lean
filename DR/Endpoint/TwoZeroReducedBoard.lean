import DR.Endpoint.TwoZeroFaceStructure
import DR.Endpoint.TwoZeroPolynomial

/-! The actual matrix form forced by a least-norm minimum on the two-zero face.
The parameter rectangle follows from its doubly stochastic equations. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def twoZeroReducedBoard (n : ℕ) (a b : ℝ) : Board (n+2) (n+2) :=
  fun i j =>
    if i = 0 then (if j = 0 then 1-n*a else if j = 1 then 0 else a)
    else if i = 1 then (if j = 0 then 0 else if j = 1 then 1-n*b else b)
    else if j = 0 then a else if j = 1 then b else (1-a-b)/n

theorem LeastNormPermanentFaceMinimum.twoZero_reduced_form {n : ℕ} (hn : 0 < n)
    {A : Board (n+2) (n+2)} (hA : LeastNormPermanentFaceMinimum (twoZeroAllowed n) A) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1/(n : ℝ) ∧ 0 ≤ b ∧ b ≤ 1/(n : ℝ) ∧
      A = twoZeroReducedBoard n a b := by
  let o : Fin n := ⟨0,hn⟩
  let a : ℝ := A 0 o.succ.succ
  let b : ℝ := A 1 o.succ.succ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg (i j) : 0 ≤ A i j := nonneg_of_mem_doublyStochastic hA.1.1
  have h01 : A 0 1 = 0 := hA.1.2.1 0 1 (by simp [twoZeroAllowed])
  have h10 : A 1 0 = 0 := hA.1.2.1 1 0 (by simp [twoZeroAllowed])
  have htop (j : Fin n) : A 0 j.succ.succ = a :=
    hA.twoZero_ordinary_columns hn j o 0
  have hsecond (j : Fin n) : A 1 j.succ.succ = b :=
    hA.twoZero_ordinary_columns hn j o 1
  have hr0 : A 0 0+n*a = 1 := by
    have h := sum_row_of_mem_doublyStochastic hA.1.1 0
    simpa [Fin.sum_univ_succ, htop, h01] using h
  have hr1 : A 1 1+n*b = 1 := by
    have h := sum_row_of_mem_doublyStochastic hA.1.1 1
    simpa [Fin.sum_univ_succ, hsecond, h10] using h
  have hleft (i : Fin n) : A i.succ.succ 0 = a := by
    have h := sum_col_of_mem_doublyStochastic hA.1.1 0
    have hi (k : Fin n) : A k.succ.succ 0 = A i.succ.succ 0 :=
      congrFun (hA.twoZero_ordinary_rows hn k i) 0
    simp [Fin.sum_univ_succ, hi, h10] at h
    apply mul_left_cancel₀ hnR.ne'
    nlinarith only [h,hr0]
  have hnext (i : Fin n) : A i.succ.succ 1 = b := by
    have h := sum_col_of_mem_doublyStochastic hA.1.1 1
    have hi (k : Fin n) : A k.succ.succ 1 = A i.succ.succ 1 :=
      congrFun (hA.twoZero_ordinary_rows hn k i) 1
    simp [Fin.sum_univ_succ, hi, h01] at h
    apply mul_left_cancel₀ hnR.ne'
    nlinarith only [h,hr1]
  have hcore (i j : Fin n) : A i.succ.succ j.succ.succ = (1-a-b)/(n : ℝ) := by
    have h := sum_row_of_mem_doublyStochastic hA.1.1 i.succ.succ
    have hi (k : Fin n) : A i.succ.succ k.succ.succ = A i.succ.succ j.succ.succ :=
      hA.twoZero_ordinary_columns hn k j i.succ.succ
    simp [Fin.sum_univ_succ, hi, hleft, hnext] at h
    apply (eq_div_iff hnR.ne').mpr
    linarith
  have ha : 0 ≤ a := hnonneg 0 _
  have hb : 0 ≤ b := hnonneg 1 _
  have hna : a ≤ 1/(n : ℝ) := (le_div_iff₀ hnR).mpr (by nlinarith [hnonneg 0 0])
  have hnb : b ≤ 1/(n : ℝ) := (le_div_iff₀ hnR).mpr (by nlinarith [hnonneg 1 1])
  refine ⟨a,b,ha,hna,hb,hnb,?_⟩
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [twoZeroReducedBoard]; linarith
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [twoZeroReducedBoard, h01]
      | succ j => simp [twoZeroReducedBoard, htop, ← Fin.succ_zero_eq_one,
          -Fin.succ_zero_eq_one']
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [twoZeroReducedBoard, h10]
      | succ j =>
        cases j using Fin.cases with
        | zero => simp [twoZeroReducedBoard]; linarith
        | succ j =>
          simp only [Fin.succ_zero_eq_one]
          rw [hsecond]
          simp [twoZeroReducedBoard, ← Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one']
    | succ i =>
      cases j using Fin.cases with
      | zero => simp [twoZeroReducedBoard, hleft, ← Fin.succ_zero_eq_one,
          -Fin.succ_zero_eq_one']
      | succ j =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.succ_zero_eq_one]
          rw [hnext]
          simp [twoZeroReducedBoard, ← Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one']
        | succ j => simp [twoZeroReducedBoard, hcore, ← Fin.succ_zero_eq_one,
            -Fin.succ_zero_eq_one']

end DittertRybin
