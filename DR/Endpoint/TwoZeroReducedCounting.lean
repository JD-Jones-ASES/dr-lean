import DR.Endpoint.TwoZeroReducedBoard
import DR.Endpoint.NearEndpointPaddingCounting

/-! Exact signed permanent counting for the two-exceptional-row model.
Two Laplace expansions leave a matrix whose rows all coincide. -/
namespace DittertRybin
open scoped BigOperators

private def twoFront (n : ℕ) (a b x : ℝ) : Fin (n+2) → ℝ :=
  Fin.cases a (Fin.cases b (fun _ => x))

private theorem twoFront_delete {n : ℕ} (a b x : ℝ) (j : Fin (n+1))
    (k : Fin (n+2)) :
    twoFront (n+1) a b x (j.succ.succ.succAbove k) = twoFront n a b x k := by
  cases k using Fin.cases with
  | zero => simp [twoFront]
  | succ k =>
    cases k using Fin.cases with
    | zero => simp only [Fin.succ_succAbove_succ,Fin.succ_succAbove_zero]; rfl
    | succ k => simp [twoFront]

private theorem permanent_repeated_row {n : ℕ} (v : Fin n → ℝ) :
    Matrix.permanent (fun (_ : Fin n) j => v j) = (n.factorial : ℝ)*∏ j, v j := by
  simp [Matrix.permanent,Fintype.card_perm,nsmul_eq_mul]

private theorem permanent_one_exception {n : ℕ} (u v : Fin (n+1) → ℝ) :
    Matrix.permanent (Fin.cases u (fun _ => v)) =
      (n.factorial : ℝ)*∑ j, u j * ∏ k : Fin n, v (j.succAbove k) := by
  calc
    _ = ∑ j, u j * Matrix.permanent (fun (_ : Fin n) k => v (j.succAbove k)) :=
      permanent_expand_row_zero (Fin.cases u (fun _ => v))
    _ = _ := by
      simp only [permanent_repeated_row,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private theorem permanent_one_exception_twoFront (n : ℕ) (a b c d e x : ℝ) :
    Matrix.permanent (Fin.cases (twoFront (n+1) a b c)
      (fun _ => twoFront (n+1) d e x)) =
      ((n+2).factorial : ℝ)*(a*e*x^(n+1)+b*d*x^(n+1)+(n+1)*c*d*e*x^n) := by
  rw [permanent_one_exception,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp_rw [twoFront_delete]
  simp only [twoFront,Fin.cases_zero,Fin.cases_succ,Fin.zero_succAbove,
    Fin.succ_succAbove_zero,Fin.succ_succAbove_succ,Fin.prod_univ_succ]
  simp
  ring_nf
  simp

private def twoExceptional (n : ℕ) (d e a b x : ℝ) : Board (n+2) (n+2) :=
  Fin.cases (twoFront n d 0 a)
    (Fin.cases (twoFront n 0 e b) (fun _ => twoFront n a b x))

private theorem twoExceptional_permanent (n : ℕ) (d e a b x : ℝ) :
    (twoExceptional (n+2) d e a b x).permanent =
      ((n+2).factorial : ℝ)*(d*e*x^(n+2)+(n+2)*(d*b^2+e*a^2)*x^(n+1)+
        (n+2)*(n+1)*a^2*b^2*x^n) := by
  rw [permanent_expand_row_zero,Fin.sum_univ_succ,Fin.sum_univ_succ]
  have hzero : (fun r c : Fin (n+3) =>
      twoExceptional (n+2) d e a b x r.succ ((0 : Fin (n+4)).succAbove c)) =
      Fin.cases (twoFront (n+1) e b b) (fun _ => twoFront (n+1) b x x) := by
    funext r c
    cases r using Fin.cases with
    | zero =>
      cases c using Fin.cases with
      | zero => rfl
      | succ c => cases c using Fin.cases <;> rfl
    | succ r =>
      cases c using Fin.cases with
      | zero => rfl
      | succ c => cases c using Fin.cases <;> rfl
  have hord (j : Fin (n+2)) :
      (fun r c : Fin (n+3) => twoExceptional (n+2) d e a b x r.succ (j.succ.succ.succAbove c)) =
      Fin.cases (twoFront (n+1) 0 e b) (fun _ => twoFront (n+1) a b x) := by
    funext r c
    cases r using Fin.cases <;> simp only [twoExceptional,Fin.cases_succ,Fin.cases_zero]
    · exact twoFront_delete _ _ _ j c
    · exact twoFront_delete _ _ _ j c
  rw [hzero]
  simp_rw [hord]
  simp only [twoExceptional,twoFront,Fin.cases_zero,Fin.cases_succ,zero_mul,zero_add]
  change d * Matrix.permanent (Fin.cases (twoFront (n+1) e b b) (fun _ => twoFront (n+1) b x x)) +
      (∑ _ : Fin (n+2), a * Matrix.permanent (Fin.cases (twoFront (n+1) 0 e b)
        (fun _ => twoFront (n+1) a b x))) = _
  rw [permanent_one_exception_twoFront,permanent_one_exception_twoFront]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  simp only [pow_succ]
  ring

private theorem twoZeroReducedBoard_eq_twoExceptional (n : ℕ) (a b : ℝ) :
    twoZeroReducedBoard n a b = twoExceptional n (1-n*a) (1-n*b) a b ((1-a-b)/n) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [twoZeroReducedBoard,twoExceptional,twoFront]
    | succ j =>
      cases j using Fin.cases <;>
        simp [twoZeroReducedBoard,twoExceptional,twoFront,← Fin.succ_zero_eq_one,
          -Fin.succ_zero_eq_one']
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [twoZeroReducedBoard,twoExceptional,twoFront,← Fin.succ_zero_eq_one,
          -Fin.succ_zero_eq_one']
      | succ j =>
        cases j using Fin.cases <;>
          simp [twoZeroReducedBoard,twoExceptional,twoFront,← Fin.succ_zero_eq_one,
            -Fin.succ_zero_eq_one']
    | succ i =>
      cases j using Fin.cases with
      | zero => simp [twoZeroReducedBoard,twoExceptional,twoFront,← Fin.succ_zero_eq_one,
          -Fin.succ_zero_eq_one']
      | succ j =>
        cases j using Fin.cases <;>
          simp [twoZeroReducedBoard,twoExceptional,twoFront,← Fin.succ_zero_eq_one,
            -Fin.succ_zero_eq_one']

/-- Exact permanent of the actual reduced board. The parameters are arbitrary
signed reals, and the proof uses no division by an entry or positivity limit. -/
theorem twoZeroReducedBoard_permanent {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    (twoZeroReducedBoard n a b).permanent = twoZeroReducedPermanent n a b := by
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hn
  have he : n=t+2 := by omega
  rw [he,twoZeroReducedBoard_eq_twoExceptional,twoExceptional_permanent]
  simp only [twoZeroReducedPermanent,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat,pow_succ]
  ring

end DittertRybin
