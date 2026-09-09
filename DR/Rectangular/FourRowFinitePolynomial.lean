import DR.Rectangular.FourRowContenderInitial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The actual quintic gap for the finite four-row certificates

Variables are literal cells of the 4-by-N board. The quartic is the original
ordered iid inclusive-OR event, and the quintic appends one unrestricted cell.
The resulting five-sample identity is the source of the finite coefficient
equations. No catalog completeness or matrix-positivity claim is assumed here.
-/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev FourRowFiniteCell (n : ℕ) := Fin 4 × Fin n

def fourRowFiniteTotalPolynomial (n : ℕ) : MvPolynomial (FourRowFiniteCell n) ℚ :=
  ∑ a, X a

def fourRowFiniteSampleMonomial {n k : ℕ} (s : Fin k → FourRowFiniteCell n) :
    MvPolynomial (FourRowFiniteCell n) ℚ := ∏ t, X (s t)

def fourRowFiniteQuarticPolynomial (n : ℕ) : MvPolynomial (FourRowFiniteCell n) ℚ := by
  classical
  exact ∑ s : Fin 4 → FourRowFiniteCell n,
    if RowsDistinct s ∨ ColsDistinct s then fourRowFiniteSampleMonomial s else 0

def fourRowFiniteUniformRational (n : ℕ) : ℚ :=
  1 - (29/32) * (6/n - 11/(n:ℚ)^2 + 6/(n:ℚ)^3)

def fourRowFiniteQuinticGap (n : ℕ) : MvPolynomial (FourRowFiniteCell n) ℚ :=
  C (fourRowFiniteUniformRational n) * fourRowFiniteTotalPolynomial n ^ 5 -
    fourRowFiniteTotalPolynomial n * fourRowFiniteQuarticPolynomial n

def fourRowFinitePolynomialEval {n : ℕ} (P : Board 4 n)
    (p : MvPolynomial (FourRowFiniteCell n) ℚ) : ℝ :=
  eval₂ (Rat.castHom ℝ) (fun a => P a.1 a.2) p

theorem fourRowFiniteTotalPolynomial_eval {n : ℕ} (P : Board 4 n) :
    fourRowFinitePolynomialEval P (fourRowFiniteTotalPolynomial n) = totalMass P := by
  simp only [fourRowFinitePolynomialEval, fourRowFiniteTotalPolynomial,
    eval₂_sum, eval₂_X, sum_cell_weights]

/-- Evaluation is the original with-replacement, ordered, inclusive-OR probability polynomial. -/
theorem fourRowFiniteQuarticPolynomial_eval {n : ℕ} (P : Board 4 n) :
    fourRowFinitePolynomialEval P (fourRowFiniteQuarticPolynomial n) =
      separationProbability P 4 := by
  classical
  simp only [fourRowFinitePolynomialEval, fourRowFiniteQuarticPolynomial,
    eval₂_sum, separationProbability, eventMass, Set.mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : RowsDistinct s ∨ ColsDistinct s <;>
    simp [hs, fourRowFiniteSampleMonomial, sampleMass]

theorem fourRowFiniteUniformRational_eq {n : ℕ} (hn : 4 ≤ n) :
    (fourRowFiniteUniformRational n : ℝ) = separationProbability (uniformBoard 4 n) 4 := by
  have h := fourRow_failure_uniform hn
  push_cast [fourRowFiniteUniformRational]
  linarith

theorem fourRowFiniteQuinticGap_eval {n : ℕ} (P : Board 4 n) :
    fourRowFinitePolynomialEval P (fourRowFiniteQuinticGap n) =
      (fourRowFiniteUniformRational n : ℝ) * totalMass P ^ 5 -
        totalMass P * separationProbability P 4 := by
  simp only [fourRowFiniteQuinticGap, fourRowFinitePolynomialEval,
    eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow]
  change (fourRowFiniteUniformRational n : ℝ) *
      fourRowFinitePolynomialEval P (fourRowFiniteTotalPolynomial n) ^ 5 -
      fourRowFinitePolynomialEval P (fourRowFiniteTotalPolynomial n) *
      fourRowFinitePolynomialEval P (fourRowFiniteQuarticPolynomial n) = _
  rw [fourRowFiniteTotalPolynomial_eval, fourRowFiniteQuarticPolynomial_eval]

theorem fourRowFiniteQuinticGap_probability {n : ℕ} (hn : 4 ≤ n)
    (P : Board 4 n) (hP : IsProbability P) :
    fourRowFinitePolynomialEval P (fourRowFiniteQuinticGap n) =
      separationProbability (uniformBoard 4 n) 4 - separationProbability P 4 := by
  rw [fourRowFiniteQuinticGap_eval, hP.2, fourRowFiniteUniformRational_eq hn]
  ring

/-- The full ordered sample expansion of the total-mass power. -/
theorem fourRowFiniteTotalPolynomial_power (n k : ℕ) :
    fourRowFiniteTotalPolynomial n ^ k =
      ∑ s : Fin k → FourRowFiniteCell n, fourRowFiniteSampleMonomial s := by
  have h := Fintype.prod_sum (fun _ : Fin k => fun a : FourRowFiniteCell n =>
    (X a : MvPolynomial (FourRowFiniteCell n) ℚ))
  simpa only [fourRowFiniteTotalPolynomial, fourRowFiniteSampleMonomial,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- The fifth cell is the total-mass multiplier; success is tested on the first four. -/
theorem fourRowFiniteTotal_mul_quartic (n : ℕ) :
    fourRowFiniteTotalPolynomial n * fourRowFiniteQuarticPolynomial n =
      ∑ s : Fin 5 → FourRowFiniteCell n,
        if RowsDistinct (Fin.init s) ∨ ColsDistinct (Fin.init s)
          then fourRowFiniteSampleMonomial s else 0 := by
  classical
  calc
    _ = ∑ a : FourRowFiniteCell n, ∑ s : Fin 4 → FourRowFiniteCell n,
        if RowsDistinct s ∨ ColsDistinct s then X a * fourRowFiniteSampleMonomial s else 0 := by
      rw [fourRowFiniteTotalPolynomial, fourRowFiniteQuarticPolynomial, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    _ = ∑ q : FourRowFiniteCell n × (Fin 4 → FourRowFiniteCell n),
        if RowsDistinct q.2 ∨ ColsDistinct q.2 then
          X q.1 * fourRowFiniteSampleMonomial q.2 else 0 := by
      exact (Fintype.sum_prod_type (fun q : FourRowFiniteCell n × (Fin 4 → FourRowFiniteCell n) =>
        if RowsDistinct q.2 ∨ ColsDistinct q.2 then
          X q.1 * fourRowFiniteSampleMonomial q.2 else 0)).symm
    _ = _ := by
      apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin 5 => FourRowFiniteCell n))
      intro q
      let s : Fin 5 → FourRowFiniteCell n := Fin.snoc q.2 q.1
      have hs : Fin.init s = q.2 := Fin.init_snoc _ _
      change (if RowsDistinct q.2 ∨ ColsDistinct q.2 then
          X q.1 * fourRowFiniteSampleMonomial q.2 else 0) =
        if RowsDistinct (Fin.init s) ∨ ColsDistinct (Fin.init s) then
          fourRowFiniteSampleMonomial s else 0
      rw [hs]
      have hprod : fourRowFiniteSampleMonomial s =
          fourRowFiniteSampleMonomial q.2 * X q.1 := by
        dsimp [fourRowFiniteSampleMonomial, s]
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
      split_ifs <;> simp [hprod, mul_comm]

/-- Exact signed five-cell expansion underlying all quintic coefficient equations. -/
theorem fourRowFiniteQuinticGap_ordered (n : ℕ) :
    fourRowFiniteQuinticGap n = ∑ s : Fin 5 → FourRowFiniteCell n,
      C (fourRowFiniteUniformRational n -
        if RowsDistinct (Fin.init s) ∨ ColsDistinct (Fin.init s) then 1 else 0) *
        fourRowFiniteSampleMonomial s := by
  classical
  rw [fourRowFiniteQuinticGap, fourRowFiniteTotalPolynomial_power,
    fourRowFiniteTotal_mul_quartic, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp [map_sub, sub_mul]

theorem fourRowFiniteSampleMonomial_isHomogeneous {n k : ℕ}
    (s : Fin k → FourRowFiniteCell n) : (fourRowFiniteSampleMonomial s).IsHomogeneous k := by
  simpa only [fourRowFiniteSampleMonomial, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] using
    IsHomogeneous.prod Finset.univ _ (fun _ => 1) (fun t _ => isHomogeneous_X ℚ (s t))

theorem fourRowFiniteQuinticGap_isHomogeneous (n : ℕ) :
    (fourRowFiniteQuinticGap n).IsHomogeneous 5 := by
  classical
  rw [fourRowFiniteQuinticGap_ordered]
  exact IsHomogeneous.sum Finset.univ _ 5 fun s _ =>
    (fourRowFiniteSampleMonomial_isHomogeneous s).C_mul _

end
end DittertRybin
