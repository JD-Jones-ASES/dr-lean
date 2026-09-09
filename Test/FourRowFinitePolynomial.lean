import DR.Rectangular.FourRowFinitePolynomial
import DR.ProbabilityScaling

open DittertRybin
open scoped BigOperators

example {n : ℕ} (P : Board 4 n) :
    fourRowFinitePolynomialEval P (fourRowFiniteQuarticPolynomial n) = separationProbability P 4 :=
  fourRowFiniteQuarticPolynomial_eval P

example {n : ℕ} (hn : 4 ≤ n) (P : Board 4 n) (hP : IsProbability P) :
    fourRowFinitePolynomialEval P (fourRowFiniteQuinticGap n) =
      separationProbability (uniformBoard 4 n) 4 - separationProbability P 4 :=
  fourRowFiniteQuinticGap_probability hn P hP

/-- Negative scaling checks both the fifth degree and the extra total-mass factor. -/
example : fourRowFinitePolynomialEval ((-2:ℝ) • uniformBoard 4 5)
    (fourRowFiniteQuinticGap 5) = 0 := by
  rw [fourRowFiniteQuinticGap_eval, separationProbability_smul]
  have hm : totalMass ((-2:ℝ) • uniformBoard 4 5) = -2 := by
    norm_num [totalMass, rowSum, uniformBoard, Fin.sum_univ_succ]
  rw [hm, fourRowFiniteUniformRational_eq (by decide)]
  ring

example : RowsDistinct (fun i : Fin 4 => (i, (0 : Fin 1))) := by
  exact Function.injective_id

example : ¬ ColsDistinct (fun i : Fin 4 => (i, (0 : Fin 1))) := by
  intro h
  have he := h (a₁ := (0 : Fin 4)) (a₂ := (1 : Fin 4)) rfl
  exact (by decide : (0 : Fin 4) ≠ 1) he

example {n : ℕ} (P : Board 4 n) (a : FourRowFiniteCell n) :
    fourRowFinitePolynomialEval P (fourRowFiniteSampleMonomial (fun _ : Fin 5 => a)) =
      P a.1 a.2 ^ 5 := by
  simp [fourRowFinitePolynomialEval, fourRowFiniteSampleMonomial]

example : fourRowFiniteUniformRational 5 = 1071/4000 := by
  norm_num [fourRowFiniteUniformRational]

#print axioms fourRowFiniteQuarticPolynomial_eval
#print axioms fourRowFiniteQuinticGap_probability
#print axioms fourRowFiniteTotal_mul_quartic
#print axioms fourRowFiniteQuinticGap_ordered
#print axioms fourRowFiniteQuinticGap_isHomogeneous
