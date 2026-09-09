import DR.Rectangular.FourRowMinorantFinal
import DR.Rectangular.FourRowLeadingConcentration

/-! The unconditional corrected minorant applied to actual columns. Column
normalization is used only for positive column mass; zero columns are handled
directly. Weighted Cauchy then supplies the precise squared gauge input. -/

namespace DittertRybin
open scoped BigOperators
open Certificates

/-- Weighted Cauchy for the literal square-root gauge on a closed probability vector. -/
theorem fourRowGauge_weighted_cauchy (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hsr : ∑ i, r i = 1)
    (hv : ∀ i, 0 ≤ v i) (hsv : ∑ i, v i = 1) :
    (∑ i, fourRowGaugeWeight r i * v i) ^ 2 ≤
      ∑ i, v i * (1 - fourRowGaugeCollision r i) := by
  have hg (i : Fin 4) : 0 ≤ 1 - fourRowGaugeCollision r i := by
    have h := (fourRowGaugeCollision_bounds r hr hsr i).2
    linarith
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => fourRowGaugeWeight r i * v i)
    (f := v) (g := fun i => v i * (1 - fourRowGaugeCollision r i))
    (fun i _ => hv i) (fun i _ => mul_nonneg (hv i) (hg i)) (fun i _ => by
      dsimp [fourRowGaugeWeight]
      rw [mul_pow, Real.sq_sqrt (hg i)]
      exact le_of_eq (by ring))
  simpa only [hsv, one_mul] using h

/-- The final closed-simplex minorant now proves the actual column gauge bound. -/
theorem fourRowGaugeColumn_minorant {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (j : Fin n) : fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j) := by
  let c := colSum P j
  have hc0 : 0 ≤ c := colSum_nonneg hP.1 j
  by_cases hc : c = 0
  · have hz (i : Fin 4) : P i j = 0 := by
      have hle : P i j ≤ c := Finset.single_le_sum (fun k _ => hP.1 k j) (Finset.mem_univ i)
      exact le_antisymm (hle.trans_eq hc) (hP.1 i j)
    simp [fourRowGaugeColumn, quadraticValue, hz]
  · have hcp : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    let v : Fin 4 → ℝ := fun i => P i j / c
    have hv : ∀ i, 0 ≤ v i := fun i => div_nonneg (hP.1 i j) hc0
    have hsv : ∑ i, v i = 1 := by
      rw [show (∑ i, v i) = c / c by simp only [v, ← Finset.sum_div]; rfl]
      exact div_self hc
    have hminor := fourRow_corrected_minorant (rowSum P) v (rowSum_nonneg hP.1) hP.2 hv hsv
    have hcs := fourRowGauge_weighted_cauchy (rowSum P) v (rowSum_nonneg hP.1) hP.2 hv hsv
    have hscale := mul_le_mul_of_nonneg_left (hcs.trans hminor) (sq_nonneg c)
    have ha : c * (∑ i, fourRowGaugeWeight (rowSum P) i * v i) = fourRowGaugeColumn P j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [v]
      field_simp
    have hQ : c ^ 2 * quadraticValue (fourRowLeadingKernel (rowSum P)) v =
        quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j) := by
      simp only [quadraticValue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      dsimp [v]
      field_simp
    rw [hQ, ← mul_pow, ha] at hscale
    exact hscale

theorem fourRow_contender_concentration {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4) :
    fourRowMarginalVariance (rowSum P) * n < 10 ∧
      (∀ j, colSum P j < 7 / (2 * (n : ℝ))) ∧
      fourRowColumnSquareMass P < 7 / (5 * (n : ℝ)) :=
  fourRow_contender_concentration_of_minorant hn P hP hcont (fourRowGaugeColumn_minorant P hP)

theorem fourRow_contender_deletion {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (a b : Fin n) (hab : a ≠ b) :
    493 / 500 ≤ totalMass (eraseColumns P {a,b}) ∧
      fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500 ∧
      fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
        totalMass (eraseColumns P {a,b})) ≤ 1 / 40 :=
  fourRow_contender_deletion_of_minorant hn P hP hcont (fourRowGaugeColumn_minorant P hP) a b hab

end DittertRybin
