import DR.Rectangular.FourByFiveThreeQuadratic
import DR.Certificates.FourByFiveThreeEquations
import DR.Certificates.FiniteK3QuarticProbability
import DR.Maximizers

/-! The independent 4x5 certificate: exact signed quartic identity, global
Frobenius stability and the unique uniform maximum on the full closed simplex. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

/-- All 33 literal rational equations imply the actual homogeneous sampling identity. -/
theorem fourByFiveThree_homogeneous_identity (P : Board 4 5) :
    (27/40:ℝ)*totalMass P^4-totalMass P*separationProbability P 3=
      ∑ e : Fin 4 × Fin 5,∑ f : Fin 4 × Fin 5,
        unorderedPairWeight e f*P e.1 e.2*P f.1 f.2*
          quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
            (fun a => P a.1 a.2) :=
  finiteK3_quartic_probability_identity fourByFiveThree_equations_real P

/-- Quantitative stability on the full closed probability simplex. -/
theorem fourByFiveThree_stability {P : Board 4 5} (hP : IsProbability P) :
    (1/5:ℝ)*fourByFiveThreeEnergy P≤27/40-separationProbability P 3 := by
  have hid := fourByFiveThree_homogeneous_identity P
  rw [hP.2,one_pow,mul_one,one_mul] at hid
  rw [hid]
  exact fourByFiveThree_weighted_quadratic_lower hP

theorem uniformMaximizer_four_by_five_three : UniformMaximizer 4 5 3 := by
  have hU : uniformSeparationValue 4 5 3=(27/40:ℝ) := by
    norm_num [uniformSeparationValue,distinctUniformProbability]
  intro P hP
  have hstab := fourByFiveThree_stability hP
  have hE := fourByFiveThreeEnergy_nonneg P
  rw [hU]
  refine ⟨by linarith only [hstab,hE],?_⟩
  constructor
  · intro heq
    apply (fourByFiveThreeEnergy_eq_zero_iff P).mp
    linarith only [hstab,hE,heq]
  · intro heq
    rw [heq,fourByFiveThree_uniform_value]

/-- Transposition retains every boundary support and the exact equality case. -/
theorem uniformMaximizer_five_by_four_three : UniformMaximizer 5 4 3 := by
  have hU : uniformSeparationValue 5 4 3=uniformSeparationValue 4 5 3 := by
    norm_num [uniformSeparationValue,distinctUniformProbability]
  intro P hP
  have h := uniformMaximizer_four_by_five_three P.transpose hP.transpose
  rw [separationProbability_transpose] at h
  rw [hU]
  refine ⟨h.1,?_⟩
  rw [h.2]
  constructor
  · intro heq
    have ht := congrArg Matrix.transpose heq
    have huT : (uniformBoard 4 5).transpose=uniformBoard 5 4 := by
      ext i j
      norm_num [uniformBoard]
    simpa only [Matrix.transpose_transpose,huT] using ht
  · intro heq
    rw [heq]
    ext i j
    norm_num [uniformBoard]

end DittertRybin
