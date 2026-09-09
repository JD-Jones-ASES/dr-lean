import DR.Certificates.FiniteK4QuinticRows
import DR.Certificates.FiniteK4QuinticChecks
import DR.Certificates.FiniteK4Soundness
import DR.Rectangular.FourRowFiniteData5Identities
import DR.Rectangular.FourRowFiniteData50Identities
import DR.Rectangular.FourRowContenderInitial
import DR.Rectangular.FourRowFiniteParameter

/-! The actual closed four-row coefficient identities for both finite
parameter families. The polynomial expression equals the sharp uniform
probability at u=a/N. Matrix positivity is assembled separately. -/
namespace DittertRybin
open Certificates
open scoped BigOperators

theorem fourRowFiniteParameter_uniform_value {a n : ℕ} (ha : 0 < a) (hn : 4 ≤ n) :
    1-87/(16*(a : ℝ))*fourRowFiniteParameter a n+
      319/(32*(a : ℝ)^2)*(fourRowFiniteParameter a n)^2-
      87/(16*(a : ℝ)^3)*(fourRowFiniteParameter a n)^3 = uniformSeparationValue 4 n 4 := by
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he := fourRow_failure_uniform hn
  rw [separationProbability_uniform (by decide) (by omega)] at he
  have hid : 1-87/(16*(a : ℝ))*fourRowFiniteParameter a n+
      319/(32*(a : ℝ)^2)*(fourRowFiniteParameter a n)^2-
      87/(16*(a : ℝ)^3)*(fourRowFiniteParameter a n)^3 =
      1-(29/32 : ℝ)*(6/n-11/(n : ℝ)^2+6/(n : ℝ)^3) := by
    unfold fourRowFiniteParameter
    field_simp
    ring
  linarith

theorem fourRowFiniteCoefficientEquations_at_columns {a n : ℕ} (ha : 0 < a) (hn : 4 ≤ n)
    (h : Fin 391 → Fin 5 → ℚ)
    (hv : ∀ e : Fin 84, (fourRowFiniteCoefficientRows e).Valid a h) :
    FiniteK4FourRowCoefficientEquations (uniformSeparationValue 4 n 4)
      (fourRowFiniteUniversalCoefficient h (fourRowFiniteParameter a n)) := by
  have hu : fourRowFiniteParameter a n ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr ha.ne') (Nat.cast_ne_zero.mpr (by omega))
  have he := fourRowFiniteUniversalCoefficient_equations a h hv (fourRowFiniteParameter a n) hu
  rw [fourRowFiniteParameter_uniform_value ha hn] at he
  exact he

theorem Certificates.FiniteK4FourRowCoefficientEquations.local {n : ℕ} {alpha : ℝ}
    {coeff : Fin 407 → ℝ} (h : FiniteK4FourRowCoefficientEquations alpha coeff)
    (s : Fin 5 → Fin 4 × Fin n) :
    finiteK4TripleValue coeff s = 60*alpha - 12*(∑ a : Fin 5,
      (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) :=
  finiteK4TripleValue_eq_of_pattern s (finiteK4QuinticPattern_correct _ _) (h.physical_row s)

theorem Certificates.FiniteK4FourRowCoefficientEquations.probability_identity {n : ℕ}
    {alpha : ℝ} {coeff : Fin 407 → ℝ} (h : FiniteK4FourRowCoefficientEquations alpha coeff)
    (P : Board 4 n) :
    alpha*totalMass P^5-totalMass P*separationProbability P 4 =
      ∑ t : Fin 3 → Fin 4 × Fin n, unorderedTripleWeight t*(∏ i, P (t i).1 (t i).2)*
        quadraticValue (finiteK4Entry coeff t) (fun e => P e.1 e.2) :=
  finiteK4_probability_identity_of_local alpha coeff h.local P

theorem fourRowFinite5_coefficientEquations {n : ℕ} (hn : 4 ≤ n) :
    FiniteK4FourRowCoefficientEquations (uniformSeparationValue 4 n 4)
      (fourRowFiniteUniversalCoefficient fourRowFiniteFamilyNumerator5 (fourRowFiniteParameter 5 n)) :=
  fourRowFiniteCoefficientEquations_at_columns (by decide) hn _ fourRowFinite5_coefficient_identities

theorem fourRowFinite50_coefficientEquations {n : ℕ} (hn : 4 ≤ n) :
    FiniteK4FourRowCoefficientEquations (uniformSeparationValue 4 n 4)
      (fourRowFiniteUniversalCoefficient fourRowFiniteFamilyNumerator50 (fourRowFiniteParameter 50 n)) :=
  fourRowFiniteCoefficientEquations_at_columns (by decide) hn _ fourRowFinite50_coefficient_identities

theorem Certificates.FiniteK4FourRowCoefficientEquations.uniformMaximizer {n : ℕ}
    (hn : 0 < n) {coeff : Fin 407 → ℝ}
    (h : FiniteK4FourRowCoefficientEquations (uniformSeparationValue 4 n 4) coeff)
    (hQ : ∀ t : Fin 3 → Fin 4 × Fin n, Matrix.PosSemidef (finiteK4Entry coeff t))
    (hk : ∀ e : Fin 4 × Fin n, ∀ p : Fin 4 × Fin n → ℝ,
      quadraticValue (finiteK4Entry coeff (fun _ => e)) p = 0 → ∃ c : ℝ, ∀ a, p a = c) :
    UniformMaximizer 4 n 4 :=
  finiteK4_uniformMaximizer_of_local (by decide) hn coeff h.local hQ hk

end DittertRybin
