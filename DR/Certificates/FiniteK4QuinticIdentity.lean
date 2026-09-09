import DR.Certificates.FiniteK4QuinticChecks
import DR.Certificates.FiniteK4QuinticLocal
import DR.Certificates.FiniteK4Soundness

/-! All91 literal sparse equations imply the actual signed homogeneous
quintic gap identity. This interface applies in arbitrary physical dimensions;
positivity and the repeated-cell kernel remain separate obligations. -/
namespace DittertRybin.Certificates
open scoped BigOperators

theorem FiniteK4CoefficientEquations.local {alpha : ℝ} {coeff : Fin 407 → ℝ}
    (h : FiniteK4CoefficientEquations alpha coeff) {m n : ℕ}
    (s : Fin 5 → Fin m × Fin n) :
    finiteK4TripleValue coeff s = 60*alpha - 12*(∑ a : Fin 5,
      (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) :=
  finiteK4TripleValue_eq_of_pattern s (finiteK4QuinticPattern_correct _ _) (h _)

theorem FiniteK4CoefficientEquations.probability_identity {alpha : ℝ} {coeff : Fin 407 → ℝ}
    (h : FiniteK4CoefficientEquations alpha coeff) {m n : ℕ} (P : Board m n) :
    alpha*totalMass P^5 - totalMass P*separationProbability P 4 =
      ∑ t : Fin 3 → Fin m × Fin n, unorderedTripleWeight t*(∏ i, P (t i).1 (t i).2)*
        quadraticValue (finiteK4Entry coeff t) (fun e => P e.1 e.2) :=
  finiteK4_probability_identity_of_local alpha coeff h.local P

theorem FiniteK4CoefficientEquations.uniformMaximizer {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {coeff : Fin 407 → ℝ}
    (h : FiniteK4CoefficientEquations (uniformSeparationValue m n 4) coeff)
    (hQ : ∀ t : Fin 3 → Fin m × Fin n, Matrix.PosSemidef (finiteK4Entry coeff t))
    (hk : ∀ e : Fin m × Fin n, ∀ p : Fin m × Fin n → ℝ,
      quadraticValue (finiteK4Entry coeff (fun _ => e)) p = 0 → ∃ c : ℝ, ∀ a, p a = c) :
    UniformMaximizer m n 4 :=
  finiteK4_uniformMaximizer_of_local hm hn coeff h.local hQ hk

end DittertRybin.Certificates
