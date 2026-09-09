import DR.Definitions
import DR.Probability

/-!
# Independent-cell semimatching probability

Rows or columns must be distinct, with inclusive OR. Samples are ordered
and drawn with replacement. No balance or positive-entry restriction is
hidden in the functional or its probability-matrix domain.
-/

namespace DittertRybin

open scoped BigOperators

/-- Every sampled cell has a different row. -/
def RowsDistinct {m n k : ℕ} (s : Fin k → Fin m × Fin n) : Prop :=
  Function.Injective (fun t => (s t).1)

/-- Every sampled cell has a different column. -/
def ColsDistinct {m n k : ℕ} (s : Fin k → Fin m × Fin n) : Prop :=
  Function.Injective (fun t => (s t).2)

/-- Probability of distinct rows OR distinct columns in k independent draws. -/
noncomputable def separationProbability {m n : ℕ} (P : Board m n) (k : ℕ) : ℝ :=
  eventMass (fun a : Fin m × Fin n => P a.1 a.2)
    {s : Fin k → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s}

/-- Distinct-label probability for uniform draws from d labels. -/
noncomputable def distinctUniformProbability (d k : ℕ) : ℝ :=
  (d.descFactorial k : ℝ) / (d : ℝ) ^ k

/-- The proposed sharp value a+b-ab, where a=(m)_k/m^k and b=(n)_k/n^k. -/
noncomputable def uniformSeparationValue (m n k : ℕ) : ℝ :=
  let a := distinctUniformProbability m k
  let b := distinctUniformProbability n k
  a + b - a * b

/-- The sharp P2 inequality and its exact equality case on the full simplex. -/
def UniformMaximizer (m n k : ℕ) : Prop :=
  ∀ P : Board m n, IsProbability P →
    separationProbability P k ≤ uniformSeparationValue m n k ∧
    (separationProbability P k = uniformSeparationValue m n k ↔ P = uniformBoard m n)

theorem sum_cell_weights {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, P a.1 a.2) = totalMass P := by
  simp [Fintype.sum_prod_type, totalMass, rowSum]

theorem separationProbability_nonneg {m n k : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ separationProbability P k := by
  exact eventMass_nonneg (fun a : Fin m × Fin n => P a.1 a.2)
    (fun a => hP a.1 a.2) _

theorem separationProbability_le_one {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) : separationProbability P k ≤ 1 := by
  exact eventMass_le_one (fun a : Fin m × Fin n => P a.1 a.2)
    (fun a => hP.1 a.1 a.2) ((sum_cell_weights P).trans hP.2) _

/-- With one draw, every probability matrix succeeds; this is not a uniqueness case. -/
theorem separationProbability_one {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) : separationProbability P 1 = 1 := by
  have hevent : {s : Fin 1 → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s} =
      Set.univ := by
    ext s
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact Or.inl (fun _ _ _ => Subsingleton.elim _ _)
  unfold separationProbability
  rw [hevent]
  exact eventMass_univ_eq_one _ ((sum_cell_weights P).trans hP.2)

end DittertRybin
