import DR.Semimatching

/-! Exact homogeneity of finite independent sampling, without sign assumptions. -/

open scoped BigOperators

namespace DittertRybin

theorem sampleMass_mul {α : Type*} {k : ℕ} (p : α → ℝ) (c : ℝ) (s : Fin k → α) :
    sampleMass (fun a => c * p a) s = c ^ k * sampleMass p s := by
  simp [sampleMass, Finset.prod_mul_distrib]

theorem eventMass_mul {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (c : ℝ) (E : Set (Fin k → α)) :
    eventMass (fun a => c * p a) E = c ^ k * eventMass p E := by
  classical
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ E <;> simp [hs, sampleMass_mul]

/-- The k-sample separation functional is a homogeneous polynomial of degree k. -/
theorem separationProbability_smul {m n : ℕ} (P : Board m n) (k : ℕ) (c : ℝ) :
    separationProbability (c • P) k = c ^ k * separationProbability P k := by
  exact eventMass_mul (fun a : Fin m × Fin n => P a.1 a.2) c _

end DittertRybin
