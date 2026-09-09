import DR.Certificates.QuarticSampling
import DR.Semimatching

/-! Signed iid symmetrization and the actual quintic gap in every rectangle.
No normalization or positivity premise enters these algebraic identities. -/

namespace DittertRybin.Certificates
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_sampleMass_symmetrize {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (f : (Fin k → α) → ℝ) :
    (∑ s, sampleMass p s * ∑ σ : Equiv.Perm (Fin k), f (s ∘ σ)) =
      (Nat.factorial k : ℝ) * ∑ s, sampleMass p s * f s := by
  classical
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [sum_sampleMass_permutation, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- Equality of complete position-permutation sums implies equality of the
actual signed iid weighted sums, including repeated outcomes and k=0. -/
theorem sum_sampleMass_eq_of_permutation_sums {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (f g : (Fin k → α) → ℝ)
    (h : ∀ s, (∑ σ : Equiv.Perm (Fin k), f (s ∘ σ)) =
      ∑ σ : Equiv.Perm (Fin k), g (s ∘ σ)) :
    (∑ s, sampleMass p s * f s) = ∑ s, sampleMass p s * g s := by
  have he : (Nat.factorial k : ℝ) * (∑ s, sampleMass p s * f s) =
      (Nat.factorial k : ℝ) * (∑ s, sampleMass p s * g s) := by
    rw [← sum_sampleMass_symmetrize, ← sum_sampleMass_symmetrize]
    simp only [h]
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) he

noncomputable def quinticGapObservable {m n : ℕ} (alpha : ℝ)
    (s : Fin 5 → Fin m × Fin n) : ℝ :=
  alpha - if RowsDistinct (Fin.init s) ∨ ColsDistinct (Fin.init s) then 1 else 0

/-- The fifth unrestricted cell contributes S, not one: the left side is
exactly alpha*S^5-S*F4 on signed boards, including S=0 and empty dimensions. -/
theorem sum_quinticGapObservable {m n : ℕ} (P : Board m n) (alpha : ℝ) :
    (∑ s : Fin 5 → Fin m × Fin n,
      sampleMass (fun a => P a.1 a.2) s * quinticGapObservable alpha s) =
      alpha * totalMass P ^ 5 - totalMass P * separationProbability P 4 := by
  classical
  have hd := sum_sampleMass_delete (fun a : Fin m × Fin n => P a.1 a.2) (Fin.last 4)
    (fun t : Fin 4 → Fin m × Fin n => if RowsDistinct t ∨ ColsDistinct t then (1 : ℝ) else 0)
  have hi (s : Fin 5 → Fin m × Fin n) : s ∘ (Fin.last 4).succAbove = Fin.init s := by
    funext i
    fin_cases i <;> rfl
  simp only [hi, sum_cell_weights, mul_ite, mul_one, mul_zero] at hd
  have he : (∑ s : Fin 5 → Fin m × Fin n,
      sampleMass (fun a => P a.1 a.2) s *
        (if RowsDistinct (Fin.init s) ∨ ColsDistinct (Fin.init s) then (1 : ℝ) else 0)) =
      totalMass P * separationProbability P 4 := by
    convert! hd using 1 <;> simp only [separationProbability, eventMass,
      Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : RowsDistinct t ∨ ColsDistinct t <;> simp only [ht, if_true, if_false]
  simp only [quinticGapObservable, mul_sub, Finset.sum_sub_distrib]
  rw [he, ← Finset.sum_mul, sum_sampleMass, sum_cell_weights]
  ring

end DittertRybin.Certificates
