import DR.Semimatching
import DR.Square.Transport
import Mathlib.Logic.Equiv.Prod

/-!
# Continuity, compactness, and the basic symmetries

The actual independent-sampling functional is a finite sum of monomials in
the cell entries. It is therefore continuous on all real matrices. The full
closed probability simplex is compact, and is nonempty when both dimensions
are positive. Consequently an unrestricted global maximizer exists for every
sample order. Zero entries are included throughout.
-/

namespace DittertRybin

open scoped BigOperators

theorem continuous_sampleMass {α : Type*} {k : ℕ} (s : Fin k → α) :
    Continuous (fun p : α → ℝ => sampleMass p s) := by
  unfold sampleMass
  fun_prop

theorem continuous_eventMass {α : Type*} [Fintype α] {k : ℕ}
    (E : Set (Fin k → α)) : Continuous (fun p : α → ℝ => eventMass p E) := by
  classical
  unfold eventMass
  apply continuous_finsetSum
  intro s _
  by_cases hs : s ∈ E
  · simpa [hs] using continuous_sampleMass s
  · simp only [if_neg hs]
    exact continuous_const

/-- Continuity of the exact iid functional, with no probability assumptions. -/
theorem continuous_separationProbability {m n : ℕ} (k : ℕ) :
    Continuous (fun P : Board m n => separationProbability P k) := by
  exact (continuous_eventMass _).comp (by fun_prop)

theorem continuous_dittertFunctional {n : ℕ} :
    Continuous (fun A : Board n n => dittertFunctional A) := by
  unfold dittertFunctional rowSum colSum Matrix.permanent
  fun_prop

/-- Each entry of a probability matrix is bounded by its total mass one. -/
theorem IsProbability.entry_le_one {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (i : Fin m) (j : Fin n) : P i j ≤ 1 := by
  calc
    P i j ≤ rowSum P i :=
      Finset.single_le_sum (fun j _ => hP.1 i j) (Finset.mem_univ j)
    _ ≤ totalMass P :=
      Finset.single_le_sum (fun i _ => rowSum_nonneg hP.1 i) (Finset.mem_univ i)
    _ = 1 := hP.2

theorem isClosed_probabilitySimplex (m n : ℕ) :
    IsClosed {P : Board m n | IsProbability P} := by
  have hnonneg : IsClosed {P : Board m n | ∀ i j, 0 ≤ P i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
  exact hnonneg.inter (isClosed_eq continuous_totalMass continuous_const)

/-- Compactness includes the possibly empty zero-dimensional probability simplices. -/
theorem isCompact_probabilitySimplex (m n : ℕ) :
    IsCompact {P : Board m n | IsProbability P} := by
  let box : Set (Board m n) := {P | ∀ i j, P i j ∈ Set.Icc 0 1}
  have hbox : IsCompact box := by
    exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_probabilitySimplex m n)
  intro P hP i j
  exact ⟨hP.1 i j, hP.entry_le_one i j⟩

theorem probabilitySimplex_nonempty {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Set.Nonempty {P : Board m n | IsProbability P} :=
  ⟨uniformBoard m n, uniformBoard_isProbability hm hn⟩

/-- A global maximizer exists on the entire closed simplex for every sample order. -/
theorem exists_separation_maximizer {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (k : ℕ) :
    ∃ P : Board m n, IsProbability P ∧
      ∀ Q : Board m n, IsProbability Q → separationProbability Q k ≤ separationProbability P k := by
  obtain ⟨P, hP, hmax⟩ := (isCompact_probabilitySimplex m n).exists_isMaxOn
    (probabilitySimplex_nonempty hm hn) (continuous_separationProbability k).continuousOn
  exact ⟨P, hP, fun Q hQ => hmax hQ⟩

/-- Transposition exchanges the two events in their inclusive union. -/
theorem separationProbability_transpose {m n : ℕ} (P : Board m n) (k : ℕ) :
    separationProbability P.transpose k = separationProbability P k := by
  classical
  unfold separationProbability eventMass
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin k))
    (Equiv.prodComm (Fin n) (Fin m)))
  intro s
  refine @if_ctx_congr ℝ _ _ (Classical.propDecidable _) (Classical.propDecidable _)
    _ _ _ _ ?_ ?_ ?_
  · change (RowsDistinct s ∨ ColsDistinct s) ↔ (ColsDistinct s ∨ RowsDistinct s)
    exact or_comm
  · intro _
    rfl
  · intro _
    rfl

/-- Relabeling both matrix axes preserves every semimatching probability. -/
theorem separationProbability_permute {m n : ℕ} (P : Board m n) (k : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    separationProbability (fun i j => P (σ i) (τ j)) k = separationProbability P k := by
  classical
  unfold separationProbability eventMass
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin k))
    (Equiv.prodCongr σ τ))
  intro s
  have hr : Function.Injective (fun t => σ (s t).1) ↔ RowsDistinct s :=
    σ.injective.of_comp_iff (fun t => (s t).1)
  have hc : Function.Injective (fun t => τ (s t).2) ↔ ColsDistinct s :=
    τ.injective.of_comp_iff (fun t => (s t).2)
  simp [RowsDistinct, ColsDistinct, sampleMass, Equiv.arrowCongr_apply, hr, hc]

theorem sampleMass_comp_perm {α : Type*} {k : ℕ} (p : α → ℝ)
    (s : Fin k → α) (σ : Equiv.Perm (Fin k)) : sampleMass p (s ∘ σ) = sampleMass p s :=
  Equiv.prod_comp σ (fun t => p (s t))

theorem rowsDistinct_comp_perm {m n k : ℕ} (s : Fin k → Fin m × Fin n)
    (σ : Equiv.Perm (Fin k)) : RowsDistinct (s ∘ σ) ↔ RowsDistinct s :=
  Function.Injective.of_comp_iff' (fun t => (s t).1) σ.bijective

theorem colsDistinct_comp_perm {m n k : ℕ} (s : Fin k → Fin m × Fin n)
    (σ : Equiv.Perm (Fin k)) : ColsDistinct (s ∘ σ) ↔ ColsDistinct s :=
  Function.Injective.of_comp_iff' (fun t => (s t).2) σ.bijective

end DittertRybin
