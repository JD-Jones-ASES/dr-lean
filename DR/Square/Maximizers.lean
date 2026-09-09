import DR.Compactness
import DR.Square.Contenders

/-! Compactness and exact global-maximizer closure on the full mass-n simplex. -/

namespace DittertRybin

open scoped BigOperators

theorem isCompact_dittertSimplex (n : ℕ) :
    IsCompact {A : Board n n | (∀ i j, 0 ≤ A i j) ∧ totalMass A = n} := by
  have hclosed : IsClosed {A : Board n n | (∀ i j, 0 ≤ A i j) ∧ totalMass A = n} := by
    have hnonneg : IsClosed {A : Board n n | ∀ i j, 0 ≤ A i j} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
    exact hnonneg.inter (isClosed_eq continuous_totalMass continuous_const)
  let box : Set (Board n n) := {A | ∀ i j, A i j ∈ Set.Icc 0 (n : ℝ)}
  have hbox : IsCompact box :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset hclosed
  intro A hA i j
  refine ⟨hA.1 i j, ?_⟩
  calc
    A i j ≤ rowSum A i :=
      Finset.single_le_sum (fun j _ => hA.1 i j) (Finset.mem_univ j)
    _ ≤ totalMass A :=
      Finset.single_le_sum (fun i _ => rowSum_nonneg hA.1 i) (Finset.mem_univ i)
    _ = n := hA.2

theorem exists_dittert_globalMax {n : ℕ} (hn : 0 < n) :
    ∃ A : Board n n, (∀ i j, 0 ≤ A i j) ∧ totalMass A = n ∧
      ∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
        dittertFunctional B ≤ dittertFunctional A := by
  have hne : Set.Nonempty {A : Board n n | (∀ i j, 0 ≤ A i j) ∧ totalMass A = n} :=
    ⟨uniformDittertMatrix n, (by intro i j; unfold uniformDittertMatrix; positivity),
      uniformDittertMatrix_totalMass hn⟩
  obtain ⟨A, hA, hmax⟩ := (isCompact_dittertSimplex n).exists_isMaxOn hne
    continuous_dittertFunctional.continuousOn
  exact ⟨A, hA.1, hA.2, fun B hB hm => hmax ⟨hB, hm⟩⟩

/-- Classifying all actual maximizers yields both the full inequality and unique equality. -/
theorem dittertMaximizer_of_globalMax_uniform {n : ℕ} (hn : 0 < n)
    (hrigid : ∀ A : Board n n, (∀ i j, 0 ≤ A i j) → totalMass A = n →
      (∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
        dittertFunctional B ≤ dittertFunctional A) → A = uniformDittertMatrix n) :
    DittertMaximizer n := by
  obtain ⟨M, hM, hm, hmax⟩ := exists_dittert_globalMax hn
  have hMu := hrigid M hM hm hmax
  have hbound (A : Board n n) (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = n) :
      dittertFunctional A ≤ 2 - dittertConstant n := by
    simpa only [hMu, dittertFunctional_uniform hn] using hmax A hA hmass
  intro A hA hmass
  refine ⟨hbound A hA hmass, ?_⟩
  constructor
  · intro heq
    apply hrigid A hA hmass
    intro B hB hmB
    rw [heq]
    exact hbound B hB hmB
  · intro hu
    rw [hu, dittertFunctional_uniform hn]

end DittertRybin
