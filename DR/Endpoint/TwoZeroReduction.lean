import DR.Endpoint.TwoZeroReducedBoard

/-! An actual least-norm face minimum supplies a reduced representative below
every doubly stochastic matrix with two independent zero entries. -/

namespace DittertRybin
open scoped BigOperators

theorem exists_permutation_on_pair {ι : Type*} [Finite ι]
    (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm ι, σ a = c ∧ σ b = d := by
  classical
  let f : Fin 2 → ι := ![a,b]
  let g : Fin 2 → ι := ![c,d]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨σ,by simpa [f,g] using hσ 0,by simpa [f,g] using hσ 1⟩

theorem twoZeroReducedBoard_representative {n : ℕ} (hn : 0 < n)
    {D : Board (n+2) (n+2)} (hD : D ∈ doublyStochastic ℝ (Fin (n+2)))
    (i₁ i₂ j₁ j₂ : Fin (n+2)) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁ = 0) (hz₂ : D i₂ j₂ = 0) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1/(n : ℝ) ∧ 0 ≤ b ∧ b ≤ 1/(n : ℝ) ∧
      (twoZeroReducedBoard n a b).permanent ≤ D.permanent := by
  obtain ⟨e,he0,he1⟩ := exists_permutation_on_pair
    (0 : Fin (n+2)) 1 i₁ i₂ Fin.zero_ne_one' hi
  obtain ⟨f,hf0,hf1⟩ := exists_permutation_on_pair
    (0 : Fin (n+2)) 1 j₂ j₁ Fin.zero_ne_one' hj.symm
  let B : Board (n+2) (n+2) := D.submatrix e f
  have hB : B ∈ doublyStochastic ℝ (Fin (n+2)) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => nonneg_of_mem_doublyStochastic hD,?_,?_⟩
    · intro i
      change (∑ j, D (e i) (f j)) = 1
      exact (Equiv.sum_comp f (fun j => D (e i) j)).trans
        (sum_row_of_mem_doublyStochastic hD (e i))
    · intro j
      change (∑ i, D (e i) (f j)) = 1
      exact (Equiv.sum_comp e (fun i => D i (f j))).trans
        (sum_col_of_mem_doublyStochastic hD (f j))
  have hface : ∀ i j, ¬twoZeroAllowed n i j → B i j = 0 := by
    intro i j h
    unfold twoZeroAllowed at h
    have hz : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by tauto
    rcases hz with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa [B,he0,hf1] using hz₁
    · simpa [B,he1,hf0] using hz₂
  have hper : B.permanent = D.permanent := by
    change ((D.submatrix id f).submatrix e id).permanent = _
    rw [Matrix.permanent_permute_cols,Matrix.permanent_permute_rows]
  obtain ⟨A,hA⟩ := exists_twoZero_leastNorm_minimum n
  obtain ⟨a,b,ha,haN,hb,hbN,hform⟩ := hA.twoZero_reduced_form hn
  refine ⟨a,b,ha,haN,hb,hbN,?_⟩
  rw [← hform,← hper]
  exact hA.1.2.2 B hB hface

end DittertRybin
