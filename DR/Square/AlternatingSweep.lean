import DR.Square.AlternatingPath

/-!
# The even-prefix alternating sweep

Minimize over every even proper prefix. The alternating path estimate bounds
this minimum directly; a separate balanced-prefix existence lemma is not
needed. In the matrix application the resulting bound is below the boundary
of every unbalanced cut, and therefore forces the selected prefix to balance.
-/

namespace DittertRybin

open scoped BigOperators

def evenPrefixIndexTwelve (t : Fin 5) : Fin 11 := ⟨2 * t.val + 1, by omega⟩

theorem evenPrefixIndexTwelve_card (t : Fin 5) :
    (sweepPrefix (evenPrefixIndexTwelve t)).card = 2 * t.val + 2 := by
  fin_cases t <;> decide +kernel

/-- The finite alternating sweep, including tied scores and zero energy. -/
theorem exists_even_sweep_prefix_twelve (f : Fin 12 → ℝ) (hf : Monotone f)
    (c : Fin 12 → Fin 12 → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hcsym : ∀ i j, c i j = c j i)
    (q h : ℝ) (hq : 0 < q) (hh : 0 ≤ h) (hhq : h < q * (2 / 15))
    (hodd : ∀ j : Fin 11, j.val % 2 = 0 → q ≤ sweepBoundary c (sweepPrefix j))
    (hvar : 0 < ∑ i, (f i - (∑ j, f j) / 12) ^ 2)
    (henergy : sweepEnergy c f ≤ h * ∑ i, (f i - (∑ j, f j) / 12) ^ 2) :
    ∃ t : Fin 5, sweepBoundary c (sweepPrefix (evenPrefixIndexTwelve t)) ≤
      alternatingBoundary q h (2 / 15) := by
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 5))
    (fun t => sweepBoundary c (sweepPrefix (evenPrefixIndexTwelve t))) ⟨0, Finset.mem_univ _⟩
  refine ⟨t, ?_⟩
  by_contra hb
  push Not at hb
  let b := sweepBoundary c (sweepPrefix (evenPrefixIndexTwelve t))
  have hweights (j : Fin 11) : alternatingWeights 11 q b j ≤ sweepBoundary c (sweepPrefix j) := by
    unfold alternatingWeights
    split_ifs with hj
    · exact hodd j hj
    · let u : Fin 5 := ⟨j.val / 2, by omega⟩
      have heq : evenPrefixIndexTwelve u = j := by
        apply Fin.ext
        dsimp [evenPrefixIndexTwelve, u]
        omega
      simpa only [heq] using ht u (Finset.mem_univ u)
  have hbound : (∑ j, alternatingWeights 11 q b j * sweepGap f j ^ 2) ≤ sweepEnergy c f :=
    (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hweights j) (sq_nonneg _)).trans
      (sweep_prefix_gap_energy_le c hc0 hcsym f hf)
  let g : Fin 12 → ℝ := fun i => f i - (∑ j, f j) / 12
  have hgmean : ∑ i, g i = 0 := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hgap (j : Fin 11) : sweepGap g j = sweepGap f j := by unfold sweepGap g; ring
  have hstrict := alternating_twelve_strict q b h hq hh hhq hb g hgmean hvar
  simp_rw [hgap] at hstrict
  exact (not_lt_of_ge (hbound.trans henergy)) hstrict

end DittertRybin
