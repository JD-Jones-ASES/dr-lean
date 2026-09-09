import DR.Rectangular.ThreeRowSingletonShape
import DR.Rectangular.ThreeRowTwoStar

/-! Unconditional exclusion of all singleton columns at three-row global maxima. -/

namespace DittertRybin

/-- Every singleton candidate reduces to an actual two-star global maximum, whose value is too small. -/
theorem IsSeparationGlobalMax.threeRow_no_singleton {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a : Fin n) (ha : ThreeRowSingleton P i a) : False := by
  obtain ⟨Q, b, u, hQ, hQmax, _hu, hshape⟩ :=
    hmax.threeRow_singleton_global_representative hP hn i a ha
  have heq : Q = threeRowTwoStar i b u := by
    ext r c
    exact hshape r c
  have hmass : totalMass (threeRowTwoStar i b u) = 1 := heq ▸ hQ.2
  have hstrict := separationProbability_threeRowTwoStar_lt_uniform hn i b u hmass
  have hle := hQmax _ (uniformBoard_isProbability (by norm_num : 0 < 3) (by omega : 0 < n))
  rw [heq, separationProbability_uniform (by norm_num : 0 < 3) (by omega : 0 < n)] at hle
  exact (not_lt_of_ge hle) hstrict

/-- Every column of a three-row global maximum has two or three positive entries. -/
theorem IsSeparationGlobalMax.threeRow_columns_full_or_doublet {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n) (c : Fin n) :
    ThreeRowFullColumn P c ∨ ∃ i, ThreeRowDoublet P i c := by
  rcases threeRow_column_support_cases hP.1 c (hmax.column_mass_pos hP hn c) with hf | ⟨i, hs⟩ | hd
  · exact Or.inl hf
  · exact False.elim (hmax.threeRow_no_singleton hP hn i c hs)
  · exact Or.inr hd

end DittertRybin
