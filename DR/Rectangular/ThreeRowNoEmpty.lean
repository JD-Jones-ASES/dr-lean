import DR.Rectangular.ThreeRowNoEmptyKernel
import DR.Rectangular.ThreeRowNormalForm

/-!
# No empty axis at a three-sample global maximizer

An empty column and a positive donor give a nondecreasing split. If any other
column carries mass, its positive residual diagonal makes the gain strict.
Otherwise a first flat split produces two positive columns, and the third
available column gives a strict second split. Transposition handles rows.
-/

namespace DittertRybin
open scoped BigOperators

theorem nonnegative_entry_le_totalMass {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (i : Fin m) (j : Fin n) : P i j ≤ totalMass P := by
  calc
    P i j ≤ rowSum P i := Finset.single_le_sum (fun j _ => hP i j) (Finset.mem_univ j)
    _ ≤ totalMass P := Finset.single_le_sum (fun i _ => rowSum_nonneg hP i) (Finset.mem_univ i)

theorem IsProbability.exists_positive_cell {m n : ℕ} {P : Board m n} (hP : IsProbability P) :
    ∃ i j, 0 < P i j := by
  by_contra h
  push Not at h
  have hz : ∀ i j, P i j = 0 := fun i j => le_antisymm (h i j) (hP.1 i j)
  have hm := hP.2
  simp [totalMass, rowSum, hz] at hm

/-- A zero column contradicts actual global maximality, including the one-donor case. -/
theorem IsSeparationGlobalMax.no_zero_column {m n : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (a : Fin n) (ha : ∀ i, P i a = 0) : False := by
  obtain ⟨i, b, hib⟩ := hP.exists_positive_cell
  have hab : a ≠ b := by
    intro h
    subst b
    rw [ha i] at hib
    exact lt_irrefl _ hib
  by_cases hrest : 0 < totalMass (eraseColumns P {a, b})
  · have hstrict := separationProbability_split_zero_column_strict hP.1 a b hab ha hrest i hib
    have hle := hmax _ (blendColumns_isProbability hP a b hab (1 / 2) (by norm_num) (by norm_num))
    exact (not_lt_of_ge hle) hstrict
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have hc : ∀ u, P u c = 0 := by
    intro u
    have hentry := nonnegative_entry_le_totalMass (eraseColumns_nonneg hP.1 {a, b}) u c
    simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hca, hcb, or_self,
      if_false] at hentry
    exact le_antisymm (hentry.trans (le_of_not_gt hrest)) (hP.1 u c)
  let R := blendColumns P a b (1 / 2)
  have hR : IsProbability R := blendColumns_isProbability hP a b hab (1 / 2) (by norm_num) (by norm_num)
  have hRmax : IsSeparationGlobalMax R 3 := hmax.split_zero_column hP a b hab ha
  have hRc : ∀ u, R u c = 0 := by
    intro u
    simpa only [R, DittertRybin.blendColumns, if_neg hca, if_neg hcb] using hc u
  have hRia : 0 < R i a := by
    dsimp [R]
    rw [blendColumns_left, ha i]
    linarith only [hib]
  have hRib : 0 < R i b := by
    dsimp [R]
    rw [blendColumns_right P a b hab, ha i]
    linarith only [hib]
  have hrestR : 0 < totalMass (eraseColumns R {c, b}) := by
    have hentry := nonnegative_entry_le_totalMass (eraseColumns_nonneg hR.1 {c, b}) i a
    have hac : a ≠ c := Ne.symm hca
    simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hac, hab, or_self,
      if_false] at hentry
    exact hRia.trans_le hentry
  have hstrict := separationProbability_split_zero_column_strict hR.1 c b hcb hRc hrestR i hRib
  have hle := hRmax _ (blendColumns_isProbability hR c b hcb (1 / 2) (by norm_num) (by norm_num))
  exact (not_lt_of_ge hle) hstrict

theorem IsSeparationGlobalMax.column_mass_pos {m n : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (j : Fin n) : 0 < colSum P j := by
  by_contra hj
  apply hmax.no_zero_column hP hn j
  intro i
  have hentry : P i j ≤ colSum P j :=
    Finset.single_le_sum (fun i _ => hP.1 i j) (Finset.mem_univ i)
  exact le_antisymm (hentry.trans (le_of_not_gt hj)) (hP.1 i j)

theorem IsSeparationGlobalMax.row_mass_pos {m n : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hm : 3 ≤ m)
    (i : Fin m) : 0 < rowSum P i :=
  hmax.transpose.column_mass_pos hP.transpose hm i

end DittertRybin
