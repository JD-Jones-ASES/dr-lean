import DR.Rectangular.ThreeRowSingleDoubletNormal
import DR.Rectangular.ThreeRowTwoDoubletScalar

/-! Two doubleton types are excluded by actual residual majorities and a division-free inverse bound. -/
namespace DittertRybin
open scoped BigOperators

/-- Same-type doubleton columns coincide; the full columns are handled separately. -/
def ThreeRowDoubletColumnsEqual {n : ℕ} (P : Board 3 n) : Prop :=
  ∀ i a b, ThreeRowDoublet P i a → ThreeRowDoublet P i b → ∀ r, P r a = P r b

/-- The exclusive entry in the larger omitted row exceeds its common-row entry.
This uses a sum over every physical column and places no bound on support multiplicities. -/
theorem IsSeparationGlobalMax.threeRow_two_doublet_entry_order {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hsame : ThreeRowFullColumnsEqual P) (hdouble : ThreeRowDoubletColumnsEqual P)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (a b : Fin n) (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (q : Fin n) (hq : ThreeRowFullColumn P q) (hrow : rowSum P h < rowSum P i)
    (htypes : ∀ r j, ThreeRowDoublet P r j → r = i ∨ r = h) : P k b < P i b := by
  have hoffset := hmax.threeRow_full_column_offset hP hn hsame i h k hih hik hhk b hb q hq hrow
  have hmajor := hmax.threeRow_full_pair_majority hP i h k hih hik hhk a b ha hb q hq hrow
  by_contra hnot
  have hentry : P i b ≤ P k b := le_of_not_gt hnot
  have hterm (j : Fin n) : P i j ≤ P h j + P k j := by
    rcases hmax.threeRow_columns_full_or_doublet hP hn j with hf | ⟨r,hr⟩
    · rw [hsame j q hf hq i, hsame j q hf hq h, hsame j q hf hq k]
      linarith only [hoffset, hP.1 i b, hq k]
    · rcases htypes r j hr with hri | hrh
      · subst r
        rw [hr.1]
        exact add_nonneg (hP.1 h j) (hP.1 k j)
      · subst r
        rw [hdouble h j b hr hb i, hdouble h j b hr hb h, hdouble h j b hr hb k, hb.1, zero_add]
        exact hentry
  have hsum : rowSum (eraseColumns P {a,b}) i ≤
      rowSum (eraseColumns P {a,b}) h + rowSum (eraseColumns P {a,b}) k := by
    simp only [rowSum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ ({a,b} : Finset (Fin n))
    · simp [eraseColumns, hj]
    · simpa only [eraseColumns, hj, if_false] using hterm j
  have hab : a ≠ b := by
    intro he
    exact hih (hb.missing_unique i (he ▸ ha.1))
  rw [rowSum_eraseColumns_pair P a b hab i, rowSum_eraseColumns_pair P a b hab h,
    rowSum_eraseColumns_pair P a b hab k] at hsum
  exact (not_lt_of_ge hsum) hmajor

/-- Ordered omitted-row masses cannot occur with only their two doubleton types and full columns. -/
theorem IsSeparationGlobalMax.threeRow_ordered_two_doublets_impossible {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (hsame : ThreeRowFullColumnsEqual P) (hdouble : ThreeRowDoubletColumnsEqual P)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (a b : Fin n) (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (q : Fin n) (hq : ThreeRowFullColumn P q) (hrow : rowSum P h < rowSum P i)
    (htypes : ∀ r j, ThreeRowDoublet P r j → r = i ∨ r = h) : False := by
  have hoffset := hmax.threeRow_full_column_offset hP hn hsame i h k hih hik hhk b hb q hq hrow
  have hentry := hmax.threeRow_two_doublet_entry_order hP hn hsame hdouble i h k hih hik hhk a b ha hb q hq hrow htypes
  have hab : a ≠ b := by
    intro he
    exact hih (hb.missing_unique i (he ▸ ha.1))
  have hqa : q ≠ a := by
    intro he
    exact (ne_of_gt (hq i)) (he.symm ▸ ha.1)
  have hqb : q ≠ b := by
    intro he
    exact (ne_of_gt (hq h)) (he.symm ▸ hb.1)
  have hremain (r : Fin 3) (har : 0 < P r a) : 0 < threeRowRemainingRow P b q r := by
    have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      eraseColumns_nonneg hP.1 {b,q} r j) (Finset.mem_univ a)
    change eraseColumns P {b,q} r a ≤ rowSum (eraseColumns P {b,q}) r at he
    rw [rowSum_eraseColumns_pair P b q hqb.symm r] at he
    simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hab, hqa.symm, or_self, if_false] at he
    exact har.trans_le he
  let p := threeRowRemainingRow P b q i
  let s := threeRowRemainingRow P b q k
  let r := threeRowRemainingRow P b q h
  have hr : 0 < r := hremain h (ha.pos_of_ne h hih.symm)
  have hs : 0 < s := hremain k (ha.pos_of_ne k hik.symm)
  have hpr : r < p := by
    dsimp [r,p,threeRowRemainingRow]
    rw [hb.1]
    linarith only [hrow,hoffset]
  have hx : P i b-P i q < P h q := by linarith only [hoffset, hq i]
  have hy : P k b-P k q < P h q := by linarith only [hoffset,hentry,hq i,hq k]
  have hmass : p+s+r = totalMass P-colSum P b-colSum P q :=
    threeRowRemainingRow_sum_other_rows P b q i k h hik hih hhk.symm
  have heq1 := hmax.threeRow_comparison_eq_zero hP b q i (hb.pos_of_ne i hih) (hq i)
  have heq2 := hmax.threeRow_comparison_eq_zero hP b q k (hb.pos_of_ne k hhk.symm) (hq k)
  have hzero := hmax.threeRow_comparison_nonneg hP b q h (hq h)
  rw [threeRowColumnComparison_dot P b q i k h hik hih hhk.symm, ← hmass, hb.1] at heq1
  rw [threeRowColumnComparison_dot P b q k i h hik.symm hhk.symm hih, ← hmass, hb.1] at heq2
  rw [threeRowColumnComparison_dot P b q h i k hih.symm hhk hik, ← hmass, hb.1] at hzero
  apply threeRow_two_doublet_inverse_impossible hpr hs hr (hq h) hx hy
  · change (p+s+r)*(P i b-P i q)+(p+s)*(P k b-P k q)+(p+r)*(0-P h q)=0 at heq1
    linarith only [heq1]
  · change (p+s+r)*(P k b-P k q)+(s+p)*(P i b-P i q)+(s+r)*(0-P h q)=0 at heq2
    nlinarith only [heq2]
  · change 0 ≤ (p+s+r)*(0-P h q)+(r+p)*(P i b-P i q)+(r+s)*(P k b-P k q) at hzero
    nlinarith only [hzero]

end DittertRybin
