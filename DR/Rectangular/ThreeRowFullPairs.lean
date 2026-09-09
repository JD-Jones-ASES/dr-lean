import DR.Rectangular.ThreeRowFullColumn

/-! Strict remaining-row majorities forced by a doubleton pair with a full column left over. -/

namespace DittertRybin
open scoped BigOperators

/-- A positive physical column survives deletion of a different pair in every row. -/
theorem threeRowRemainingRow_pos_of_full {n : ℕ} {P : Board 3 n} (hP : ∀ i j, 0 ≤ P i j)
    (a b : Fin n) (hab : a ≠ b) (c : Fin n) (hca : c ≠ a) (hcb : c ≠ b)
    (hc : ThreeRowFullColumn P c) (r : Fin 3) : 0 < threeRowRemainingRow P a b r := by
  have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    eraseColumns_nonneg hP {a, b} r j) (Finset.mem_univ c)
  change eraseColumns P {a, b} r c ≤ rowSum (eraseColumns P {a, b}) r at he
  rw [rowSum_eraseColumns_pair P a b hab r] at he
  change eraseColumns P {a, b} r c ≤ threeRowRemainingRow P a b r at he
  simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hca, hcb, or_self, if_false] at he
  exact (hc r).trans_le he

/-- Under the Schur conditions, strict full-row ordering also orders the residual masses. -/
theorem threeRow_proper_pair_remaining_order {b e x y z : ℝ}
    (hb : 0 < b) (he : 0 < e) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hD : 0 < x ^ 2 + x * y + y ^ 2 - z ^ 2)
    (hleft : e * y * (2 * (x + y + z) - y) ≤ b * (x ^ 2 + x * y + y ^ 2 - z ^ 2))
    (hright : b * x * (2 * (x + y + z) - x) ≤ e * (x ^ 2 + x * y + y ^ 2 - z ^ 2))
    (hrow : y + b < x + e) : y < x := by
  by_contra hn
  have hxy : x ≤ y := le_of_not_gt hn
  by_cases heq : x = y
  · subst y
    have h := threeRow_proper_pair_equal_remainders hb he hx hz
      (by nlinarith only [hD]) (by nlinarith only [hleft]) (by nlinarith only [hright])
    linarith only [h.2.2, hrow]
  · have hlt : x < y := lt_of_le_of_ne hxy heq
    have heb := orderThree_proper_pair_entry_order (b := e) (e := b) (x := y) (y := x) (z := z)
      he hx hz hlt (by nlinarith only [hD]) (by nlinarith only [hleft])
    linarith only [hrow, hlt, heb]

/-- The residual mass in the larger omitted row exceeds the other two combined. -/
theorem IsSeparationGlobalMax.threeRow_full_pair_majority {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (a b : Fin n) (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (c : Fin n) (hc : ThreeRowFullColumn P c) (hrow : rowSum P h < rowSum P i) :
    threeRowRemainingRow P a b h + threeRowRemainingRow P a b k < threeRowRemainingRow P a b i := by
  have ha' := (threeRowDoublet_iff_other_rows P i h k hih hik hhk a).mp ha
  have hb' := (threeRowDoublet_iff_other_rows P h i k hih.symm hhk hik b).mp hb
  have hab : a ≠ b := by
    intro hab
    exact (ne_of_gt hb'.2.1) (hab ▸ ha'.1)
  have hca : c ≠ a := by
    intro hca
    exact (ne_of_gt (hc i)) (hca.symm ▸ ha'.1)
  have hcb : c ≠ b := by
    intro hcb
    exact (ne_of_gt (hc h)) (hcb.symm ▸ hb'.1)
  let x := threeRowRemainingRow P a b i
  let y := threeRowRemainingRow P a b h
  let z := threeRowRemainingRow P a b k
  have hx : 0 < x := threeRowRemainingRow_pos_of_full hP.1 a b hab c hca hcb hc i
  have hy : 0 < y := threeRowRemainingRow_pos_of_full hP.1 a b hab c hca hcb hc h
  have hz : 0 < z := threeRowRemainingRow_pos_of_full hP.1 a b hab c hca hcb hc k
  have hs : x + y + z = totalMass P - colSum P a - colSum P b :=
    threeRowRemainingRow_sum_other_rows P a b i h k hih hik hhk
  have hc0 := hmax.threeRow_comparison_eq_zero hP a b k ha'.2.2 hb'.2.2
  have hl0 := hmax.threeRow_comparison_nonneg hP a b i hb'.2.1
  have hr0 : (∑ l, threeRowColumnComparison P a b h l * (P l a - P l b)) ≤ 0 := by
    have hg := hmax.threeRow_gradient_le hP (h, b) (h, a) ha'.2.1
    have hd := threeRow_column_gradient_difference P a b h
    dsimp at hg
    linarith only [hg, hd]
  rw [threeRowColumnComparison_dot P a b k i h hik.symm hhk.symm hih,
    ha'.1, hb'.1, ← hs] at hc0
  rw [threeRowColumnComparison_dot P a b i h k hih hik hhk, ha'.1, hb'.1, ← hs] at hl0
  rw [threeRowColumnComparison_dot P a b h i k hih.symm hhk hik, ha'.1, hb'.1, ← hs] at hr0
  have hcommon : -(x + z) * P i b + (y + z) * P h a + (x + y + z) * (P k a - P k b) = 0 := by
    change (x + y + z) * (P k a - P k b) + (z + x) * (0 - P i b) +
      (z + y) * (P h a - 0) = 0 at hc0
    nlinarith only [hc0]
  have hleft : 0 ≤ -(x + y + z) * P i b + (x + y) * P h a + (x + z) * (P k a - P k b) := by
    change 0 ≤ (x + y + z) * (0 - P i b) + (x + y) * (P h a - 0) +
      (x + z) * (P k a - P k b) at hl0
    nlinarith only [hl0]
  have hright : -(x + y) * P i b + (x + y + z) * P h a + (y + z) * (P k a - P k b) ≤ 0 := by
    change (x + y + z) * (P h a - 0) + (y + x) * (0 - P i b) +
      (y + z) * (P k a - P k b) ≤ 0 at hr0
    nlinarith only [hr0]
  have hE : 0 < x + y + z := by linarith
  obtain ⟨hL, hR⟩ := orderThree_proper_pair_schur hE hcommon hleft hright
  have hD := orderThree_proper_pair_D_pos ha'.2.1 hb'.2.1 hx.le hy.le hz.le hE hL hR
  have hrow' : y + P h a < x + P i b := by
    dsimp [x, y, threeRowRemainingRow]
    rw [ha'.1, hb'.1]
    linarith only [hrow]
  have hxy := threeRow_proper_pair_remaining_order ha'.2.1 hb'.2.1 hx.le hy.le hz.le hD hL hR hrow'
  have hq := orderThree_proper_pair_quartic ha'.2.1 hb'.2.1 hx.le hy.le hz.le hD hL hR
  exact orderThree_proper_pair_majority hx hy hz hxy.le hD hq

/-- Any two occurring doubleton types omit rows of different mass when a full column occurs. -/
theorem IsSeparationGlobalMax.threeRow_full_pair_row_masses_ne {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h : Fin 3) (hih : i ≠ h) (a b : Fin n)
    (ha : ThreeRowDoublet P i a) (hb : ThreeRowDoublet P h b)
    (c : Fin n) (hc : ThreeRowFullColumn P c) : rowSum P i ≠ rowSum P h := by
  intro hrow
  obtain ⟨k, hki, hkh⟩ := Fin.exists_ne_and_ne_of_two_lt i h (by norm_num : 2 < 3)
  have hab : a ≠ b := by
    intro hab
    exact hih ((hb.missing_unique i (hab ▸ ha.1)))
  have hca : c ≠ a := by
    intro hca
    exact (ne_of_gt (hc i)) (hca.symm ▸ ha.1)
  have hcb : c ≠ b := by
    intro hcb
    exact (ne_of_gt (hc h)) (hcb.symm ▸ hb.1)
  have hp := threeRowRemainingRow_pos_of_full hP.1 a b hab c hca hcb hc k
  have hz := hmax.threeRow_doublet_common_remaining_zero hP hn i h k hih hki.symm hkh.symm a b ha hb hrow
  exact (ne_of_gt hp) hz

end DittertRybin
