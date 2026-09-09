import DR.Rectangular.ThreeRowSingletons

/-! Exact pair inequalities after equal-support row normalization of a singleton candidate. -/

namespace DittertRybin
open scoped BigOperators

theorem threeRow_singleton_full_scalar {u v w x y : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ w) (hE : 0 < x + 2 * y)
    (hcommon : (x + 2 * y) * (u - v) = 2 * (x + y) * w) : v + w ≤ u := by
  have hp : 0 ≤ (x + 2 * y) * (u - v - w) := by
    nlinarith only [hcommon, mul_nonneg hx hw]
  have h := nonneg_of_mul_nonneg_right hp hE
  linarith only [h]

theorem threeRow_singleton_opposite_scalar {u w x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hE : 0 < x + 2 * y)
    (hmissing : 0 ≤ (x + y) * u - (x + 4 * y) * w) : w ≤ u := by
  have hxy : 0 < x + y := by linarith only [hx, hy, hE]
  have hp : 0 ≤ (x + y) * (u - w) := by
    nlinarith only [hmissing, mul_nonneg hy hw]
  have h := nonneg_of_mul_nonneg_right hp hxy
  linarith only [h]

theorem threeRow_same_row_remaining {n : ℕ} (P : Board 3 n) (h k : Fin 3)
    (hsym : ∀ j, P h j = P k j) (a b : Fin n) :
    threeRowRemainingRow P a b h = threeRowRemainingRow P a b k := by
  unfold threeRowRemainingRow rowSum
  simp_rw [hsym]

/-- A full column next to a singleton is constrained by equality at their shared positive row. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_full_bound {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a b : Fin n) (ha : ThreeRowSingleton P i a)
    (hbi : 0 < P i b) (hbh : 0 < P h b) : P i b + P h b ≤ P i a := by
  have ha' := (threeRowSingleton_iff_other_rows P i h k hih hik hhk a).mp ha
  have hab : a ≠ b := by
    intro heq
    have hz := ha'.2.1
    rw [heq] at hz
    exact (ne_of_gt hbh) hz
  let x := threeRowRemainingRow P a b i
  let y := threeRowRemainingRow P a b h
  have hx : 0 ≤ x := threeRowRemainingRow_nonneg hP.1 a b hab i
  have hr := threeRow_same_row_remaining P h k hsym a b
  have hs : x + 2 * y = totalMass P - colSum P a - colSum P b := by
    have hh := threeRowRemainingRow_sum_other_rows P a b i h k hih hik hhk
    rw [← hr] at hh
    change x + y + y = _ at hh
    linarith only [hh]
  have hE : 0 < x + 2 * y := hs.symm ▸ hmax.threeRow_remaining_mass_pos hP hn a b hab
  have hc := hmax.threeRow_comparison_eq_zero hP a b i ha'.1 hbi
  rw [threeRowColumnComparison_dot P a b i h k hih hik hhk,
    ha'.2.1, ha'.2.2, ← hsym b, ← hr, ← hs] at hc
  apply threeRow_singleton_full_scalar (u := P i a) (v := P i b) hx hbh.le hE
  change (x + 2 * y) * (P i a - P i b) + (x + y) * (0 - P h b) +
    (x + y) * (0 - P h b) = 0 at hc
  nlinarith only [hc]

/-- The opposite doubleton has no larger common entry than the selected singleton. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_opposite_bound {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a b : Fin n) (ha : ThreeRowSingleton P i a)
    (hbi : P i b = 0) (hbh : 0 < P h b) : P h b ≤ P i a := by
  have ha' := (threeRowSingleton_iff_other_rows P i h k hih hik hhk a).mp ha
  have hab : a ≠ b := by
    intro heq
    have hz := ha'.2.1
    rw [heq] at hz
    exact (ne_of_gt hbh) hz
  let x := threeRowRemainingRow P a b i
  let y := threeRowRemainingRow P a b h
  have hx : 0 ≤ x := threeRowRemainingRow_nonneg hP.1 a b hab i
  have hy : 0 ≤ y := threeRowRemainingRow_nonneg hP.1 a b hab h
  have hr := threeRow_same_row_remaining P h k hsym a b
  have hs : x + 2 * y = totalMass P - colSum P a - colSum P b := by
    have hh := threeRowRemainingRow_sum_other_rows P a b i h k hih hik hhk
    rw [← hr] at hh
    change x + y + y = _ at hh
    linarith only [hh]
  have hE : 0 < x + 2 * y := hs.symm ▸ hmax.threeRow_remaining_mass_pos hP hn a b hab
  have hc := hmax.threeRow_comparison_nonneg hP a b h hbh
  rw [threeRowColumnComparison_dot P a b h i k hih.symm hhk hik,
    ha'.2.1, ha'.2.2, hbi, ← hsym b, ← hr, ← hs] at hc
  apply threeRow_singleton_opposite_scalar (u := P i a) hx hy hbh.le hE
  change 0 ≤ (x + 2 * y) * (0 - P h b) + (y + x) * (P i a - 0) +
    (y + y) * (0 - P h b) at hc
  nlinarith only [hc]

/-- Missing gradient at a row-symmetric singleton as a sum of genuine physical-column terms. -/
theorem threeRow_symmetric_singleton_gradient_sum {n : ℕ} (P : Board 3 n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a) :
    threeRowReducedGradient P h a - threeRowReducedGradient P i a =
      ∑ j, P h j * (P i a + P i j - P h j) := by
  have ha' := (threeRowSingleton_iff_other_rows P i h k hih hik hhk a).mp ha
  rw [threeRow_singleton_gradient_difference P i h k hih hik hhk a ha'.2.1 ha'.2.2,
    threeRowPair_eq_other_rows P h k i hhk hih.symm hik.symm,
    threeRowPair_eq_other_rows P i h k hih hik hhk]
  unfold rowSum
  simp_rw [← hsym]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  ring

/-- Every physical-column contribution to the singleton's missing derivative vanishes. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_terms_zero {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a) :
    ∀ j, P h j * (P i a + P i j - P h j) = 0 := by
  have ht (j : Fin n) : 0 ≤ P h j * (P i a + P i j - P h j) := by
    by_cases hhj : P h j = 0
    · rw [hhj, zero_mul]
    have hhp : 0 < P h j := lt_of_le_of_ne (hP.1 h j) (Ne.symm hhj)
    apply mul_nonneg (hP.1 h j)
    by_cases hij : P i j = 0
    · have h := hmax.threeRow_symmetric_singleton_opposite_bound hP hn i h k hih hik hhk hsym a j ha hij hhp
      rw [hij, add_zero]
      exact sub_nonneg.mpr h
    · have hip : 0 < P i j := lt_of_le_of_ne (hP.1 i j) (Ne.symm hij)
      have h := hmax.threeRow_symmetric_singleton_full_bound hP hn i h k hih hik hhk hsym a j ha hip hhp
      linarith only [h, hip]
  have hid := threeRow_symmetric_singleton_gradient_sum P i h k hih hik hhk hsym a ha
  have hgrad := hmax.threeRow_gradient_le hP (h, a) (i, a) ha.1
  dsimp at hgrad
  have hzero : (∑ j, P h j * (P i a + P i j - P h j)) = 0 := by
    apply le_antisymm (by linarith only [hid, hgrad])
    exact Finset.sum_nonneg fun j _ => ht j
  intro j
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ht j)).mp hzero j (Finset.mem_univ j)

/-- A row-symmetric singleton candidate has no full column; every opposite entry equals its mass. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_opposite_entries {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a)
    (b : Fin n) (hb : 0 < P h b) : P i b = 0 ∧ P h b = P i a := by
  have ht := hmax.threeRow_symmetric_singleton_terms_zero hP hn i h k hih hik hhk hsym a ha b
  have hf := (mul_eq_zero.mp ht).resolve_left (ne_of_gt hb)
  have hz : P i b = 0 := by
    by_contra hz
    have hip : 0 < P i b := lt_of_le_of_ne (hP.1 i b) (Ne.symm hz)
    have hbound := hmax.threeRow_symmetric_singleton_full_bound hP hn i h k hih hik hhk hsym a b ha hip hb
    linarith only [hf, hbound, hip]
  exact ⟨hz, by linarith only [hf, hz]⟩

/-- The raw opposite-column inequality retains the residual mass for rigidity. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_opposite_comparison {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a b : Fin n) (ha : ThreeRowSingleton P i a)
    (hbi : P i b = 0) (hbh : 0 < P h b) :
    let x := threeRowRemainingRow P a b i
    let y := threeRowRemainingRow P a b h
    0 ≤ (x + y) * P i a - (x + 4 * y) * P h b := by
  have ha' := (threeRowSingleton_iff_other_rows P i h k hih hik hhk a).mp ha
  have hr := threeRow_same_row_remaining P h k hsym a b
  have hs := threeRowRemainingRow_sum_other_rows P a b i h k hih hik hhk
  rw [← hr] at hs
  have hc := hmax.threeRow_comparison_nonneg hP a b h hbh
  rw [threeRowColumnComparison_dot P a b h i k hih.symm hhk hik,
    ha'.2.1, ha'.2.2, hbi, ← hsym b, ← hr, ← hs] at hc
  dsimp
  nlinarith only [hc]

/-- All mass in the two equal rows lies in the one selected opposite column. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_remainder_zero {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a)
    (b : Fin n) (hb : 0 < P h b) : threeRowRemainingRow P a b h = 0 := by
  have he := hmax.threeRow_symmetric_singleton_opposite_entries hP hn i h k hih hik hhk hsym a ha b hb
  have hc := hmax.threeRow_symmetric_singleton_opposite_comparison hP i h k hih hik hhk hsym a b ha he.1 hb
  have hab : a ≠ b := by
    intro hab
    have hp := ha.1
    rw [hab, he.1] at hp
    exact lt_irrefl _ hp
  have hy := threeRowRemainingRow_nonneg hP.1 a b hab h
  rw [← he.2] at hc
  have hp : threeRowRemainingRow P a b h * P h b ≤ 0 := by nlinarith only [hc]
  exact le_antisymm (nonpos_of_mul_nonpos_left hp hb) hy

/-- The actual support in each of the two equal rows is a single physical column. -/
theorem IsSeparationGlobalMax.threeRow_symmetric_singleton_other_zero {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h k : Fin 3) (hih : i ≠ h) (hik : i ≠ k) (hhk : h ≠ k)
    (hsym : ∀ j, P h j = P k j) (a : Fin n) (ha : ThreeRowSingleton P i a)
    (b : Fin n) (hb : 0 < P h b) (c : Fin n) (hcb : c ≠ b) : P h c = 0 := by
  have ha' := (threeRowSingleton_iff_other_rows P i h k hih hik hhk a).mp ha
  by_cases hca : c = a
  · simpa only [hca] using ha'.2.1
  have hab : a ≠ b := by
    intro hab
    exact (ne_of_gt hb) (hab ▸ ha'.2.1)
  have he := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    eraseColumns_nonneg hP.1 {a, b} h j) (Finset.mem_univ c)
  change eraseColumns P {a, b} h c ≤ rowSum (eraseColumns P {a, b}) h at he
  rw [rowSum_eraseColumns_pair P a b hab h] at he
  change eraseColumns P {a, b} h c ≤ threeRowRemainingRow P a b h at he
  rw [hmax.threeRow_symmetric_singleton_remainder_zero hP hn i h k hih hik hhk hsym a ha b hb] at he
  simp only [eraseColumns, Finset.mem_insert, Finset.mem_singleton, hca, hcb, or_self, if_false] at he
  exact le_antisymm he (hP.1 h c)

end DittertRybin
