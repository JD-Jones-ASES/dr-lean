import DR.Rectangular.ThreeRowComparison

/-! Boundary-safe ordering for two doubleton columns of an actual global maximizer. -/

namespace DittertRybin
open scoped BigOperators

/-- A physical doubleton column, indexed by its missing row. -/
def ThreeRowDoublet {n : ℕ} (P : Board 3 n) (i : Fin 3) (j : Fin n) : Prop :=
  P i j = 0 ∧ 0 < P (i + 1) j ∧ 0 < P (i + 2) j

/-- Equal residual masses force a zero common-row remainder, including singular boundaries. -/
theorem threeRow_proper_pair_equal_remainders {b e x z : ℝ}
    (hb : 0 < b) (he : 0 < e) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hD : 0 < 3 * x ^ 2 - z ^ 2)
    (hleft : e * x * (2 * (x + x + z) - x) ≤ b * (3 * x ^ 2 - z ^ 2))
    (hright : b * x * (2 * (x + x + z) - x) ≤ e * (3 * x ^ 2 - z ^ 2)) :
    0 < x ∧ z = 0 ∧ e = b := by
  have hxp : 0 < x := by nlinarith only [hx, hD, sq_nonneg z]
  have hsum : (b + e) * z * (2 * x + z) ≤ 0 := by nlinarith only [hleft, hright]
  have hz0 : z = 0 := by
    by_contra hn
    have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hn)
    have hp := mul_pos (mul_pos (add_pos hb he) hzp) (by linarith : 0 < 2 * x + z)
    exact (not_lt_of_ge hsum) hp
  have hc : 0 < 3 * x ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hxp)
  have heb : e * (3 * x ^ 2) ≤ b * (3 * x ^ 2) := by
    rw [hz0] at hleft
    nlinarith only [hleft]
  have hbe : b * (3 * x ^ 2) ≤ e * (3 * x ^ 2) := by
    rw [hz0] at hright
    nlinarith only [hright]
  exact ⟨hxp, hz0, le_antisymm ((mul_le_mul_iff_left₀ hc).mp heb)
    ((mul_le_mul_iff_left₀ hc).mp hbe)⟩

/-- Ordering by full omitted-row masses, without dividing by either residual mass. -/
theorem threeRow_proper_pair_row_order {b e x y z : ℝ}
    (hb : 0 < b) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hD : 0 < x ^ 2 + x * y + y ^ 2 - z ^ 2)
    (hright : b * x * (2 * (x + y + z) - x) ≤ e * (x ^ 2 + x * y + y ^ 2 - z ^ 2))
    (hrow : y + b < x + e) : b ≤ e := by
  by_contra hn
  have heb : e < b := lt_of_not_ge hn
  have hxy : y < x := by linarith only [hrow, heb]
  exact hn (orderThree_proper_pair_entry_order hb hy hz hxy hD hright)

/-- Equality of the omitted row masses has a rigid, fully retained boundary case. -/
theorem threeRow_proper_pair_equal_rows {b e x y z : ℝ}
    (hb : 0 < b) (he : 0 < e) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hD : 0 < x ^ 2 + x * y + y ^ 2 - z ^ 2)
    (hleft : e * y * (2 * (x + y + z) - y) ≤ b * (x ^ 2 + x * y + y ^ 2 - z ^ 2))
    (hright : b * x * (2 * (x + y + z) - x) ≤ e * (x ^ 2 + x * y + y ^ 2 - z ^ 2))
    (hrow : x + e = y + b) : x = y ∧ 0 < x ∧ z = 0 ∧ e = b := by
  have hxy : x = y := by
    apply le_antisymm
    · by_contra hn
      have hlt : y < x := lt_of_not_ge hn
      have hbe := orderThree_proper_pair_entry_order hb hy hz hlt hD hright
      linarith only [hrow, hlt, hbe]
    · by_contra hn
      have hlt : x < y := lt_of_not_ge hn
      have hD' : 0 < y ^ 2 + y * x + x ^ 2 - z ^ 2 := by nlinarith only [hD]
      have hleft' : e * y * (2 * (y + x + z) - y) ≤ b * (y ^ 2 + y * x + x ^ 2 - z ^ 2) := by
        nlinarith only [hleft]
      have heb := orderThree_proper_pair_entry_order he hx hz hlt hD' hleft'
      linarith only [hrow, hlt, heb]
  subst y
  refine ⟨rfl, ?_⟩
  apply threeRow_proper_pair_equal_remainders hb he hx hz
  · nlinarith only [hD]
  · nlinarith only [hleft]
  · nlinarith only [hright]

/-- The three physical residual masses sum to the remaining total mass. -/
theorem threeRowRemainingRow_sum {n : ℕ} (P : Board 3 n) (a b : Fin n) (i : Fin 3) :
    threeRowRemainingRow P a b i + threeRowRemainingRow P a b (i + 2) +
      threeRowRemainingRow P a b (i + 1) = totalMass P - colSum P a - colSum P b := by
  fin_cases i <;> simp [threeRowRemainingRow, totalMass, colSum, Fin.sum_univ_succ] <;> ring

/-- Raw full-simplex comparison for two doubleton types.
The common row is positive in both columns; the two missing cells retain their inequalities. -/
theorem IsSeparationGlobalMax.threeRow_doublet_pair_conditions {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P)
    (i : Fin 3) (a b : Fin n) (hv : ThreeRowDoublet P i a)
    (hw : ThreeRowDoublet P (i + 2) b) :
    let x := threeRowRemainingRow P a b i
    let y := threeRowRemainingRow P a b (i + 2)
    let z := threeRowRemainingRow P a b (i + 1)
    let aa := P (i + 1) a
    let bb := P (i + 2) a
    let ee := P i b
    let ff := P (i + 1) b
    (-(x + z) * ee + (y + z) * bb + (x + y + z) * (aa - ff) = 0) ∧
    (0 ≤ -(x + y + z) * ee + (x + y) * bb + (x + z) * (aa - ff)) ∧
    (-(x + y) * ee + (x + y + z) * bb + (y + z) * (aa - ff) ≤ 0) := by
  have he : 0 < P i b := by
    have h := hw.2.1
    convert h using 1; congr 1; fin_cases i <;> decide
  have hf : 0 < P (i + 1) b := by
    have h := hw.2.2
    convert h using 1; congr 1; fin_cases i <;> decide
  have hc := hmax.threeRow_comparison_eq_zero hP a b (i + 1) hv.2.1 hf
  have hl := hmax.threeRow_comparison_nonneg hP a b i he
  have hr := hmax.threeRow_comparison_nonneg hP b a (i + 2) hv.2.2
  have hzv := hv.1
  have hzw := hw.1
  dsimp
  fin_cases i <;>
    simp [threeRowColumnComparison, threeRowRemainingRow, totalMass, colSum, Fin.sum_univ_succ] at hc hl hr hzv hzw ⊢ <;>
    rw [hzv, hzw] at hc hl hr ⊢ <;>
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [hc, hl, hr]

/-- Different doubleton types necessarily occupy different physical columns. -/
theorem ThreeRowDoublet.columns_ne {n : ℕ} {P : Board 3 n} {i : Fin 3} {a b : Fin n}
    (hv : ThreeRowDoublet P i a) (hw : ThreeRowDoublet P (i + 2) b) : a ≠ b := by
  intro hab
  have hp := hv.2.2
  rw [hab, hw.1] at hp
  exact lt_irrefl _ hp

private theorem doublet_next_pos {n : ℕ} {P : Board 3 n} {i : Fin 3} {b : Fin n}
    (hw : ThreeRowDoublet P (i + 2) b) : 0 < P i b := by
  have h := hw.2.1
  convert h using 1; congr 1; fin_cases i <;> decide

/-- Schur inequalities and strict denominator positivity for actual doubleton columns. -/
theorem IsSeparationGlobalMax.threeRow_doublet_pair_schur {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a b : Fin n) (hv : ThreeRowDoublet P i a)
    (hw : ThreeRowDoublet P (i + 2) b) :
    let x := threeRowRemainingRow P a b i
    let y := threeRowRemainingRow P a b (i + 2)
    let z := threeRowRemainingRow P a b (i + 1)
    let bb := P (i + 2) a
    let ee := P i b
    0 < x ^ 2 + x * y + y ^ 2 - z ^ 2 ∧
      ee * y * (2 * (x + y + z) - y) ≤ bb * (x ^ 2 + x * y + y ^ 2 - z ^ 2) ∧
      bb * x * (2 * (x + y + z) - x) ≤ ee * (x ^ 2 + x * y + y ^ 2 - z ^ 2) := by
  let x := threeRowRemainingRow P a b i
  let y := threeRowRemainingRow P a b (i + 2)
  let z := threeRowRemainingRow P a b (i + 1)
  have hab := hv.columns_ne hw
  have hx : 0 ≤ x := threeRowRemainingRow_nonneg hP.1 a b hab i
  have hy : 0 ≤ y := threeRowRemainingRow_nonneg hP.1 a b hab (i + 2)
  have hz : 0 ≤ z := threeRowRemainingRow_nonneg hP.1 a b hab (i + 1)
  have hE : 0 < x + y + z := by
    change 0 < threeRowRemainingRow P a b i + threeRowRemainingRow P a b (i + 2) +
      threeRowRemainingRow P a b (i + 1)
    rw [threeRowRemainingRow_sum]
    exact hmax.threeRow_remaining_mass_pos hP hn a b hab
  have hc := hmax.threeRow_doublet_pair_conditions hP i a b hv hw
  obtain ⟨hl, hr⟩ := orderThree_proper_pair_schur hE hc.1 hc.2.1 hc.2.2
  exact ⟨orderThree_proper_pair_D_pos hv.2.2 (doublet_next_pos hw) hx hy hz hE hl hr, hl, hr⟩

/-- Strict ordering of the omitted row masses determines the weak exclusive-entry order. -/
theorem IsSeparationGlobalMax.threeRow_doublet_row_order {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a b : Fin n) (hv : ThreeRowDoublet P i a)
    (hw : ThreeRowDoublet P (i + 2) b) (hrow : rowSum P (i + 2) < rowSum P i) :
    P (i + 2) a ≤ P i b := by
  have hs := hmax.threeRow_doublet_pair_schur hP hn i a b hv hw
  apply threeRow_proper_pair_row_order hv.2.2
    (threeRowRemainingRow_nonneg hP.1 a b (hv.columns_ne hw) (i + 2))
    (threeRowRemainingRow_nonneg hP.1 a b (hv.columns_ne hw) (i + 1)) hs.1 hs.2.2
  unfold threeRowRemainingRow
  rw [hv.1, hw.1]
  linarith only [hrow]

/-- The equality case includes exactly which residual row must vanish. -/
theorem IsSeparationGlobalMax.threeRow_doublet_equal_rows {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a b : Fin n) (hv : ThreeRowDoublet P i a)
    (hw : ThreeRowDoublet P (i + 2) b) (hrow : rowSum P i = rowSum P (i + 2)) :
    threeRowRemainingRow P a b i = threeRowRemainingRow P a b (i + 2) ∧
      0 < threeRowRemainingRow P a b i ∧ threeRowRemainingRow P a b (i + 1) = 0 ∧
      P i b = P (i + 2) a ∧ P (i + 1) a = P (i + 1) b := by
  have hab := hv.columns_ne hw
  have hs := hmax.threeRow_doublet_pair_schur hP hn i a b hv hw
  have hrow' : threeRowRemainingRow P a b i + P i b =
      threeRowRemainingRow P a b (i + 2) + P (i + 2) a := by
    unfold threeRowRemainingRow
    rw [hv.1, hw.1]
    linarith only [hrow]
  obtain ⟨hxy, hx, hz, heb⟩ := threeRow_proper_pair_equal_rows hv.2.2 (doublet_next_pos hw)
    (threeRowRemainingRow_nonneg hP.1 a b hab i)
    (threeRowRemainingRow_nonneg hP.1 a b hab (i + 2))
    (threeRowRemainingRow_nonneg hP.1 a b hab (i + 1)) hs.1 hs.2.1 hs.2.2 hrow'
  refine ⟨hxy, hx, hz, heb, ?_⟩
  have hc := (hmax.threeRow_doublet_pair_conditions hP i a b hv hw).1
  rw [← hxy, hz, heb] at hc
  have hprod : (threeRowRemainingRow P a b i + threeRowRemainingRow P a b i) *
      (P (i + 1) a - P (i + 1) b) = 0 := by nlinarith only [hc]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (ne_of_gt (add_pos hx hx)))

/-- The reverse omitted-row ordering is equally valid at zero residual masses. -/
theorem IsSeparationGlobalMax.threeRow_doublet_row_order_reverse {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i : Fin 3) (a b : Fin n) (hv : ThreeRowDoublet P i a)
    (hw : ThreeRowDoublet P (i + 2) b) (hrow : rowSum P i < rowSum P (i + 2)) :
    P i b ≤ P (i + 2) a := by
  have hs := hmax.threeRow_doublet_pair_schur hP hn i a b hv hw
  apply threeRow_proper_pair_row_order (doublet_next_pos hw)
    (threeRowRemainingRow_nonneg hP.1 a b (hv.columns_ne hw) i)
    (threeRowRemainingRow_nonneg hP.1 a b (hv.columns_ne hw) (i + 1))
    (x := threeRowRemainingRow P a b (i + 2)) (e := P (i + 2) a)
  · nlinarith only [hs.1]
  · nlinarith only [hs.2.1]
  · unfold threeRowRemainingRow
    rw [hv.1, hw.1]
    linarith only [hrow]

/-- An orientation-free physical-column ordering API for any two distinct missing rows. -/
theorem IsSeparationGlobalMax.threeRow_doublet_exclusive_order {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n)
    (i h : Fin 3) (hih : i ≠ h) (a b : Fin n) (hv : ThreeRowDoublet P i a)
    (hw : ThreeRowDoublet P h b) (hrow : rowSum P h < rowSum P i) : P h a ≤ P i b := by
  by_cases hh : h = i + 2
  · subst h
    exact hmax.threeRow_doublet_row_order hP hn i a b hv hw hrow
  · have hi : i = h + 2 := by fin_cases i <;> fin_cases h <;> simp_all
    subst i
    exact hmax.threeRow_doublet_row_order_reverse hP hn h b a hw hv hrow

end DittertRybin
