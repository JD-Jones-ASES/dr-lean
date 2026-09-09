import DR.Rectangular.FourRowFiniteBernstein

/-!
# The actual finite-family parameter and denominator clearing

The two source intervals use u=a/N for a=5 and a=50. The three possible
ordinary-column denominators are N-c, with c=1,2,3. Their literal positive
clearing factor and cancellations are proved here, including the closed
interval endpoints. No interval is extended by finite numerical evidence.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowFiniteParameter (a n : ℕ) : ℝ := (a : ℝ) / n

noncomputable def fourRowFiniteDenominator (a u : ℝ) : ℝ :=
  ∏ q : Fin 3, (1 - ((q : ℕ) + 1 : ℝ) * u / a)

theorem fourRowFiniteParameter_interval {a n : ℕ} (ha : 0 < a)
    (han : a ≤ n) (hna : n ≤ 10 * a) :
    1/10 ≤ fourRowFiniteParameter a n ∧ fourRowFiniteParameter a n ≤ 1 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le ha han)
  have han' : (a : ℝ) ≤ n := by exact_mod_cast han
  have hna' : (n : ℝ) ≤ 10 * a := by exact_mod_cast hna
  constructor
  · exact (le_div_iff₀ hn).mpr (by linarith)
  · exact (div_le_one hn).mpr han'

theorem fourRowFiniteParameter_five {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 50) :
    1/10 ≤ fourRowFiniteParameter 5 n ∧ fourRowFiniteParameter 5 n ≤ 1 :=
  fourRowFiniteParameter_interval (by decide) hn.1 (by omega)

theorem fourRowFiniteParameter_fifty {n : ℕ} (hn : 50 ≤ n ∧ n ≤ 500) :
    1/10 ≤ fourRowFiniteParameter 50 n ∧ fourRowFiniteParameter 50 n ≤ 1 :=
  fourRowFiniteParameter_interval (by decide) hn.1 (by omega)

/-- The two closed parameter intervals cover precisely the requested finite range. -/
theorem fourRowFiniteParameter_coverage {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 500) :
    (5 ≤ n ∧ n ≤ 50 ∧ 1/10 ≤ fourRowFiniteParameter 5 n ∧ fourRowFiniteParameter 5 n ≤ 1) ∨
    (50 ≤ n ∧ n ≤ 500 ∧ 1/10 ≤ fourRowFiniteParameter 50 n ∧ fourRowFiniteParameter 50 n ≤ 1) := by
  by_cases h : n ≤ 50
  · exact Or.inl ⟨hn.1, h, fourRowFiniteParameter_five ⟨hn.1, h⟩⟩
  · exact Or.inr ⟨by omega, hn.2, fourRowFiniteParameter_fifty ⟨by omega, hn.2⟩⟩

theorem fourRowFiniteDenominator_factor_pos {a u : ℝ} (ha : 5 ≤ a)
    (hu1 : u ≤ 1) (q : Fin 3) :
    0 < 1 - ((q : ℕ) + 1 : ℝ) * u / a := by
  have hq : (q : ℝ) + 1 ≤ 3 := by exact_mod_cast (show (q : ℕ) + 1 ≤ 3 by omega)
  have hq0 : 0 ≤ (q : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hu1 hq0
  have hdiv : ((q : ℕ) + 1 : ℝ) * u / a < 1 :=
    (div_lt_one (by linarith : 0 < a)).mpr (by nlinarith only [hq, hmul, ha])
  linarith

theorem fourRowFiniteDenominator_pos {a u : ℝ} (ha : 5 ≤ a)
    (hu1 : u ≤ 1) : 0 < fourRowFiniteDenominator a u :=
  Finset.prod_pos (fun q _ => fourRowFiniteDenominator_factor_pos ha hu1 q)

theorem fourRowFiniteClearingFactor_pos {a u : ℝ} (ha : 5 ≤ a)
    (hu : 0 < u) (hu1 : u ≤ 1) : 0 < u * fourRowFiniteDenominator a u :=
  mul_pos hu (fourRowFiniteDenominator_pos ha hu1)

/-- Exact cancellation of each possible ordinary-column denominator. -/
theorem fourRowFiniteDenominator_cancel {a u : ℝ} (ha : 5 ≤ a)
    (hu : 0 < u) (hu1 : u ≤ 1) (q : Fin 3) :
    fourRowFiniteDenominator a u / (a/u - ((q : ℕ) + 1 : ℝ)) =
      (u/a) * ∏ s ∈ (Finset.univ : Finset (Fin 3)).erase q,
        (1 - ((s : ℕ) + 1 : ℝ) * u/a) := by
  have ha0 : a ≠ 0 := ne_of_gt (by linarith : 0 < a)
  have hu0 : u ≠ 0 := hu.ne'
  have hf := fourRowFiniteDenominator_factor_pos ha hu1 q
  have hden : a/u - ((q : ℕ) + 1 : ℝ) ≠ 0 := by
    have hid : a/u - ((q : ℕ) + 1 : ℝ) =
        (a/u) * (1 - ((q : ℕ) + 1 : ℝ) * u/a) := by field_simp
    rw [hid]
    exact mul_ne_zero (div_ne_zero ha0 hu0) hf.ne'
  have hfrac : (1 - ((q : ℕ) + 1 : ℝ) * u/a) /
      (a/u - ((q : ℕ) + 1 : ℝ)) = u/a := by
    apply (div_eq_iff hden).mpr
    field_simp
  rw [fourRowFiniteDenominator, ← Finset.prod_erase_mul _ _ (Finset.mem_univ q),
    mul_div_assoc, hfrac]
  ring

/-- At the actual integer column parameter, the formal dimension a/u is N. -/
theorem fourRowFiniteParameter_dimension {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    (a : ℝ) / fourRowFiniteParameter a n = n := by
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold fourRowFiniteParameter
  field_simp

theorem fourRowFiniteClearingFactor_at_columns {a n : ℕ} (ha : 5 ≤ a)
    (han : a ≤ n) (hna : n ≤ 10*a) :
    0 < fourRowFiniteParameter a n *
      fourRowFiniteDenominator a (fourRowFiniteParameter a n) := by
  obtain ⟨hu, hu1⟩ := fourRowFiniteParameter_interval (by omega : 0 < a) han hna
  exact fourRowFiniteClearingFactor_pos (by exact_mod_cast ha) (by linarith) hu1

/-- Ordinary columns remain a positive finite class for each literal multiplier width. -/
theorem fourRowFinite_ordinary_count {n : ℕ} (hn : 5 ≤ n) (q : Fin 3) :
    0 < n - ((q : ℕ) + 1) ∧
      ((n - ((q : ℕ) + 1) : ℕ) : ℝ) = (n : ℝ) - ((q : ℕ) + 1 : ℝ) := by
  constructor
  · omega
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_sub (R := ℝ) (show (q : ℕ) + 1 ≤ n by omega))

end DittertRybin
