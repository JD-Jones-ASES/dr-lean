import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Finite weighted unions and the second Bonferroni inequality

These elementary inequalities are the probability input to the collision
concentration argument. The sample weights only need to be nonnegative;
normalization to total weight one is not required. Intersections are summed
over ordered distinct event pairs, so the second-order correction has a
factor of one half.
-/

namespace DittertRybin.FiniteEvents

open scoped BigOperators

variable {α ι : Type*}

/-- The real-valued indicator of a proposition. -/
noncomputable def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

/-- The total weight of an event on a finite sample space. -/
noncomputable def mass (Ω : Finset α) (w : α → ℝ) (E : α → Prop) : ℝ :=
  ∑ x ∈ Ω, w x * indicator (E x)

@[simp] theorem indicator_true : indicator True = 1 := by
  simp [indicator]

@[simp] theorem indicator_false : indicator False = 0 := by
  simp [indicator]

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  classical
  simp only [indicator]
  split_ifs <;> norm_num

theorem mass_nonneg (Ω : Finset α) (w : α → ℝ) (E : α → Prop)
    (hw : ∀ x ∈ Ω, 0 ≤ w x) : 0 ≤ mass Ω w E := by
  exact Finset.sum_nonneg fun x hx ↦ mul_nonneg (hw x hx) (indicator_nonneg _)

/-- The number of events that occur is the sum of their indicators. -/
theorem sum_indicators (I : Finset ι) (E : ι → Prop) [DecidablePred E] :
    (∑ i ∈ I, indicator (E i)) = ((I.filter E).card : ℝ) := by
  rw [← Finset.sum_boole (R := ℝ) E I]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : E i <;> simp [indicator, hi]

/-- Distinct ordered pairs of occurring events number `n² - n`. -/
theorem sum_intersection_indicators (I : Finset ι) (E : ι → Prop) [DecidablePred E] :
    (∑ ij ∈ I.offDiag, indicator (E ij.1 ∧ E ij.2)) =
      ((I.filter E).card : ℝ) ^ 2 - (I.filter E).card := by
  classical
  have hfilter : I.offDiag.filter (fun ij ↦ E ij.1 ∧ E ij.2) =
      (I.filter E).offDiag := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    tauto
  rw [show (∑ ij ∈ I.offDiag, indicator (E ij.1 ∧ E ij.2)) =
      ((I.offDiag.filter (fun ij ↦ E ij.1 ∧ E ij.2)).card : ℝ) from
    sum_indicators I.offDiag (fun ij ↦ E ij.1 ∧ E ij.2)]
  rw [hfilter, Finset.offDiag_card]
  rw [Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  ring

/-- Pointwise union bound, before applying sample weights. -/
theorem indicator_union_le_sum (I : Finset ι) (E : ι → Prop) :
    indicator (∃ i ∈ I, E i) ≤ ∑ i ∈ I, indicator (E i) := by
  classical
  by_cases h : ∃ i ∈ I, E i
  · obtain ⟨i, hi, hEi⟩ := h
    have hc : 1 ≤ (I.filter E).card :=
      Finset.one_le_card.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hEi⟩⟩
    rw [sum_indicators]
    simpa [indicator, show ∃ i ∈ I, E i from ⟨i, hi, hEi⟩] using
      (show (1 : ℝ) ≤ ((I.filter E).card : ℝ) by exact_mod_cast hc)
  · simp only [indicator, if_neg h]
    exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

/-- Pointwise second Bonferroni bound, expressed without probability. -/
theorem sum_le_indicator_union_add_pairs (I : Finset ι) (E : ι → Prop) :
    (∑ i ∈ I, indicator (E i)) ≤ indicator (∃ i ∈ I, E i) +
      (∑ ij ∈ I.offDiag, indicator (E ij.1 ∧ E ij.2)) / 2 := by
  classical
  rw [sum_indicators, sum_intersection_indicators]
  by_cases h : ∃ i ∈ I, E i
  · obtain ⟨i, hi, hEi⟩ := h
    have hc : 1 ≤ (I.filter E).card :=
      Finset.one_le_card.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hEi⟩⟩
    simp only [indicator, if_pos (show ∃ i ∈ I, E i from ⟨i, hi, hEi⟩)]
    by_cases h1 : (I.filter E).card = 1
    · norm_num [h1]
    · have h2 : 2 ≤ (I.filter E).card := by omega
      have hr : (2 : ℝ) ≤ ((I.filter E).card : ℝ) := by exact_mod_cast h2
      have hp := mul_nonneg (show 0 ≤ ((I.filter E).card : ℝ) - 1 by linarith)
        (show 0 ≤ ((I.filter E).card : ℝ) - 2 by linarith)
      nlinarith
  · have he : I.filter E = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact h ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    simp [indicator, h, he]

/-- Union bound for a finite space with nonnegative real weights. -/
theorem union_bound (Ω : Finset α) (I : Finset ι) (w : α → ℝ)
    (E : ι → α → Prop) (hw : ∀ x ∈ Ω, 0 ≤ w x) :
    mass Ω w (fun x ↦ ∃ i ∈ I, E i x) ≤ ∑ i ∈ I, mass Ω w (E i) := by
  unfold mass
  calc
    _ ≤ ∑ x ∈ Ω, w x * ∑ i ∈ I, indicator (E i x) :=
      Finset.sum_le_sum fun x hx ↦
        mul_le_mul_of_nonneg_left (indicator_union_le_sum I (fun i ↦ E i x)) (hw x hx)
    _ = _ := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm

/-- The second Bonferroni inequality for arbitrary nonnegative finite weights. -/
theorem second_bonferroni (Ω : Finset α) (I : Finset ι) (w : α → ℝ)
    (E : ι → α → Prop) (hw : ∀ x ∈ Ω, 0 ≤ w x) :
    (∑ i ∈ I, mass Ω w (E i)) ≤ mass Ω w (fun x ↦ ∃ i ∈ I, E i x) +
      (∑ ij ∈ I.offDiag, mass Ω w (fun x ↦ E ij.1 x ∧ E ij.2 x)) / 2 := by
  have h := Finset.sum_le_sum (s := Ω) fun x hx ↦
    mul_le_mul_of_nonneg_left (sum_le_indicator_union_add_pairs I (fun i ↦ E i x))
      (hw x hx)
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_div] at h
  simp only [← mul_div_assoc, ← Finset.sum_div] at h
  have hleft : (∑ x ∈ Ω, ∑ i ∈ I, w x * indicator (E i x)) =
      ∑ i ∈ I, mass Ω w (E i) := Finset.sum_comm
  have hright : (∑ x ∈ Ω, ∑ ij ∈ I.offDiag,
      w x * indicator (E ij.1 x ∧ E ij.2 x)) =
      ∑ ij ∈ I.offDiag, mass Ω w (fun x ↦ E ij.1 x ∧ E ij.2 x) := Finset.sum_comm
  rw [hleft, hright] at h
  exact h

/-- A uniform bound on distinct event intersections controls the collision sum.

If every pair intersection has weight at most `η` times the union weight,
then the sum of single-event weights is at most the union weight multiplied
by `1 + C η`, where `C` is half the number of ordered distinct event pairs.
-/
theorem collision_sum_le_of_intersections (Ω : Finset α) (I : Finset ι)
    (w : α → ℝ) (E : ι → α → Prop) (η : ℝ)
    (hw : ∀ x ∈ Ω, 0 ≤ w x)
    (hpair : ∀ ij ∈ I.offDiag, mass Ω w (fun x ↦ E ij.1 x ∧ E ij.2 x) ≤
      η * mass Ω w (fun x ↦ ∃ i ∈ I, E i x)) :
    (∑ i ∈ I, mass Ω w (E i)) ≤
      (1 + (I.offDiag.card : ℝ) / 2 * η) *
        mass Ω w (fun x ↦ ∃ i ∈ I, E i x) := by
  have hsum := Finset.sum_le_sum hpair
  have hb := second_bonferroni Ω I w E hw
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

/-- The collision-sum bound with the usual unordered-pair coefficient. -/
theorem collision_sum_le (Ω : Finset α) (I : Finset ι)
    (w : α → ℝ) (E : ι → α → Prop) (η : ℝ)
    (hw : ∀ x ∈ Ω, 0 ≤ w x)
    (hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      mass Ω w (fun x ↦ E i x ∧ E j x) ≤
        η * mass Ω w (fun x ↦ ∃ i ∈ I, E i x)) :
    (∑ i ∈ I, mass Ω w (E i)) ≤
      (1 + (I.card.choose 2 : ℝ) * η) *
        mass Ω w (fun x ↦ ∃ i ∈ I, E i x) := by
  have hc : (I.offDiag.card : ℝ) / 2 = (I.card.choose 2 : ℝ) := by
    rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul,
      Nat.cast_choose_two]
    ring
  rw [← hc]
  exact collision_sum_le_of_intersections Ω I w E η hw fun ij hij ↦
    hpair ij.1 (Finset.mem_offDiag.mp hij).1 ij.2
      (Finset.mem_offDiag.mp hij).2.1 (Finset.mem_offDiag.mp hij).2.2

/-- The scalar quadratic bootstrap used to concentrate contenders. -/
theorem lt_add_one_of_sq_le (κ x : ℝ) (hx : 0 ≤ x)
    (h : x ^ 2 ≤ κ * (1 + x)) : x < κ + 1 := by
  by_contra hn
  have hge : κ + 1 ≤ x := le_of_not_gt hn
  have hp := mul_nonneg hx (sub_nonneg.mpr hge)
  nlinarith

/-- Collision and marginal inequalities force strict quantitative concentration.

In the matrix application `ζ = MN ‖P-U‖²`, `η` is the largest marginal,
`d = min(M,N)`, and `κ` is the collision-pair coefficient. This theorem is
only the scalar bootstrap; the application must prove its two hypotheses.
-/
theorem concentration_bootstrap (d κ ζ η : ℝ) (hd : 0 < d) (hκ : 0 ≤ κ)
    (hζ : 0 ≤ ζ) (hcollision : ζ ≤ κ * η)
    (hmarginal : η ≤ 1 / d + Real.sqrt (ζ / d)) :
    ζ < (κ + 1) ^ 2 / d ∧ η < (κ + 2) / d := by
  let x := d * Real.sqrt (ζ / d)
  have hx : 0 ≤ x := mul_nonneg hd.le (Real.sqrt_nonneg _)
  have hxsq : x ^ 2 = d * ζ := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt (div_nonneg hζ hd.le)]
    field_simp
  have hbound : x ^ 2 ≤ κ * (1 + x) := by
    rw [hxsq]
    have h := mul_le_mul_of_nonneg_left
      (hcollision.trans (mul_le_mul_of_nonneg_left hmarginal hκ)) hd.le
    dsimp [x]
    field_simp at h ⊢
    nlinarith
  have hxlt := lt_add_one_of_sq_le κ x hx hbound
  constructor
  · apply (lt_div_iff₀ hd).mpr
    have hp := mul_pos (show 0 < κ + 1 - x by linarith)
      (show 0 < κ + 1 + x by linarith)
    nlinarith [hxsq]
  · apply (lt_div_iff₀ hd).mpr
    have h := mul_le_mul_of_nonneg_left hmarginal hd.le
    dsimp [x] at hxlt
    field_simp at h
    nlinarith

end DittertRybin.FiniteEvents
