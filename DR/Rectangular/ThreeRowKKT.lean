import DR.Square.OrderThree
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Full-simplex first-order conditions for actual independent sampling

These finite formulas allow repeated sampled cells and do not remove zero cells
from the optimization domain. The derivative and Euler identities hold for every
sample order and arbitrary signed weights.
-/

namespace DittertRybin
open scoped BigOperators Topology
open Filter Set

/-- Actual global optimality on the complete closed matrix probability simplex. -/
def IsSeparationGlobalMax {m n : ℕ} (P : Board m n) (k : ℕ) : Prop :=
  ∀ Q : Board m n, IsProbability Q → separationProbability Q k ≤ separationProbability P k

/-- A formal cell derivative of a single ordered sample, including repetitions. -/
noncomputable def sampleMassGradient {α : Type*} [DecidableEq α] {k : ℕ}
    (p : α → ℝ) (s : Fin k → α) (a : α) : ℝ :=
  ∑ t, if s t = a then ∏ u ∈ Finset.univ.erase t, p (s u) else 0

/-- The exact gradient of the finite event polynomial. -/
noncomputable def eventMassGradient {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (p : α → ℝ) (E : Set (Fin k → α)) (a : α) : ℝ := by
  classical
  exact ∑ s, if s ∈ E then sampleMassGradient p s a else 0

/-- The gradient of the actual inclusive-OR separation probability. -/
noncomputable def separationGradient {m n : ℕ} (P : Board m n) (k : ℕ)
    (i : Fin m) (j : Fin n) : ℝ :=
  eventMassGradient (fun a : Fin m × Fin n => P a.1 a.2)
    {s : Fin k → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s} (i, j)

theorem sampleMassGradient_dot {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (p D : α → ℝ) (s : Fin k → α) :
    (∑ a, sampleMassGradient p s a * D a) =
      ∑ t, D (s t) * ∏ u ∈ Finset.univ.erase t, p (s u) := by
  classical
  simp only [sampleMassGradient, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [mul_comm]

theorem hasDerivAt_sampleMass_line {α : Type*} {k : ℕ}
    (p D : α → ℝ) (s : Fin k → α) :
    HasDerivAt (fun t : ℝ => sampleMass (fun a => p a + D a * t) s)
      (∑ t, D (s t) * ∏ u ∈ Finset.univ.erase t, p (s u)) 0 := by
  have hh (i : Fin k) (_hi : i ∈ (Finset.univ : Finset (Fin k))) :
      HasDerivAt (fun t : ℝ => p (s i) + D (s i) * t) (D (s i)) 0 := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (D (s i))).const_add (p (s i))
  simpa [sampleMass, smul_eq_mul, mul_comm] using HasDerivAt.fun_finsetProd hh

theorem hasDerivAt_eventMass_line {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (p D : α → ℝ) (E : Set (Fin k → α)) :
    HasDerivAt (fun t : ℝ => eventMass (fun a => p a + D a * t) E)
      (∑ a, eventMassGradient p E a * D a) 0 := by
  classical
  have hdot : (∑ a, eventMassGradient p E a * D a) =
      ∑ s, if s ∈ E then ∑ t, D (s t) * ∏ u ∈ Finset.univ.erase t, p (s u) else 0 := by
    simp only [eventMassGradient, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s ∈ E
    · simpa only [if_pos hs] using sampleMassGradient_dot p D s
    · simp only [if_neg hs, Finset.sum_const_zero]
  rw [hdot]
  unfold eventMass
  apply HasDerivAt.fun_sum
  intro s _
  by_cases hs : s ∈ E
  · simpa only [if_pos hs] using hasDerivAt_sampleMass_line p D s
  · simp only [if_neg hs]
    exact hasDerivAt_const _ _

theorem hasDerivAt_separationProbability_line {m n : ℕ} (P D : Board m n) (k : ℕ) :
    HasDerivAt (fun t : ℝ => separationProbability (fun i j => P i j + D i j * t) k)
      (∑ i, ∑ j, separationGradient P k i j * D i j) 0 := by
  simpa only [separationProbability, separationGradient, Fintype.sum_prod_type] using
    hasDerivAt_eventMass_line (fun a : Fin m × Fin n => P a.1 a.2)
      (fun a : Fin m × Fin n => D a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s}

theorem hasDerivAt_separationProbability_cellTransfer {m n : ℕ} (P : Board m n)
    (k : ℕ) (u v : Fin m × Fin n) :
    HasDerivAt (fun t : ℝ => separationProbability
      (fun i j => P i j + cellTransferDirection u v i j * t) k)
      (separationGradient P k u.1 u.2 - separationGradient P k v.1 v.2) 0 := by
  have h := hasDerivAt_separationProbability_line P (cellTransferDirection u v) k
  rcases u with ⟨ui, uj⟩
  rcases v with ⟨vi, vj⟩
  simpa [cellTransferDirection, mul_sub, Finset.sum_sub_distrib, Prod.mk.injEq, ite_and] using h

theorem separation_deriv_nonpos_of_right_max {f : ℝ → ℝ} {d ε : ℝ}
    (hε : 0 < ε) (hd : HasDerivAt f d 0) (hmax : ∀ t, 0 < t → t < ε → f t ≤ f 0) :
    d ≤ 0 := by
  have hlim := hd.tendsto_slope_zero_right
  apply le_of_tendsto hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hte
  simpa [div_eq_mul_inv, mul_comm] using div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hmax t ht hte)) ht.le

/-- Missing target cells are included; only the donor is required to be positive. -/
theorem IsSeparationGlobalMax.gradient_le {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P)
    (u v : Fin m × Fin n) (hv : 0 < P v.1 v.2) :
    separationGradient P k u.1 u.2 ≤ separationGradient P k v.1 v.2 := by
  have h := separation_deriv_nonpos_of_right_max hv
    (hasDerivAt_separationProbability_cellTransfer P k u v) (by
      intro t ht htv
      obtain ⟨hpos, hmass⟩ := cellTransfer_feasible hP.1 u v ht.le htv.le
      have h := hmax _ ⟨hpos, hmass.trans hP.2⟩
      simpa using h)
  linarith

theorem IsSeparationGlobalMax.gradient_eq {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P)
    (u v : Fin m × Fin n) (hu : 0 < P u.1 u.2) (hv : 0 < P v.1 v.2) :
    separationGradient P k u.1 u.2 = separationGradient P k v.1 v.2 :=
  le_antisymm (hmax.gradient_le hP u v hv) (hmax.gradient_le hP v u hu)

/-- Homogeneity is exact even when some or all sample weights vanish. -/
theorem sampleMassGradient_euler {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (p : α → ℝ) (s : Fin k → α) :
    (∑ a, sampleMassGradient p s a * p a) = (k : ℝ) * sampleMass p s := by
  rw [sampleMassGradient_dot]
  have hterm (t : Fin k) : p (s t) * (∏ u ∈ Finset.univ.erase t, p (s u)) =
      sampleMass p s := by
    exact Finset.mul_prod_erase Finset.univ (fun u => p (s u)) (Finset.mem_univ t)
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem eventMassGradient_euler {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (p : α → ℝ) (E : Set (Fin k → α)) :
    (∑ a, eventMassGradient p E a * p a) = (k : ℝ) * eventMass p E := by
  classical
  simp only [eventMassGradient, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ E
  · simpa only [if_pos hs] using sampleMassGradient_euler p s
  · simp only [if_neg hs, Finset.sum_const_zero, mul_zero]

theorem separationGradient_euler {m n : ℕ} (P : Board m n) (k : ℕ) :
    (∑ i, ∑ j, separationGradient P k i j * P i j) =
      (k : ℝ) * separationProbability P k := by
  simpa only [separationGradient, separationProbability, Fintype.sum_prod_type] using
    eventMassGradient_euler (fun a : Fin m × Fin n => P a.1 a.2)
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s}

/-- The common support gradient is fixed by Euler's identity and total mass one. -/
theorem IsSeparationGlobalMax.gradient_eq_value {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P)
    (v : Fin m × Fin n) (hv : 0 < P v.1 v.2) :
    separationGradient P k v.1 v.2 = (k : ℝ) * separationProbability P k := by
  have hterm (i : Fin m) (j : Fin n) :
      separationGradient P k i j * P i j = separationGradient P k v.1 v.2 * P i j := by
    by_cases hij : 0 < P i j
    · rw [hmax.gradient_eq hP (i, j) v hij hv]
    · have hz : P i j = 0 := le_antisymm (le_of_not_gt hij) (hP.1 i j)
      rw [hz, mul_zero, mul_zero]
  have heuler := separationGradient_euler P k
  simp only [hterm, ← Finset.mul_sum] at heuler
  change separationGradient P k v.1 v.2 * totalMass P = _ at heuler
  simpa only [hP.2, mul_one] using heuler

/-- All cells, including zeros, satisfy the full KKT inequality. -/
theorem IsSeparationGlobalMax.gradient_le_value {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P)
    (u : Fin m × Fin n) :
    separationGradient P k u.1 u.2 ≤ (k : ℝ) * separationProbability P k := by
  have hex : ∃ v : Fin m × Fin n, 0 < P v.1 v.2 := by
    by_contra h
    push Not at h
    have hz : ∀ i j, P i j = 0 := fun i j => le_antisymm (h (i, j)) (hP.1 i j)
    have hmass := hP.2
    simp [totalMass, rowSum, hz] at hmass
  obtain ⟨v, hv⟩ := hex
  exact (hmax.gradient_le hP u v hv).trans_eq (hmax.gradient_eq_value hP v hv)

end DittertRybin
