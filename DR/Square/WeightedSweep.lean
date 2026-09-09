import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A finite weighted spectral sweep

The energy uses one half of the ordered double sum. A cut boundary sums
each crossing edge once. Sorting scores and summing squared adjacent gaps,
together with weighted Popoviciu, gives the finite `(N-1)/4` sweep factor.
No connectedness or positive-energy hypothesis is imposed.
-/

namespace DittertRybin

open scoped BigOperators

def sweepMean {α : Type*} [Fintype α] (π f : α → ℝ) : ℝ := ∑ v, π v * f v

def sweepVariance {α : Type*} [Fintype α] (π f : α → ℝ) : ℝ :=
  ∑ v, π v * (f v - sweepMean π f) ^ 2

noncomputable def sweepEnergy {α : Type*} [Fintype α] (c : α → α → ℝ) (f : α → ℝ) : ℝ :=
  (1 / 2) * ∑ v, ∑ w, c v w * (f v - f w) ^ 2

def sweepMass {α : Type*} (π : α → ℝ) (S : Finset α) : ℝ := ∑ v ∈ S, π v

def sweepBoundary {α : Type*} [Fintype α] [DecidableEq α]
    (c : α → α → ℝ) (S : Finset α) : ℝ := ∑ v ∈ S, ∑ w ∈ Sᶜ, c v w

theorem sweepVariance_eq_second_moment {α : Type*} [Fintype α]
    (π f : α → ℝ) (hπ : ∑ v, π v = 1) :
    sweepVariance π f = (∑ v, π v * f v ^ 2) - sweepMean π f ^ 2 := by
  let μ := sweepMean π f
  have hpoint (v : α) : π v * (f v - μ) ^ 2 =
      π v * f v ^ 2 - 2 * μ * (π v * f v) + μ ^ 2 * π v := by ring
  change (∑ v, π v * (f v - μ) ^ 2) = _
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hπ, mul_one]
  change _ - 2 * μ * μ + μ ^ 2 = _ - μ ^ 2
  ring

/-- Weighted Popoviciu on a closed interval; zero weights and tied scores are allowed. -/
theorem sweepVariance_le_range_sq {α : Type*} [Fintype α]
    (π f : α → ℝ) (hπ0 : ∀ v, 0 ≤ π v) (hπ : ∑ v, π v = 1)
    (a b : ℝ) (hlo : ∀ v, a ≤ f v) (hhi : ∀ v, f v ≤ b) :
    sweepVariance π f ≤ (b - a) ^ 2 / 4 := by
  have hprod : 0 ≤ ∑ v, π v * (f v - a) * (b - f v) :=
    Finset.sum_nonneg fun v _ => mul_nonneg (mul_nonneg (hπ0 v) (sub_nonneg.mpr (hlo v)))
      (sub_nonneg.mpr (hhi v))
  have hpoint (v : α) : π v * (f v - a) * (b - f v) =
      (a + b) * (π v * f v) - π v * f v ^ 2 - (a * b) * π v := by ring
  simp_rw [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ, mul_one] at hprod
  rw [sweepVariance_eq_second_moment π f hπ]
  change 0 ≤ (a + b) * sweepMean π f - (∑ v, π v * f v ^ 2) - a * b at hprod
  nlinarith [sq_nonneg (2 * sweepMean π f - a - b)]

def sweepGap {n : ℕ} (f : Fin (n + 1) → ℝ) (t : Fin n) : ℝ :=
  f t.succ - f t.castSucc

def sweepPrefix {n : ℕ} (t : Fin n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => i.val ≤ t.val)

theorem sweepGap_nonneg {n : ℕ} (f : Fin (n + 1) → ℝ) (hf : Monotone f) (t : Fin n) :
    0 ≤ sweepGap f t := sub_nonneg.mpr (hf (by change t.val ≤ t.val + 1; omega))

/-- Every prefix of the gap sequence telescopes, including empty prefixes. -/
theorem sum_sweepGap_prefix {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (∑ t : Fin n, if t.val < i.val then sweepGap f t else 0) = f i - f 0 := by
  classical
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    have hpoint (t : Fin n) : (if t.val < i.succ.val then sweepGap f t else 0) =
        (if t.val < i.castSucc.val then sweepGap f t else 0) +
          (if t = i then sweepGap f t else 0) := by
      by_cases hti : t = i
      · subst t
        simp
      · have hne : t.val ≠ i.val := fun h => hti (Fin.ext h)
        by_cases hlt : t.val < i.val
        · simp [hlt, hti, show t.val < i.val + 1 by omega]
        · simp [hlt, hti, show ¬ t.val < i.val + 1 by omega]
    simp_rw [hpoint, Finset.sum_add_distrib]
    rw [hi]
    simp [sweepGap]

theorem sum_sweepGap {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∑ t, sweepGap f t) = f (Fin.last n) - f 0 := by
  simpa using sum_sweepGap_prefix f (Fin.last n)

/-- The score difference is the sum of exactly the crossed gaps. -/
theorem sum_sweepGap_interval {n : ℕ} (f : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (∑ t : Fin n, if i.val ≤ t.val ∧ t.val < j.val then sweepGap f t else 0) = f j - f i := by
  have hpoint (t : Fin n) :
      (if i.val ≤ t.val ∧ t.val < j.val then sweepGap f t else 0) =
        (if t.val < j.val then sweepGap f t else 0) -
          (if t.val < i.val then sweepGap f t else 0) := by
    by_cases hti : t.val < i.val
    · have htj : t.val < j.val := lt_of_lt_of_le hti hij
      have hn : ¬ i.val ≤ t.val := by omega
      simp [hti, htj, hn]
    · have hit : i.val ≤ t.val := by omega
      by_cases htj : t.val < j.val <;> simp [hti, htj, hit]
  simp_rw [hpoint, Finset.sum_sub_distrib, sum_sweepGap_prefix]
  ring

theorem sum_sweepGap_sq_interval_le {n : ℕ} (f : Fin (n + 1) → ℝ) (hf : Monotone f)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (∑ t : Fin n, if i.val ≤ t.val ∧ t.val < j.val then sweepGap f t ^ 2 else 0) ≤
      (f j - f i) ^ 2 := by
  classical
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun t : Fin n => if i.val ≤ t.val ∧ t.val < j.val then sweepGap f t else 0)
    (by
      intro t _
      by_cases h : i.val ≤ t.val ∧ t.val < j.val
      · simpa only [if_pos h] using sweepGap_nonneg f hf t
      · simp [h])
  simpa only [ite_pow, zero_pow (by decide : 2 ≠ 0), sum_sweepGap_interval f i j hij] using h

theorem sweepBoundary_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α]
    (c : α → α → ℝ) (S : Finset α) :
    sweepBoundary c S = ∑ v, ∑ w, if v ∈ S ∧ w ∉ S then c v w else 0 := by
  classical
  unfold sweepBoundary
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter]
  congr 1
  ext w
  simp

theorem sweepBoundary_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (c : α → α → ℝ) (hc : ∀ v w, 0 ≤ c v w) (S : Finset α) : 0 ≤ sweepBoundary c S :=
  Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => hc v w

theorem sweepBoundary_compl {α : Type*} [Fintype α] [DecidableEq α]
    (c : α → α → ℝ) (hc : ∀ v w, c v w = c w v) (S : Finset α) :
    sweepBoundary c Sᶜ = sweepBoundary c S := by
  classical
  rw [sweepBoundary_eq_sum_ite, sweepBoundary_eq_sum_ite, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;> simp [hv, hw, hc]

theorem sweepMass_compl {α : Type*} [Fintype α] [DecidableEq α]
    (π : α → ℝ) (hπ : ∑ v, π v = 1) (S : Finset α) : sweepMass π Sᶜ = 1 - sweepMass π S := by
  have h := Finset.sum_add_sum_compl S π
  rw [hπ] at h
  unfold sweepMass
  linarith

theorem sweepPrefix_nonempty {n : ℕ} (t : Fin n) : (sweepPrefix t).Nonempty :=
  ⟨0, by simp [sweepPrefix]⟩

theorem sweepPrefix_ne_univ {n : ℕ} (t : Fin n) : sweepPrefix t ≠ Finset.univ := by
  intro h
  have hm : Fin.last n ∈ sweepPrefix t := h ▸ Finset.mem_univ _
  simp [sweepPrefix, Nat.not_le.mpr t.isLt] at hm

theorem sweepBoundary_prefix {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (t : Fin n) :
    sweepBoundary c (sweepPrefix t) =
      ∑ i, ∑ j, if i.val ≤ t.val ∧ t.val < j.val then c i j else 0 := by
  simp [sweepBoundary_eq_sum_ite, sweepPrefix, not_le]

/-- Symmetric energy is the sum over increasing endpoint pairs, so every edge is counted once. -/
theorem sweepEnergy_eq_upper {N : ℕ} (c : Fin N → Fin N → ℝ)
    (hc : ∀ i j, c i j = c j i) (f : Fin N → ℝ) :
    sweepEnergy c f = ∑ i, ∑ j, if i < j then c i j * (f i - f j) ^ 2 else 0 := by
  classical
  let F := fun i j => c i j * (f i - f j) ^ 2
  have hsym (i j : Fin N) : F i j = F j i := by
    dsimp [F]
    rw [hc i j]
    ring
  have hpoint (i j : Fin N) : F i j = (if i < j then F i j else 0) +
      (if j < i then F i j else 0) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt.mpr hij.le]
    · simp [F]
    · simp [hji, not_lt.mpr hji.le]
  have hrev : (∑ i, ∑ j, if j < i then F i j else 0) =
      ∑ i, ∑ j, if i < j then F i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have htotal : (∑ i, ∑ j, F i j) =
      2 * ∑ i, ∑ j, if i < j then F i j else 0 := by
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [hpoint i j]
    simp only [Finset.sum_add_distrib]
    rw [hrev]
    ring
  change (1 / 2) * (∑ i, ∑ j, F i j) = _
  rw [htotal]
  ring

/-- Edge differences dominate all the squared gaps they cross. -/
theorem sweep_prefix_gap_energy_le {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc0 : ∀ i j, 0 ≤ c i j) (hcsym : ∀ i j, c i j = c j i)
    (f : Fin (n + 1) → ℝ) (hf : Monotone f) :
    (∑ t, sweepBoundary c (sweepPrefix t) * sweepGap f t ^ 2) ≤ sweepEnergy c f := by
  classical
  have hsum : (∑ t, sweepBoundary c (sweepPrefix t) * sweepGap f t ^ 2) =
      ∑ i, ∑ j, c i j * ∑ t : Fin n,
        if i.val ≤ t.val ∧ t.val < j.val then sweepGap f t ^ 2 else 0 := by
    simp_rw [sweepBoundary_prefix, Finset.sum_mul]
    calc
      _ = ∑ i, ∑ t : Fin n, ∑ j,
          (if i.val ≤ t.val ∧ t.val < j.val then c i j else 0) * sweepGap f t ^ 2 :=
        Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ t : Fin n,
          (if i.val ≤ t.val ∧ t.val < j.val then c i j else 0) * sweepGap f t ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> simp
  rw [hsum, sweepEnergy_eq_upper c hcsym f]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i < j
  · rw [if_pos hij]
    have h := mul_le_mul_of_nonneg_left (sum_sweepGap_sq_interval_le f hf i j hij.le) (hc0 i j)
    convert h using 1
    ring
  · rw [if_neg hij]
    have hnone (t : Fin n) : ¬ (i.val ≤ t.val ∧ t.val < j.val) := by
      intro h
      exact hij (by change i.val < j.val; omega)
    simp [hnone]

/-- Weighted variance is controlled by the total squared adjacent gap on a sorted path. -/
theorem sweep_variance_gap_bound {n : ℕ} (π f : Fin (n + 1) → ℝ)
    (hπ0 : ∀ v, 0 ≤ π v) (hπ : ∑ v, π v = 1) (hf : Monotone f) :
    4 * sweepVariance π f ≤ (n : ℝ) * ∑ t, sweepGap f t ^ 2 := by
  have hpop := sweepVariance_le_range_sq π f hπ0 hπ (f 0) (f (Fin.last n))
    (fun v => hf (Fin.zero_le v)) (fun v => hf (Fin.le_last v))
  have hgap := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := sweepGap f)
  rw [sum_sweepGap] at hgap
  simp only [Finset.card_univ, Fintype.card_fin] at hgap
  linarith

/-- A minimizing sorted prefix has the claimed boundary bound, even when the energy is zero. -/
theorem exists_sweep_prefix {n : ℕ} (hn : 0 < n)
    (π f : Fin (n + 1) → ℝ) (hπ0 : ∀ v, 0 ≤ π v) (hπ : ∑ v, π v = 1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hcsym : ∀ i j, c i j = c j i) (hf : Monotone f) (hV : 0 < sweepVariance π f) :
    ∃ t : Fin n, sweepBoundary c (sweepPrefix t) ≤
      (n : ℝ) * sweepEnergy c f / (4 * sweepVariance π f) := by
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun t => sweepBoundary c (sweepPrefix t)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨t, ?_⟩
  let b := sweepBoundary c (sweepPrefix t)
  have hb : 0 ≤ b := sweepBoundary_nonneg c hc0 _
  have hD : b * (∑ u, sweepGap f u ^ 2) ≤ sweepEnergy c f := by
    calc
      _ = ∑ u, b * sweepGap f u ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ u, sweepBoundary c (sweepPrefix u) * sweepGap f u ^ 2 :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (ht u (Finset.mem_univ _)) (sq_nonneg _)
      _ ≤ _ := sweep_prefix_gap_energy_le c hc0 hcsym f hf
  apply (le_div_iff₀ (by positivity : 0 < 4 * sweepVariance π f)).mpr
  calc
    _ ≤ b * ((n : ℝ) * ∑ u, sweepGap f u ^ 2) :=
      mul_le_mul_of_nonneg_left (sweep_variance_gap_bound π f hπ0 hπ hf) hb
    _ = (n : ℝ) * (b * ∑ u, sweepGap f u ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)

theorem sweepMean_permute {α : Type*} [Fintype α] (π f : α → ℝ) (σ : Equiv.Perm α) :
    sweepMean (π ∘ σ) (f ∘ σ) = sweepMean π f := Equiv.sum_comp σ (fun v => π v * f v)

theorem sweepVariance_permute {α : Type*} [Fintype α] (π f : α → ℝ) (σ : Equiv.Perm α) :
    sweepVariance (π ∘ σ) (f ∘ σ) = sweepVariance π f := by
  unfold sweepVariance
  rw [sweepMean_permute]
  exact Equiv.sum_comp σ (fun v => π v * (f v - sweepMean π f) ^ 2)

theorem sweepEnergy_permute {α : Type*} [Fintype α] (c : α → α → ℝ)
    (f : α → ℝ) (σ : Equiv.Perm α) :
    sweepEnergy (fun i j => c (σ i) (σ j)) (f ∘ σ) = sweepEnergy c f := by
  unfold sweepEnergy
  congr 1
  apply Fintype.sum_equiv σ
  intro i
  exact Equiv.sum_comp σ (fun j => c (σ i) j * (f (σ i) - f j) ^ 2)

theorem sweepMass_permute {α : Type*} (π : α → ℝ) (σ : Equiv.Perm α) (S : Finset α) :
    sweepMass π (S.map σ.toEmbedding) = sweepMass (π ∘ σ) S := by
  simp [sweepMass]

theorem sweepBoundary_permute {α : Type*} [Fintype α] [DecidableEq α]
    (c : α → α → ℝ) (σ : Equiv.Perm α) (S : Finset α) :
    sweepBoundary (fun i j => c (σ i) (σ j)) S = sweepBoundary c (S.map σ.toEmbedding) := by
  classical
  rw [sweepBoundary_eq_sum_ite, sweepBoundary_eq_sum_ite]
  apply Fintype.sum_equiv σ
  intro i
  apply Fintype.sum_equiv σ
  intro j
  simp

theorem sweepMass_pos {α : Type*} (π : α → ℝ) (hπ : ∀ v, 0 < π v)
    (S : Finset α) (hS : S.Nonempty) : 0 < sweepMass π S :=
  Finset.sum_pos (fun v _ => hπ v) hS

/-- Complementing a proper cut preserves its boundary and makes its mass at most one half. -/
theorem exists_balanced_sweep_cut {α : Type*} [Fintype α] [DecidableEq α]
    (π : α → ℝ) (hπ : ∑ v, π v = 1) (c : α → α → ℝ) (hc : ∀ v w, c v w = c w v)
    (S : Finset α) (hS : S.Nonempty) (hproper : S ≠ Finset.univ) (B : ℝ)
    (hbound : sweepBoundary c S ≤ B) :
    ∃ T : Finset α, T.Nonempty ∧ T ≠ Finset.univ ∧ sweepMass π T ≤ 1 / 2 ∧ sweepBoundary c T ≤ B := by
  by_cases hmass : sweepMass π S ≤ 1 / 2
  · exact ⟨S, hS, hproper, hmass, hbound⟩
  · refine ⟨Sᶜ, ?_, (Finset.compl_ne_univ_iff_nonempty S).mpr hS, ?_, ?_⟩
    · apply Finset.nonempty_iff_ne_empty.mpr
      intro hEmpty
      exact hproper ((Finset.compl_eq_empty_iff S).mp hEmpty)
    · rw [sweepMass_compl π hπ]
      linarith
    · simpa only [sweepBoundary_compl c hc S] using hbound

/-- The finite weighted sweep inequality, with all score ties and disconnected conductances included. -/
theorem exists_weighted_sweep_cut {N : ℕ} (hN : 2 ≤ N)
    (π : Fin N → ℝ) (hπpos : ∀ v, 0 < π v) (hπ : ∑ v, π v = 1)
    (c : Fin N → Fin N → ℝ) (hc0 : ∀ v w, 0 ≤ c v w) (hcsym : ∀ v w, c v w = c w v)
    (f : Fin N → ℝ) (hV : 0 < sweepVariance π f) :
    ∃ S : Finset (Fin N), S.Nonempty ∧ S ≠ Finset.univ ∧ sweepMass π S ≤ 1 / 2 ∧
      sweepBoundary c S ≤ ((N - 1 : ℕ) : ℝ) * sweepEnergy c f / (4 * sweepVariance π f) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  let σ := Tuple.sort f
  have hπsum : ∑ v, (π ∘ σ) v = 1 := (Equiv.sum_comp σ π).trans hπ
  have hVsort : 0 < sweepVariance (π ∘ σ) (f ∘ σ) := by rwa [sweepVariance_permute]
  obtain ⟨t, ht⟩ := exists_sweep_prefix (by omega : 0 < n) (π ∘ σ) (f ∘ σ)
    (fun v => (hπpos (σ v)).le) hπsum (fun i j => c (σ i) (σ j))
    (fun i j => hc0 (σ i) (σ j)) (fun i j => hcsym (σ i) (σ j))
    (Tuple.monotone_sort f) hVsort
  let S := (sweepPrefix t).map σ.toEmbedding
  have hS : S.Nonempty := Finset.map_nonempty.mpr (sweepPrefix_nonempty t)
  have hproper : S ≠ Finset.univ := by
    intro h
    apply sweepPrefix_ne_univ t
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi : σ i ∈ S := h ▸ Finset.mem_univ _
    simpa [S] using hi
  have hbound : sweepBoundary c S ≤ (n : ℝ) * sweepEnergy c f / (4 * sweepVariance π f) := by
    simpa only [sweepBoundary_permute, sweepEnergy_permute, sweepVariance_permute] using ht
  exact exists_balanced_sweep_cut π hπ c hcsym S hS hproper _ hbound

end DittertRybin
