import DR.Collision.OccupationBounds
import DR.Collision.Intersections
import DR.Collision.Concentration

/-!
# Collision bounds for the actual conditional occupation law

The estimates here use the iid sample measure, not a hypothesized occupation
law. A pair of distinct sample indices always has an endpoint outside any
fixed coordinate. Integrating that endpoint bounds a label collision even
after restricting the fixed coordinate. Thus all row-cylinder estimates
include zero-mass rows without dividing by their mass.
-/

namespace DittertRybin

open scoped BigOperators

open Classical in
theorem eventMass_coordinate {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (hp : ∑ a, p a = 1) (t : Fin k) (C : α → Prop) :
    eventMass p {s : Fin k → α | C (s t)} = ∑ a, if C a then p a else 0 := by
  rw [eventMass_coordinate_fibers p t (fun a _ => C a), ← Finset.sum_mul,
    sum_prod_weights_eq_one p hp, one_mul]

theorem eventMass_exists_le_sum {α ι : Type*} [Fintype α] [Fintype ι] {k : ℕ}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (E : ι → (Fin k → α) → Prop) :
    eventMass p {s : Fin k → α | ∃ i, E i s} ≤
      ∑ i, eventMass p {s : Fin k → α | E i s} := by
  classical
  simp_rw [eventMass_eq_finiteMass]
  simpa only [Finset.mem_univ, true_and, Set.mem_ofPred_eq] using
    FiniteEvents.union_bound Finset.univ Finset.univ (sampleMass p) E
      (fun s _ => sampleMass_nonneg p hp s)

theorem exists_pairEqual_iff_not_injective {α : Type*} {k : ℕ} (f : Fin k → α) :
    (∃ r : SampleIndexPair k, PairEqual r f) ↔ ¬ Function.Injective f := by
  constructor
  · rintro ⟨r, hr⟩ hi
    exact (ne_of_lt r.property) (hi hr)
  · intro hn
    obtain ⟨u, v, he, hne⟩ := Function.not_injective_iff.mp hn
    exact ⟨sortedIndexPair u v hne, (pairEqual_sorted u v hne f).mpr he⟩

open Classical in
/-- A label equality costs at most the largest label mass after any cylinder restriction. -/
theorem eventMass_pair_cylinder_le {α β : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (g : α → β) (ξ : ℝ) (hg : ∀ b, (∑ a, if g a = b then p a else 0) ≤ ξ)
    (t : Fin k) (C : α → Prop) (r : SampleIndexPair k) :
    eventMass p {s : Fin k → α | C (s t) ∧ PairEqual r (g ∘ s)} ≤
      ξ * eventMass p {s : Fin k → α | C (s t)} := by
  classical
  have huv : r.val.1 ≠ r.val.2 := ne_of_lt r.property
  by_cases ht : r.val.1 = t
  · have htv : t ≠ r.val.2 := ht ▸ huv
    have h := eventMass_fiber_le p hp hsum r.val.2
      (fun q => C (q ⟨t, htv⟩))
      (fun a q => g a = g (q ⟨r.val.1, huv⟩)) ξ (fun q => hg _)
    simpa only [PairEqual, Function.comp_apply, eq_comm] using h
  · have h := eventMass_fiber_le p hp hsum r.val.1
      (fun q => C (q ⟨t, Ne.symm ht⟩))
      (fun a q => g a = g (q ⟨r.val.2, huv.symm⟩)) ξ (fun q => hg _)
    exact h

open Classical in
theorem eventMass_noninjective_cylinder_le {α β : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (g : α → β) (ξ : ℝ) (hg : ∀ b, (∑ a, if g a = b then p a else 0) ≤ ξ)
    (t : Fin k) (C : α → Prop) :
    eventMass p {s : Fin k → α | C (s t) ∧ ¬ Function.Injective (g ∘ s)} ≤
      (k.choose 2 : ℝ) * ξ * eventMass p {s : Fin k → α | C (s t)} := by
  classical
  have he : {s : Fin k → α | C (s t) ∧ ¬ Function.Injective (g ∘ s)} =
      {s : Fin k → α | ∃ r : SampleIndexPair k, C (s t) ∧ PairEqual r (g ∘ s)} := by
    ext s
    simp only [Set.mem_ofPred_eq, ← exists_pairEqual_iff_not_injective]
    exact exists_and_left.symm
  rw [he]
  calc
    _ ≤ ∑ r : SampleIndexPair k,
        eventMass p {s : Fin k → α | C (s t) ∧ PairEqual r (g ∘ s)} :=
      eventMass_exists_le_sum p hp _
    _ ≤ ∑ _r : SampleIndexPair k, ξ * eventMass p {s : Fin k → α | C (s t)} :=
      Finset.sum_le_sum fun r _ => eventMass_pair_cylinder_le p hp hsum g ξ hg t C r
    _ = _ := by simp [card_sampleIndexPair, mul_assoc]

open Classical in
/-- Unconditioned pair collision bound, valid even for an empty sample. -/
theorem eventMass_noninjective_le {α β : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (g : α → β) (ξ : ℝ) (hg : ∀ b, (∑ a, if g a = b then p a else 0) ≤ ξ) :
    eventMass p {s : Fin k → α | ¬ Function.Injective (g ∘ s)} ≤ (k.choose 2 : ℝ) * ξ := by
  classical
  by_cases hk : 0 < k
  · have h := eventMass_noninjective_cylinder_le p hp hsum g ξ hg ⟨0, hk⟩ (fun _ => True)
    simpa [eventMass_univ_eq_one p hsum] using h
  · have hk0 : k = 0 := by omega
    subst k
    have hi (s : Fin 0 → α) : Function.Injective (g ∘ s) := by intro i; exact Fin.elim0 i
    simp [eventMass, hi]

theorem eventMass_two_exclusions_lower {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (E F G : Set (Fin k → α)) :
    eventMass p E - eventMass p {s | s ∈ E ∧ s ∉ F} -
      eventMass p {s | s ∈ E ∧ s ∉ G} ≤ eventMass p {s | s ∈ E ∧ s ∈ F ∧ s ∈ G} := by
  classical
  unfold eventMass
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro s _
  have hs := sampleMass_nonneg p hp s
  by_cases he : s ∈ E <;> by_cases hf : s ∈ F <;> by_cases hg : s ∈ G <;>
    simp_all

open Classical in
theorem row_label_mass_le {m n : ℕ} (P : Board m n) (ξ : ℝ)
    (hr : ∀ i, rowSum P i ≤ ξ) (i : Fin m) :
    (∑ a : Fin m × Fin n, @ite ℝ (a.1 = i) (Classical.propDecidable _) (P a.1 a.2) 0) ≤ ξ := by
  simpa only [eq_comm] using (sum_row_eq_weight P i).trans_le (hr i)

open Classical in
theorem col_label_mass_le {m n : ℕ} (P : Board m n) (ξ : ℝ)
    (hc : ∀ j, colSum P j ≤ ξ) (j : Fin n) :
    (∑ a : Fin m × Fin n, @ite ℝ (a.2 = j) (Classical.propDecidable _) (P a.1 a.2) 0) ≤ ξ := by
  simpa only [eq_comm] using (sum_col_eq_weight P j).trans_le (hc j)

theorem row_cylinder_mass {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (t : Fin k) (i : Fin m) :
    eventMass (fun a : Fin m × Fin n => P a.1 a.2)
      {s : Fin k → Fin m × Fin n | (s t).1 = i} = rowSum P i := by
  classical
  rw [eventMass_coordinate _ ((sum_cell_weights P).trans hP.2) t (fun a => a.1 = i)]
  simpa only [eq_comm] using sum_row_eq_weight P i

theorem columnDistinctMass_bounds {m n : ℕ} {P : Board m n} (hP : IsProbability P)
    (k : ℕ) (ξ : ℝ) (hc : ∀ j, colSum P j ≤ ξ) :
    1 - (k.choose 2 : ℝ) * ξ ≤ columnDistinctMass P k ∧ columnDistinctMass P k ≤ 1 := by
  have h := eventMass_noninjective_le (k := k) (fun a : Fin m × Fin n => P a.1 a.2)
    (fun a => hP.1 a.1 a.2) ((sum_cell_weights P).trans hP.2) Prod.snd ξ
    (col_label_mass_le P ξ hc)
  have he : {s : Fin k → Fin m × Fin n | ¬ Function.Injective (Prod.snd ∘ s)} =
      {s : Fin k → Fin m × Fin n | ColsDistinct s}ᶜ := rfl
  rw [he, eventMass_compl _ ((sum_cell_weights P).trans hP.2)] at h
  constructor
  · change 1 - columnDistinctMass P k ≤ _ at h
    linarith
  · exact eventMass_le_one (fun a : Fin m × Fin n => P a.1 a.2) (fun a => hP.1 a.1 a.2) ((sum_cell_weights P).trans hP.2) _

theorem rows_cols_mass_lower {m n : ℕ} {P : Board m n} (hP : IsProbability P)
    (k : ℕ) (ξ : ℝ) (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ) :
    1 - 2 * (k.choose 2 : ℝ) * ξ ≤
      eventMass (fun a : Fin m × Fin n => P a.1 a.2)
        {s : Fin k → Fin m × Fin n | ColsDistinct s ∧ RowsDistinct s} := by
  let p := fun a : Fin m × Fin n => P a.1 a.2
  have hsum : ∑ a, p a = 1 := (sum_cell_weights P).trans hP.2
  have hpn : ∀ a, 0 ≤ p a := fun a => hP.1 a.1 a.2
  have hR := eventMass_noninjective_le (k := k) p hpn hsum Prod.fst ξ
    (row_label_mass_le P ξ hr)
  have hD := eventMass_noninjective_le (k := k) p hpn hsum Prod.snd ξ
    (col_label_mass_le P ξ hc)
  have h := eventMass_two_exclusions_lower p hpn Set.univ
    {s : Fin k → Fin m × Fin n | ColsDistinct s} {s | RowsDistinct s}
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, eventMass_univ_eq_one p hsum] at h
  change eventMass p {s : Fin k → Fin m × Fin n | ¬ RowsDistinct s} ≤ _ at hR
  change eventMass p {s : Fin k → Fin m × Fin n | ¬ ColsDistinct s} ≤ _ at hD
  linarith

theorem row_cylinder_rows_cols_bounds {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (ξ : ℝ) (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ)
    (t : Fin k) (i : Fin m) :
    rowSum P i * (1 - 2 * (k.choose 2 : ℝ) * ξ) ≤
      eventMass (fun a : Fin m × Fin n => P a.1 a.2)
        {s : Fin k → Fin m × Fin n | (s t).1 = i ∧ ColsDistinct s ∧ RowsDistinct s} ∧
    eventMass (fun a : Fin m × Fin n => P a.1 a.2)
        {s : Fin k → Fin m × Fin n | (s t).1 = i ∧ ColsDistinct s ∧ RowsDistinct s} ≤ rowSum P i := by
  let p := fun a : Fin m × Fin n => P a.1 a.2
  have hsum : ∑ a, p a = 1 := (sum_cell_weights P).trans hP.2
  have hpn : ∀ a, 0 ≤ p a := fun a => hP.1 a.1 a.2
  have hR := eventMass_noninjective_cylinder_le p hpn hsum Prod.fst ξ
    (row_label_mass_le P ξ hr) t (fun a => a.1 = i)
  have hD := eventMass_noninjective_cylinder_le p hpn hsum Prod.snd ξ
    (col_label_mass_le P ξ hc) t (fun a => a.1 = i)
  have h := eventMass_two_exclusions_lower p hpn {s | (s t).1 = i}
    {s : Fin k → Fin m × Fin n | ColsDistinct s} {s | RowsDistinct s}
  change eventMass p {s : Fin k → Fin m × Fin n | (s t).1 = i ∧ ¬ RowsDistinct s} ≤ _ at hR
  change eventMass p {s : Fin k → Fin m × Fin n | (s t).1 = i ∧ ¬ ColsDistinct s} ≤ _ at hD
  simp only [Set.mem_ofPred_eq] at h
  rw [row_cylinder_mass hP t i] at h hR hD
  constructor
  · nlinarith
  · calc
      _ ≤ eventMass p {s : Fin k → Fin m × Fin n | (s t).1 = i} :=
        eventMass_mono p hpn (fun _ hs => hs.1)
      _ = _ := row_cylinder_mass hP t i

open Classical in
/-- Distinctness makes the row-occupation indicator the sum of its coordinate indicators. -/
theorem rowOccupation_eq_sum_positions {m n k : ℕ} (s : Fin k → Fin m × Fin n) (i : Fin m) :
    rowOccupation s i = ∑ t, if RowsDistinct s ∧ (s t).1 = i then (1 : ℝ) else 0 := by
  classical
  by_cases hR : RowsDistinct s
  · by_cases hi : i ∈ occupiedRows s
    · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hi
      have he (u : Fin k) : (s u).1 = i ↔ u = t := by
        constructor
        · intro hu; exact hR (hu.trans ht.symm)
        · rintro rfl; exact ht
      simp [rowOccupation, hR, hi, he]
    · have he (t : Fin k) : (s t).1 ≠ i := by
        intro ht
        exact hi (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)
      simp [rowOccupation, hR, hi, he]
  · simp [rowOccupation, hR]

/-- The actual occupation numerator is a sum over all sampled positions, including k=0. -/
theorem occupationProbability_eq_sum_positions {m n : ℕ} (P : Board m n) (k : ℕ) (i : Fin m) :
    occupationProbability P k i =
      (∑ t : Fin k, eventMass (fun a : Fin m × Fin n => P a.1 a.2)
        {s : Fin k → Fin m × Fin n | (s t).1 = i ∧ ColsDistinct s ∧ RowsDistinct s}) /
          columnDistinctMass P k := by
  classical
  simp only [occupationProbability, columnConditionalExpectation, rowOccupation_eq_sum_positions,
    Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  unfold eventMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hD : ColsDistinct s <;> by_cases hR : RowsDistinct s <;> by_cases hi : (s t).1 = i <;>
    simp [columnConditionedWeight, hD, hR, hi]

theorem columnDistinctMass_pos_of_pair_bound {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (k : ℕ) (ξ : ℝ) (hc : ∀ j, colSum P j ≤ ξ)
    (hsmall : (k.choose 2 : ℝ) * ξ ≤ 1 / 2) : 0 < columnDistinctMass P k := by
  have h := (columnDistinctMass_bounds hP k ξ hc).1
  linarith

theorem conditionalRowsProbability_lower_of_pair_bound {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (k : ℕ) (ξ : ℝ)
    (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ)
    (hsmall : (k.choose 2 : ℝ) * ξ ≤ 1 / 2) :
    1 - 2 * (k.choose 2 : ℝ) * ξ ≤ conditionalRowsProbability P k := by
  have hZ := columnDistinctMass_pos_of_pair_bound hP k ξ hc hsmall
  have hZone := (columnDistinctMass_bounds hP k ξ hc).2
  have hJ := rows_cols_mass_lower hP k ξ hr hc
  rw [conditionalRowsProbability_eq_eventMass]
  calc
    _ ≤ _ := hJ
    _ ≤ _ := by
      apply (le_div_iff₀ hZ).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hZone
        (eventMass_nonneg _ (fun a : Fin m × Fin n => hP.1 a.1 a.2) _)

/-- Multiplicative occupation error, with no positive-row hypothesis. -/
theorem occupationProbability_deviation_le {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (k : ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ)
    (hsmall : (k.choose 2 : ℝ) * ξ ≤ 1 / 2) (i : Fin m) :
    |occupationProbability P k i - (k : ℝ) * rowSum P i| ≤
      2 * k * (k.choose 2 : ℝ) * ξ * rowSum P i := by
  let d : ℝ := (k.choose 2 : ℝ) * ξ
  let a : ℝ := (k : ℝ) * rowSum P i
  let N : ℝ := ∑ t : Fin k, eventMass (fun c : Fin m × Fin n => P c.1 c.2)
    {s : Fin k → Fin m × Fin n | (s t).1 = i ∧ ColsDistinct s ∧ RowsDistinct s}
  have hd : 0 ≤ d := mul_nonneg (Nat.cast_nonneg _) hξ
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (rowSum_nonneg hP.1 i)
  have hdsmall : d ≤ 1 / 2 := hsmall
  have hZ := columnDistinctMass_pos_of_pair_bound hP k ξ hc hsmall
  obtain ⟨hZlo, hZhi⟩ := columnDistinctMass_bounds hP k ξ hc
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun t _ =>
    eventMass_nonneg _ (fun c : Fin m × Fin n => hP.1 c.1 c.2) _
  have hNlo : a * (1 - 2 * d) ≤ N := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) fun t _ =>
      (row_cylinder_rows_cols_bounds hP ξ hr hc t i).1
    simpa [a, d, N, mul_assoc] using h
  have hNhi : N ≤ a := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) fun t _ =>
      (row_cylinder_rows_cols_bounds hP ξ hr hc t i).2
    simpa [a, N] using h
  have hq : occupationProbability P k i = N / columnDistinctMass P k :=
    occupationProbability_eq_sum_positions P k i
  have hNq : N ≤ occupationProbability P k i := by
    rw [hq]
    apply (le_div_iff₀ hZ).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hZhi hN0
  have hqupper : occupationProbability P k i ≤ a + 2 * a * d := by
    rw [hq]
    apply (div_le_iff₀ hZ).mpr
    calc
      N ≤ a := hNhi
      _ ≤ (a + 2 * a * d) * (1 - d) := by
        nlinarith [mul_nonneg (mul_nonneg ha hd) (show 0 ≤ 1 - 2 * d by linarith)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hZlo (by positivity)
  have herr : |occupationProbability P k i - a| ≤ 2 * a * d := by
    apply abs_le.mpr
    constructor <;> nlinarith
  simpa only [a, d, mul_assoc, mul_left_comm, mul_comm] using herr

theorem occupationProbability_le_twice_marginal {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (k : ℕ) (ξ : ℝ)
    (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ)
    (hsmall : (k.choose 2 : ℝ) * ξ ≤ 1 / 2) (i : Fin m) :
    occupationProbability P k i ≤ 2 * k * rowSum P i := by
  have hZ := columnDistinctMass_pos_of_pair_bound hP k ξ hc hsmall
  have hZhalf : (1 : ℝ) / 2 ≤ columnDistinctMass P k := by
    linarith [(columnDistinctMass_bounds hP k ξ hc).1]
  rw [occupationProbability_eq_sum_positions]
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ ∑ _t : Fin k, rowSum P i := Finset.sum_le_sum fun t _ =>
      (row_cylinder_rows_cols_bounds hP ξ hr hc t i).2
    _ = (2 * k * rowSum P i) * (1 / 2) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZhalf
      (mul_nonneg (by positivity) (rowSum_nonneg hP.1 i))

/-- Equations (8)--(9), under a dimension-free bound on pair-collision load. -/
theorem occupation_controls_of_pair_bound {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (k : ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ)
    (hsmall : (k.choose 2 : ℝ) * ξ ≤ 1 / 4) :
    0 < columnDistinctMass P k ∧
    (1 : ℝ) / 2 ≤ conditionalRowsProbability P k ∧
    (∀ i, occupationProbability P k i ≤ 2 * k * ξ) ∧
    (∀ i, |occupationProbability P k i - (k : ℝ) * rowSum P i| ≤
      2 * k * (k.choose 2 : ℝ) * ξ * rowSum P i) := by
  have hhalf : (k.choose 2 : ℝ) * ξ ≤ 1 / 2 := by linarith
  refine ⟨columnDistinctMass_pos_of_pair_bound hP k ξ hc hhalf, ?_, ?_, ?_⟩
  · linarith [conditionalRowsProbability_lower_of_pair_bound hP k ξ hr hc hhalf]
  · intro i
    exact (occupationProbability_le_twice_marginal hP k ξ hr hc hhalf i).trans
      (mul_le_mul_of_nonneg_left (hr i) (by positivity))
  · exact occupationProbability_deviation_le hP k ξ hξ hr hc hhalf

/-- A zero row has zero occupation in the actual conditional law, even if its normalizer vanishes. -/
theorem occupationProbability_eq_zero_of_rowSum_eq_zero {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (k : ℕ) (i : Fin m) (hi : rowSum P i = 0) :
    occupationProbability P k i = 0 := by
  rw [occupationProbability_eq_sum_positions]
  have hterm (t : Fin k) : eventMass (fun a : Fin m × Fin n => P a.1 a.2)
      {s : Fin k → Fin m × Fin n | (s t).1 = i ∧ ColsDistinct s ∧ RowsDistinct s} = 0 := by
    apply le_antisymm
    · calc
        _ ≤ eventMass (fun a : Fin m × Fin n => P a.1 a.2)
            {s : Fin k → Fin m × Fin n | (s t).1 = i} :=
          eventMass_mono (fun a : Fin m × Fin n => P a.1 a.2)
            (fun a => hP.1 a.1 a.2) (fun _ hs => hs.1)
        _ = 0 := (row_cylinder_mass hP t i).trans hi
    · exact eventMass_nonneg (fun a : Fin m × Fin n => P a.1 a.2) (fun a => hP.1 a.1 a.2) _
  simp_rw [hterm]
  simp

theorem pair_collision_load_small (k : ℕ) (hk : 2 ≤ k) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / (64 * (k : ℝ) ^ 3)) : (k.choose 2 : ℝ) * ξ ≤ 1 / 256 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hb : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  calc
    _ ≤ ((k : ℝ) ^ 2 / 2) * (1 / (64 * (k : ℝ) ^ 3)) :=
      mul_le_mul hb hξ hξ0 (by positivity)
    _ = 1 / (128 * k) := by field_simp; ring
    _ ≤ 1 / 256 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 128 * k) (by norm_num : (0 : ℝ) < 256)).mpr
      nlinarith

/-- The source marginal threshold supplies every occupation control used in the quadratic estimate. -/
theorem occupation_controls_of_marginals {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (k : ℕ) (hk : 2 ≤ k) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (hξ : ξ ≤ 1 / (64 * (k : ℝ) ^ 3))
    (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ) :
    0 < columnDistinctMass P k ∧
    (1 : ℝ) / 2 ≤ conditionalRowsProbability P k ∧
    (∀ i, occupationProbability P k i ≤ 2 * k * ξ) ∧
    (∀ i, |occupationProbability P k i - (k : ℝ) * rowSum P i| ≤
      2 * k * (k.choose 2 : ℝ) * ξ * rowSum P i) := by
  apply occupation_controls_of_pair_bound hP k ξ hξ0 hr hc
  linarith [pair_collision_load_small k hk ξ hξ0 hξ]

/-- The normalized avoidance kernel is uniformly positive from actual marginal and dispersion bounds. -/
theorem occupationKernel_rational_lower_of_marginals {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (k : ℕ) (hk : 2 ≤ k) (hP : IsProbability P)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / (64 * (k : ℝ) ^ 3))
    (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ)
    (hθ : rowDispersion P ≤ 1 / (32 * k)) (x : Fin m → ℝ) :
    (847 / 2048 : ℝ) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ h, x i * occupationKernel P k i h * x h := by
  obtain ⟨hZ, hq0, hq, herr⟩ := occupation_controls_of_marginals hP k hk ξ hξ0 hξ hr hc
  exact occupationKernel_rational_lower_of_control hm P k hk hP hZ ξ hξ0 hξ hθ hq0 hq herr x

theorem occupationKernel_two_fifths_of_marginals {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (k : ℕ) (hk : 2 ≤ k) (hP : IsProbability P)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / (64 * (k : ℝ) ^ 3))
    (hr : ∀ i, rowSum P i ≤ ξ) (hc : ∀ j, colSum P j ≤ ξ)
    (hθ : rowDispersion P ≤ 1 / (32 * k)) (x : Fin m → ℝ) :
    (2 / 5 : ℝ) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ h, x i * occupationKernel P k i h * x h := by
  obtain ⟨hZ, hq0, hq, herr⟩ := occupation_controls_of_marginals hP k hk ξ hξ0 hξ hr hc
  exact occupationKernel_two_fifths_of_control hm P k hk hP hZ ξ hξ0 hξ hθ hq0 hq herr x

/-- Positivity API in terms of the actual largest marginal; all conditional-law bounds are derived. -/
theorem columnDistinctMass_pos_of_small_marginal {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (k : ℕ) (hk : 2 ≤ k) (hP : IsProbability P)
    (hξ : peakMarginal P ≤ 1 / (64 * (k : ℝ) ^ 3)) :
    0 < columnDistinctMass P k := by
  apply columnDistinctMass_pos_of_pair_bound hP k (peakMarginal P) (colSum_le_peakMarginal P)
  linarith [pair_collision_load_small k hk (peakMarginal P) (peakMarginal_nonneg hm hP) hξ]

/-- Uniform positivity from the actual largest marginal and row dispersion. -/
theorem occupationKernel_two_fifths {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (k : ℕ) (hk : 2 ≤ k) (hP : IsProbability P)
    (hξ : peakMarginal P ≤ 1 / (64 * (k : ℝ) ^ 3))
    (hθ : rowDispersion P ≤ 1 / (32 * k)) (x : Fin m → ℝ) :
    (2 / 5 : ℝ) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ h, x i * occupationKernel P k i h * x h :=
  occupationKernel_two_fifths_of_marginals hm P k hk hP (peakMarginal P)
    (peakMarginal_nonneg hm hP) hξ (rowSum_le_peakMarginal P)
    (colSum_le_peakMarginal P) hθ x

end DittertRybin
