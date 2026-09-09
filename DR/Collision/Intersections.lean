import DR.Collision.FirstMoment
import Mathlib.Logic.Equiv.Prod

/-!
# Deleting a constrained sample from two collision witnesses

Distinct witnesses contain two different equality pairs on at least one
axis. On that axis a sample can be removed outside the other axis's
retained pair, leaving a row collision and a column collision. If the
removed sample was the common index of two pairs, equality of their other
indices follows by transitivity. Thus the argument includes overlapping
pairs without enumerating board labels or imposing positive support.

Exact summation over the deleted coordinate then gives
`Pr(E ∩ F) ≤ η (1 - separationProbability P k)` for any nonnegative `η`
bounding every row and column marginal. The concluding Bonferroni corollary
bounds the full first collision sum by `(1 + C η)` times failure probability.
These theorems require no lower bound on sample order or board dimensions.
-/

namespace DittertRybin

open scoped BigOperators

/-- The equality imposed by one sample-index pair on a label function. -/
def PairEqual {k : ℕ} {α : Type*} (r : SampleIndexPair k) (f : Fin k → α) : Prop :=
  f r.val.1 = f r.val.2

theorem pairEqual_sorted {k : ℕ} {α : Type*} (i j : Fin k) (hij : i ≠ j)
    (f : Fin k → α) : PairEqual (sortedIndexPair i j hij) f ↔ f i = f j := by
  by_cases h : i < j <;> simp [PairEqual, sortedIndexPair, h, eq_comm]

/-- The other endpoint of a pair containing the specified index. -/
def pairPartner {k : ℕ} (r : SampleIndexPair k) (t : Fin k) : Fin k :=
  if t = r.val.1 then r.val.2 else r.val.1

theorem pairPartner_ne {k : ℕ} (r : SampleIndexPair k) (t : Fin k)
    (ht : PairContains r t) : t ≠ pairPartner r t := by
  have hr := ne_of_lt r.property
  rcases ht with rfl | rfl <;> simp [pairPartner, hr, hr.symm]

theorem sorted_pairPartner {k : ℕ} (r : SampleIndexPair k) (t : Fin k)
    (ht : PairContains r t) : sortedIndexPair t (pairPartner r t) (pairPartner_ne r t ht) = r := by
  have hr := ne_of_lt r.property
  rcases ht with rfl | rfl
  · simp [pairPartner, sortedIndexPair, r.property]
  · simp [pairPartner, hr.symm, sortedIndexPair, not_lt_of_gt r.property]

theorem pairEqual_partner {k : ℕ} {α : Type*} (r : SampleIndexPair k) (t : Fin k)
    (ht : PairContains r t) (f : Fin k → α) (hf : PairEqual r f) :
    f t = f (pairPartner r t) := by
  have h := (pairEqual_sorted t (pairPartner r t) (pairPartner_ne r t ht) f)
  rw [sorted_pairPartner r t ht] at h
  exact h.mp hf

/-- Two different pairs have an endpoint outside any prescribed pair. -/
theorem exists_index_outside_pair {k : ℕ} (r r' c : SampleIndexPair k) (hne : r ≠ r') :
    ∃ t, (PairContains r t ∨ PairContains r' t) ∧ ¬ PairContains c t := by
  classical
  by_contra hn
  have hsub (t : Fin k) (ht : PairContains r t ∨ PairContains r' t) : PairContains c t := by
    by_contra hc
    exact hn ⟨t, ht, hc⟩
  have hr : r = c := (sampleIndexPair_eq_iff r c).mpr
    ⟨hsub _ (Or.inl (Or.inl rfl)), hsub _ (Or.inl (Or.inr rfl))⟩
  have hr' : r' = c := (sampleIndexPair_eq_iff r' c).mpr
    ⟨hsub _ (Or.inr (Or.inl rfl)), hsub _ (Or.inr (Or.inr rfl))⟩
  exact hne (hr.trans hr'.symm)

/-- Removing any sample from two distinct equality pairs leaves a collision.
If the sample belonged to both pairs, the two other endpoints are equal.
-/
theorem surviving_pair_after_delete {k : ℕ} {α : Type*} (r r' : SampleIndexPair k)
    (hne : r ≠ r') (t : Fin k) :
    ∃ e : SampleIndexPair k, ¬ PairContains e t ∧
      ∀ f : Fin k → α, PairEqual r f → PairEqual r' f → PairEqual e f := by
  classical
  by_cases ht : PairContains r t
  · by_cases ht' : PairContains r' t
    · let u := pairPartner r t
      let v := pairPartner r' t
      have htu : t ≠ u := pairPartner_ne r t ht
      have htv : t ≠ v := pairPartner_ne r' t ht'
      have huv : u ≠ v := by
        intro heq
        have hr := sorted_pairPartner r t ht
        have hr' := sorted_pairPartner r' t ht'
        change sortedIndexPair t u htu = r at hr
        change sortedIndexPair t v htv = r' at hr'
        have hs : sortedIndexPair t u htu = sortedIndexPair t v htv := by
          congr 1
        exact hne (hr.symm.trans (hs.trans hr'))
      refine ⟨sortedIndexPair u v huv, ?_, ?_⟩
      · rw [pairContains_sorted]
        exact not_or.mpr ⟨htu, htv⟩
      · intro f hr hr'
        apply (pairEqual_sorted u v huv f).mpr
        exact (pairEqual_partner r t ht f hr).symm.trans (pairEqual_partner r' t ht' f hr')
    · exact ⟨r', ht', fun _ _ hr' ↦ hr'⟩
  · exact ⟨r, ht, fun _ hr _ ↦ hr⟩

/-- A removable equality factor and a surviving collision outside a prescribed pair. -/
theorem collision_pair_deletion {k : ℕ} {α : Type*} (r r' c : SampleIndexPair k)
    (hne : r ≠ r') :
    ∃ (t u : Fin k) (e : SampleIndexPair k),
      t ≠ u ∧ ¬ PairContains c t ∧ ¬ PairContains e t ∧
      ∀ f : Fin k → α, PairEqual r f → PairEqual r' f →
        f t = f u ∧ PairEqual e f := by
  obtain ⟨t, ht, hc⟩ := exists_index_outside_pair r r' c hne
  obtain ⟨e, he, hsurvive⟩ := surviving_pair_after_delete (α := α) r r' hne t
  rcases ht with ht | ht
  · refine ⟨t, pairPartner r t, e, pairPartner_ne r t ht, hc, he, ?_⟩
    intro f hr hr'
    exact ⟨pairEqual_partner r t ht f hr, hsurvive f hr hr'⟩
  · refine ⟨t, pairPartner r' t, e, pairPartner_ne r' t ht, hc, he, ?_⟩
    intro f hr hr'
    exact ⟨pairEqual_partner r' t ht f hr', hsurvive f hr hr'⟩

open Classical in
/-- Sum out one sample coordinate, retaining its exact conditional fiber mass. -/
theorem eventMass_coordinate_fibers {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (t : Fin k)
    (E : α → ({j : Fin k // j ≠ t} → α) → Prop) :
    eventMass p {s : Fin k → α | E (s t) (fun j ↦ s j.val)} =
      ∑ q : {j : Fin k // j ≠ t} → α, (∏ j, p (q j)) *
        ∑ a, if E a q then p a else 0 := by
  classical
  unfold eventMass
  calc
    _ = ∑ aq : α × ({j : Fin k // j ≠ t} → α),
        (∏ j, p (aq.2 j)) * (if E aq.1 aq.2 then p aq.1 else 0) := by
      apply Fintype.sum_equiv (Equiv.funSplitAt t α)
      intro s
      have hprod := Fintype.prod_eq_mul_prod_subtype_ne (fun j ↦ p (s j)) t
      change (if E (s t) (fun j ↦ s j.val) then sampleMass p s else 0) =
        (∏ j : {j : Fin k // j ≠ t}, p (s j.val)) *
          (if E (s t) (fun j ↦ s j.val) then p (s t) else 0)
      by_cases he : E (s t) (fun j ↦ s j.val)
      · simpa only [he, if_true, sampleMass, mul_comm] using hprod
      · simp [he]
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [← Finset.mul_sum]

open Classical in
/-- An event omitting a sample coordinate has its reduced product-weight sum. -/
theorem eventMass_without_coordinate {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (hp : ∑ a, p a = 1) (t : Fin k)
    (B : ({j : Fin k // j ≠ t} → α) → Prop) :
    eventMass p {s : Fin k → α | B (fun j ↦ s j.val)} =
      ∑ q : {j : Fin k // j ≠ t} → α, if B q then ∏ j, p (q j) else 0 := by
  classical
  rw [eventMass_coordinate_fibers p t (fun _ q ↦ B q)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hb : B q <;> simp [hb, hp]

open Classical in
/-- A uniform conditional fiber bound may be multiplied by any event that
does not use the integrated coordinate. -/
theorem eventMass_fiber_le {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (t : Fin k) (B : ({j : Fin k // j ≠ t} → α) → Prop)
    (C : α → ({j : Fin k // j ≠ t} → α) → Prop) (η : ℝ)
    (hC : ∀ q, (∑ a, if C a q then p a else 0) ≤ η) :
    eventMass p {s : Fin k → α | B (fun j ↦ s j.val) ∧ C (s t) (fun j ↦ s j.val)} ≤
      η * eventMass p {s : Fin k → α | B (fun j ↦ s j.val)} := by
  classical
  rw [eventMass_coordinate_fibers p t (fun a q ↦ B q ∧ C a q),
    eventMass_without_coordinate p hpsum t B, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  by_cases hb : B q
  · simp only [hb, true_and, if_true]
    have hprod : 0 ≤ ∏ j, p (q j) := Finset.prod_nonneg fun _ _ ↦ hp _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hC q) hprod
  · simp [hb]

open Classical in
/-- A witness avoiding `t` can be multiplied by a bounded label-equality
factor involving sample `t` and any other sample `u`. -/
theorem collisionEvent_label_match_le {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    {β : Type*} (g : (Fin m × Fin n) → β) (η : ℝ)
    (hg : ∀ b, (∑ a : Fin m × Fin n, if g a = b then P a.1 a.2 else 0) ≤ η)
    (z : CollisionWitness k) (t u : Fin k) (htu : t ≠ u)
    (hzr : ¬ PairContains z.1 t) (hzc : ¬ PairContains z.2 t) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent z s ∧ g (s t) = g (s u)} ≤
        η * eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
          {s : Fin k → Fin m × Fin n | CollisionEvent z s} := by
  have hr0 : z.1.val.1 ≠ t := fun h ↦ hzr (Or.inl h.symm)
  have hr1 : z.1.val.2 ≠ t := fun h ↦ hzr (Or.inr h.symm)
  have hc0 : z.2.val.1 ≠ t := fun h ↦ hzc (Or.inl h.symm)
  have hc1 : z.2.val.2 ≠ t := fun h ↦ hzc (Or.inr h.symm)
  let B : ({j : Fin k // j ≠ t} → Fin m × Fin n) → Prop := fun q ↦
    (q ⟨z.1.val.1, hr0⟩).1 = (q ⟨z.1.val.2, hr1⟩).1 ∧
      (q ⟨z.2.val.1, hc0⟩).2 = (q ⟨z.2.val.2, hc1⟩).2
  exact eventMass_fiber_le (fun a : Fin m × Fin n ↦ P a.1 a.2)
    (fun a ↦ hP.1 a.1 a.2) ((sum_cell_weights P).trans hP.2) t B
    (fun a q ↦ g a = g (q ⟨u, htu.symm⟩)) η (fun q ↦ hg _)

theorem collisionEvent_mass_le_failure {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (z : CollisionWitness k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent z s} ≤ 1 - separationProbability P k := by
  rw [← collision_union_mass hP]
  apply eventMass_mono (fun a : Fin m × Fin n ↦ P a.1 a.2) (fun a ↦ hP.1 a.1 a.2)
  intro s hs
  exact ⟨z, hs⟩

/-- Distinct simultaneous-collision witnesses have intersection mass at most
`η` times the full failure probability, whenever `η` bounds all marginals.

The proof derives the removable sample combinatorially and integrates its
row or column equality exactly. The remaining event still witnesses failure.
No stationarity, balanced marginals, or positive-support hypothesis is used.
-/
theorem collision_intersection_le {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (η : ℝ) (hη : 0 ≤ η) (hr : ∀ i, rowSum P i ≤ η) (hc : ∀ j, colSum P j ≤ η)
    (w v : CollisionWitness k) (hwv : w ≠ v) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent w s ∧ CollisionEvent v s} ≤
        η * (1 - separationProbability P k) := by
  classical
  by_cases hrow : w.1 = v.1
  · have hcol : w.2 ≠ v.2 := fun h ↦ hwv (Prod.ext hrow h)
    obtain ⟨t, u, e, htu, htrow, hte, hd⟩ :=
      collision_pair_deletion (α := Fin n) w.2 v.2 w.1 hcol
    let z : CollisionWitness k := (w.1, e)
    have hsubset : {s : Fin k → Fin m × Fin n | CollisionEvent w s ∧ CollisionEvent v s} ⊆
        {s : Fin k → Fin m × Fin n | CollisionEvent z s ∧ (s t).2 = (s u).2} := by
      intro s hs
      obtain ⟨htie, hsurvive⟩ := hd (fun j ↦ (s j).2) hs.1.2 hs.2.2
      exact ⟨⟨hs.1.1, hsurvive⟩, htie⟩
    have hbound : ∀ b : Fin n,
        (∑ a : Fin m × Fin n, if a.2 = b then P a.1 a.2 else 0) ≤ η := by
      intro b
      have hb := sum_col_eq_weight P b
      rw [show (∑ a : Fin m × Fin n, if a.2 = b then P a.1 a.2 else 0) = colSum P b by
        simpa only [eq_comm] using hb]
      exact hc b
    exact (eventMass_mono _ (fun a ↦ hP.1 a.1 a.2) hsubset).trans
      ((collisionEvent_label_match_le hP Prod.snd η (by
          intro b
          convert hbound b using 1
          apply Finset.sum_congr rfl
          intro a _
          by_cases he : a.2 = b <;> simp [he]) z t u htu htrow hte).trans
        (mul_le_mul_of_nonneg_left (collisionEvent_mass_le_failure hP z) hη))
  · obtain ⟨t, u, e, htu, htcol, hte, hd⟩ :=
      collision_pair_deletion (α := Fin m) w.1 v.1 w.2 hrow
    let z : CollisionWitness k := (e, w.2)
    have hsubset : {s : Fin k → Fin m × Fin n | CollisionEvent w s ∧ CollisionEvent v s} ⊆
        {s : Fin k → Fin m × Fin n | CollisionEvent z s ∧ (s t).1 = (s u).1} := by
      intro s hs
      obtain ⟨htie, hsurvive⟩ := hd (fun j ↦ (s j).1) hs.1.1 hs.2.1
      exact ⟨⟨hsurvive, hs.1.2⟩, htie⟩
    have hbound : ∀ b : Fin m,
        (∑ a : Fin m × Fin n, if a.1 = b then P a.1 a.2 else 0) ≤ η := by
      intro b
      have hb := sum_row_eq_weight P b
      rw [show (∑ a : Fin m × Fin n, if a.1 = b then P a.1 a.2 else 0) = rowSum P b by
        simpa only [eq_comm] using hb]
      exact hr b
    exact (eventMass_mono _ (fun a ↦ hP.1 a.1 a.2) hsubset).trans
      ((collisionEvent_label_match_le hP Prod.fst η (by
          intro b
          convert hbound b using 1
          apply Finset.sum_congr rfl
          intro a _
          by_cases he : a.1 = b <;> simp [he]) z t u htu hte htcol).trans
        (mul_le_mul_of_nonneg_left (collisionEvent_mass_le_failure hP z) hη))

/-- The first collision sum is controlled by the full failure probability. -/
theorem collisionFirstSum_le_failure {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (η : ℝ) (hη : 0 ≤ η) (hr : ∀ i, rowSum P i ≤ η) (hc : ∀ j, colSum P j ≤ η) :
    collisionFirstSum P k ≤
      (1 + (((k.choose 2) ^ 2).choose 2 : ℝ) * η) * (1 - separationProbability P k) :=
  collisionFirstSum_le_of_intersections hP η (collision_intersection_le hP η hη hr hc)

end DittertRybin
