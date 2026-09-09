import DR.Collision.Bonferroni
import DR.Uniform
import Mathlib.Data.Fintype.Prod

/-!
# Witnesses for simultaneous row and column collision

A witness consists of an unordered pair of sample indices whose rows agree
and an unordered pair whose columns agree. We represent each unordered pair
by its unique increasing ordering. The two pairs may coincide, overlap, or
be disjoint. Their union is exactly failure of the inclusive-OR separation
event, and there are `(k.choose 2)^2` witnesses.
-/

namespace DittertRybin

open scoped BigOperators

/-- An unordered pair of different sample indices, in increasing order. -/
abbrev SampleIndexPair (k : ℕ) := {ij : Fin k × Fin k // ij.1 < ij.2}

/-- One pair requiring row equality and one pair requiring column equality. -/
abbrev CollisionWitness (k : ℕ) := SampleIndexPair k × SampleIndexPair k

theorem card_sampleIndexPair (k : ℕ) :
    Fintype.card (SampleIndexPair k) = k.choose 2 := by
  simpa [Fintype.card_subtype] using
    (Fintype.card_product_filter_lt (α := Fin k))

theorem card_collisionWitness (k : ℕ) :
    Fintype.card (CollisionWitness k) = (k.choose 2) ^ 2 := by
  rw [Fintype.card_prod, card_sampleIndexPair, pow_two]

/-- The actual equality constraints imposed by a collision witness. -/
def CollisionEvent {m n k : ℕ} (w : CollisionWitness k)
    (s : Fin k → Fin m × Fin n) : Prop :=
  (s w.1.val.1).1 = (s w.1.val.2).1 ∧
    (s w.2.val.1).2 = (s w.2.val.2).2

private theorem exists_sampleIndexPair_iff {k : ℕ} {α : Type*} (f : Fin k → α) :
    (∃ ij : SampleIndexPair k, f ij.val.1 = f ij.val.2) ↔ ¬ Function.Injective f := by
  constructor
  · rintro ⟨ij, heq⟩ hinj
    exact (ne_of_lt ij.property) (hinj heq)
  · intro h
    obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp h
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨⟨(i, j), hij⟩, heq⟩
    · exact ⟨⟨(j, i), hji⟩, heq.symm⟩

/-- Every failure has a witness, and every witness certifies failure. -/
theorem exists_collisionWitness_iff {m n k : ℕ} (s : Fin k → Fin m × Fin n) :
    (∃ w : CollisionWitness k, CollisionEvent w s) ↔
      ¬ (RowsDistinct s ∨ ColsDistinct s) := by
  constructor
  · rintro ⟨⟨r, c⟩, hr, hc⟩
    apply not_or.mpr
    exact ⟨(exists_sampleIndexPair_iff (fun t ↦ (s t).1)).mp ⟨r, hr⟩,
      (exists_sampleIndexPair_iff (fun t ↦ (s t).2)).mp ⟨c, hc⟩⟩
  · intro h
    obtain ⟨hr, hc⟩ := not_or.mp h
    obtain ⟨r, hreq⟩ := (exists_sampleIndexPair_iff (fun t ↦ (s t).1)).mpr hr
    obtain ⟨c, hceq⟩ := (exists_sampleIndexPair_iff (fun t ↦ (s t).2)).mpr hc
    exact ⟨(r, c), hreq, hceq⟩

/-- Connect independent-sample event mass to the generic finite-weight API. -/
theorem eventMass_eq_finiteMass {α : Type*} [Fintype α] {k : ℕ}
    (p : α → ℝ) (E : Set (Fin k → α)) :
    eventMass p E = FiniteEvents.mass Finset.univ (sampleMass p) (fun s ↦ s ∈ E) := by
  classical
  unfold eventMass FiniteEvents.mass
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : s ∈ E <;> simp [FiniteEvents.indicator, h]

/-- The sum of the probabilities of all collision witnesses. -/
noncomputable def collisionFirstSum {m n : ℕ} (P : Board m n) (k : ℕ) : ℝ :=
  ∑ w : CollisionWitness k, eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
    {s : Fin k → Fin m × Fin n | CollisionEvent w s}

/-- The union of collision witnesses has probability exactly `1-F_k(P)`. -/
theorem collision_union_mass {m n k : ℕ} {P : Board m n} (hP : IsProbability P) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | ∃ w : CollisionWitness k, CollisionEvent w s} =
        1 - separationProbability P k := by
  have he : {s : Fin k → Fin m × Fin n | ∃ w : CollisionWitness k, CollisionEvent w s} =
      {s : Fin k → Fin m × Fin n | RowsDistinct s ∨ ColsDistinct s}ᶜ := by
    ext s
    exact exists_collisionWitness_iff s
  rw [he, eventMass_compl _ ((sum_cell_weights P).trans hP.2)]
  rfl

/-- The elementary union bound for the actual sample collision witnesses. -/
theorem failure_le_collisionFirstSum {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) : 1 - separationProbability P k ≤ collisionFirstSum P k := by
  classical
  rw [← collision_union_mass hP, collisionFirstSum]
  simp_rw [eventMass_eq_finiteMass]
  have h := FiniteEvents.union_bound Finset.univ (Finset.univ : Finset (CollisionWitness k))
    (sampleMass (fun a : Fin m × Fin n ↦ P a.1 a.2))
    (fun w (s : Fin k → Fin m × Fin n) ↦ CollisionEvent w s)
    (fun s _ ↦ sampleMass_nonneg _ (fun a ↦ hP.1 a.1 a.2) s)
  simpa only [Finset.mem_univ, true_and, Set.mem_ofPred_eq] using h

/-- A bound on distinct witness intersections gives the exact Bonferroni factor.

The hypothesis concerns the original independent-cell measure. Establishing
it by deletion of a constrained sample is a separate combinatorial step.
-/
theorem collisionFirstSum_le_of_intersections {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (η : ℝ)
    (hpair : ∀ w v : CollisionWitness k, w ≠ v →
      eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
        {s : Fin k → Fin m × Fin n | CollisionEvent w s ∧ CollisionEvent v s} ≤
          η * (1 - separationProbability P k)) :
    collisionFirstSum P k ≤
      (1 + (((k.choose 2) ^ 2).choose 2 : ℝ) * η) *
        (1 - separationProbability P k) := by
  classical
  have h := FiniteEvents.collision_sum_le Finset.univ
    (Finset.univ : Finset (CollisionWitness k))
    (sampleMass (fun a : Fin m × Fin n ↦ P a.1 a.2))
    (fun w (s : Fin k → Fin m × Fin n) ↦ CollisionEvent w s) η
    (fun s _ ↦ sampleMass_nonneg _ (fun a ↦ hP.1 a.1 a.2) s)
  have hunion : FiniteEvents.mass Finset.univ
      (sampleMass (fun a : Fin m × Fin n ↦ P a.1 a.2))
      (fun s : Fin k → Fin m × Fin n ↦
        ∃ w ∈ (Finset.univ : Finset (CollisionWitness k)), CollisionEvent w s) =
          1 - separationProbability P k := by
    simpa only [eventMass_eq_finiteMass, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] using collision_union_mass hP
  rw [hunion, Finset.card_univ, card_collisionWitness] at h
  unfold collisionFirstSum
  simp_rw [eventMass_eq_finiteMass]
  apply h
  intro w _ v _ hwv
  simpa only [eventMass_eq_finiteMass, Set.mem_ofPred_eq] using hpair w v hwv

/-- Delete the second index of an equality constraint; its value is recovered
from the first index. This counts constrained functions without any sampling
or dimension assumptions. -/
def equalSamplesEquiv {α β : Type*} [DecidableEq α] (i j : α) (hij : i ≠ j) :
    {f : α → β // f i = f j} ≃ ({t : α // t ≠ j} → β) where
  toFun f t := f.val t.val
  invFun g := ⟨fun t ↦ if h : t = j then g ⟨i, hij⟩ else g ⟨t, h⟩, by simp [hij]⟩
  left_inv f := by
    apply Subtype.ext
    funext t
    by_cases ht : t = j
    · subst t
      simpa using f.property
    · simp [ht]
  right_inv g := by
    funext t
    simp [t.property]

/-- Exactly one free label is removed by an equality between distinct indices. -/
theorem card_equalSamples (d k : ℕ) (ij : SampleIndexPair k) :
    Nat.card {f : Fin k → Fin d // f ij.val.1 = f ij.val.2} = d ^ (k - 1) := by
  classical
  rw [Nat.card_congr (equalSamplesEquiv ij.val.1 ij.val.2 (ne_of_lt ij.property))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.card_subtype_compl (fun t : Fin k ↦ t = ij.val.2)]
  simp

/-- Row and column equality constraints separate into independent label
functions, even if their sample-index pairs coincide or overlap. -/
def collisionEventEquiv {m n k : ℕ} (w : CollisionWitness k) :
    {s : Fin k → Fin m × Fin n // CollisionEvent w s} ≃
      {r : Fin k → Fin m // r w.1.val.1 = r w.1.val.2} ×
        {c : Fin k → Fin n // c w.2.val.1 = c w.2.val.2} where
  toFun s := (⟨fun t ↦ (s.val t).1, s.property.1⟩,
    ⟨fun t ↦ (s.val t).2, s.property.2⟩)
  invFun f := ⟨fun t ↦ (f.1.val t, f.2.val t), f.1.property, f.2.property⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv f := by
    rcases f with ⟨⟨r, hr⟩, ⟨c, hc⟩⟩
    rfl

theorem card_collisionEvent (m n k : ℕ) (w : CollisionWitness k) :
    Nat.card {s : Fin k → Fin m × Fin n // CollisionEvent w s} =
      m ^ (k - 1) * n ^ (k - 1) := by
  rw [Nat.card_congr (collisionEventEquiv (m := m) (n := n) w), Nat.card_prod,
    card_equalSamples, card_equalSamples]

/-- Every uniform witness has mass `1/(mn)`, with no restriction on how its
two sample-index pairs meet. -/
theorem collisionEvent_mass_uniform {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (w : CollisionWitness k) :
    eventMass (fun a : Fin m × Fin n ↦ uniformBoard m n a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent w s} = 1 / ((m : ℝ) * n) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hk : 1 ≤ k := by have := w.1.val.1.isLt; omega
  simp only [uniformBoard]
  rw [eventMass_const]
  change (Nat.card {s : Fin k → Fin m × Fin n // CollisionEvent w s} : ℝ) *
    ((m : ℝ) * n)⁻¹ ^ k = _
  rw [card_collisionEvent]
  simp only [Nat.cast_mul, Nat.cast_pow, ← mul_pow, inv_pow]
  have hpow : ((m : ℝ) * n) ^ k = ((m : ℝ) * n) ^ (k - 1) * ((m : ℝ) * n) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  rw [hpow]
  field_simp

/-- The exact first collision sum at uniform. -/
theorem collisionFirstSum_uniform {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) :
    collisionFirstSum (uniformBoard m n) k =
      ((k.choose 2) ^ 2 : ℝ) / ((m : ℝ) * n) := by
  unfold collisionFirstSum
  simp_rw [collisionEvent_mass_uniform hm hn]
  rw [Finset.sum_const, Finset.card_univ, card_collisionWitness, nsmul_eq_mul]
  push_cast
  ring

/-- The uniform failure bound used in the contender concentration argument. -/
theorem failure_uniform_le {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) :
    1 - separationProbability (uniformBoard m n) k ≤
      ((k.choose 2) ^ 2 : ℝ) / ((m : ℝ) * n) := by
  simpa only [collisionFirstSum_uniform hm hn] using
    (failure_le_collisionFirstSum (k := k) (uniformBoard_isProbability hm hn))

end DittertRybin
