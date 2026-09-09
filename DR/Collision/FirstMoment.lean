import DR.Collision.Witnesses
import DR.Marginalization
import DR.Rectangular.OrderTwo
import Mathlib.Data.Fintype.CardEmbedding

/-!
# The exact first collision moment

Two sample-index pairs may coincide, meet in one index, or be disjoint.
Their basic independent-sample masses are respectively the cell square
sum, the mixed cell/row/column moment, and the product of marginal square
sums. The basic pattern identities allow signed cell weights and need no
normalization. Marginalization transfers them to arbitrary distinct sample
indices on probability matrices.

The final theorem `collisionFirstSum_formula` proves, for `k ≥ 4`,

`L = choose(k,2) ∑p² + 6 choose(k,3) ∑p r c + 6 choose(k,4) (∑r²)(∑c²)`.

The coefficients are proved by an exhaustive three-way witness partition.
Overlapping witnesses are in bijection with injective ordered triples;
the remaining disjoint count follows from the total witness count and an
exact binomial identity. No positivity beyond the probability-matrix domain
and no balance of row or column marginals is imposed.
-/

namespace DittertRybin

open scoped BigOperators

/-- The sum of squared cell weights. -/
def cellSquareSum {m n : ℕ} (P : Board m n) : ℝ :=
  ∑ a : Fin m × Fin n, P a.1 a.2 ^ 2

/-- The sum of squared row masses. -/
def rowSquareSum {m n : ℕ} (P : Board m n) : ℝ := ∑ i, rowSum P i ^ 2

/-- The sum of squared column masses. -/
def colSquareSum {m n : ℕ} (P : Board m n) : ℝ := ∑ j, colSum P j ^ 2

/-- The moment for a shared sample with one row mate and one column mate. -/
def mixedCollisionMoment {m n : ℕ} (P : Board m n) : ℝ :=
  ∑ a : Fin m × Fin n, P a.1 a.2 * rowSum P a.1 * colSum P a.2

private def samplesThreeEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun s := (s 0, s 1, s 2)
  invFun a := ![a.1, a.2.1, a.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv a := by rfl

private def samplesFourEquiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun s := (s 0, s 1, s 2, s 3)
  invFun a := ![a.1, a.2.1, a.2.2.1, a.2.2.2]
  left_inv s := by funext i; fin_cases i <;> rfl
  right_inv a := by rfl

private theorem sum_samplesThree {α : Type*} [Fintype α] (f : (Fin 3 → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
  rw [← (samplesThreeEquiv α).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem sum_samplesFour {α : Type*} [Fintype α] (f : (Fin 4 → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
  rw [← (samplesFourEquiv α).symm.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

theorem sum_row_eq_weight {m n : ℕ} (P : Board m n) (i : Fin m) :
    (∑ a : Fin m × Fin n, if i = a.1 then P a.1 a.2 else 0) = rowSum P i := by
  classical
  simp [Fintype.sum_prod_type, rowSum]

theorem sum_col_eq_weight {m n : ℕ} (P : Board m n) (j : Fin n) :
    (∑ a : Fin m × Fin n, if j = a.2 then P a.1 a.2 else 0) = colSum P j := by
  classical
  simp [Fintype.sum_prod_type, colSum]

/-- Coincident row and column pairs force equality of the two sampled cells. -/
theorem coincident_pattern_mass {m n : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin 2 → Fin m × Fin n | (s 0).1 = (s 1).1 ∧ (s 0).2 = (s 1).2} =
        cellSquareSum P := by
  have he : {s : Fin 2 → Fin m × Fin n | (s 0).1 = (s 1).1 ∧ (s 0).2 = (s 1).2} =
      {s : Fin 2 → Fin m × Fin n | s 0 = s 1} := by
    ext s
    exact Prod.ext_iff.symm
  rw [he, eventMass_two_equal]
  rfl

/-- A shared cell, its row mate, and its column mate have mass `∑ p r c`. -/
theorem overlapping_pattern_mass {m n : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin 3 → Fin m × Fin n | (s 0).1 = (s 1).1 ∧ (s 0).2 = (s 2).2} =
        mixedCollisionMoment P := by
  classical
  unfold eventMass
  rw [sum_samplesThree]
  simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sampleMass, Fin.prod_univ_three]
  have hterm (a b c : Fin m × Fin n) :
      (if a.1 = b.1 ∧ a.2 = c.2 then P a.1 a.2 * P b.1 b.2 * P c.1 c.2 else 0) =
        P a.1 a.2 * (if a.1 = b.1 then P b.1 b.2 else 0) *
          (if a.2 = c.2 then P c.1 c.2 else 0) := by
    by_cases hr : a.1 = b.1 <;> by_cases hc : a.2 = c.2 <;> simp [hr, hc]
  simp_rw [hterm]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_row_eq_weight, sum_col_eq_weight]
  rfl

/-- The sum for one row-equality pair is the squared row-mass sum. -/
theorem sum_row_pair_weight {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, ∑ b : Fin m × Fin n,
      if a.1 = b.1 then P a.1 a.2 * P b.1 b.2 else 0) = rowSquareSum P := by
  classical
  have hterm (a b : Fin m × Fin n) :
      (if a.1 = b.1 then P a.1 a.2 * P b.1 b.2 else 0) =
        P a.1 a.2 * (if a.1 = b.1 then P b.1 b.2 else 0) := by
    by_cases h : a.1 = b.1 <;> simp [h]
  simp_rw [hterm, ← Finset.mul_sum, sum_row_eq_weight]
  simp only [Fintype.sum_prod_type, ← Finset.sum_mul, rowSum, rowSquareSum, pow_two]

/-- The sum for one column-equality pair is the squared column-mass sum. -/
theorem sum_col_pair_weight {m n : ℕ} (P : Board m n) :
    (∑ a : Fin m × Fin n, ∑ b : Fin m × Fin n,
      if a.2 = b.2 then P a.1 a.2 * P b.1 b.2 else 0) = colSquareSum P := by
  classical
  have hterm (a b : Fin m × Fin n) :
      (if a.2 = b.2 then P a.1 a.2 * P b.1 b.2 else 0) =
        P a.1 a.2 * (if a.2 = b.2 then P b.1 b.2 else 0) := by
    by_cases h : a.2 = b.2 <;> simp [h]
  simp_rw [hterm, ← Finset.mul_sum, sum_col_eq_weight]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.sum_mul, colSum, colSquareSum, pow_two]

/-- Disjoint row and column pairs have the product of their two marginal square sums. -/
theorem disjoint_pattern_mass {m n : ℕ} (P : Board m n) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin 4 → Fin m × Fin n | (s 0).1 = (s 1).1 ∧ (s 2).2 = (s 3).2} =
        rowSquareSum P * colSquareSum P := by
  classical
  unfold eventMass
  rw [sum_samplesFour]
  simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    sampleMass, Fin.prod_univ_four]
  have hterm (a b c d : Fin m × Fin n) :
      (if a.1 = b.1 ∧ c.2 = d.2 then
        P a.1 a.2 * P b.1 b.2 * P c.1 c.2 * P d.1 d.2 else 0) =
        (if a.1 = b.1 then P a.1 a.2 * P b.1 b.2 else 0) *
          (if c.2 = d.2 then P c.1 c.2 * P d.1 d.2 else 0) := by
    by_cases hr : a.1 = b.1 <;> by_cases hc : c.2 = d.2 <;> simp [hr, hc]
    ring
  simp_rw [hterm]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_row_pair_weight, sum_col_pair_weight]

/-- A canonical sample pair viewed as an injection of two indices. -/
def sampleIndexPairEmbedding {k : ℕ} (ij : SampleIndexPair k) : Fin 2 ↪ Fin k where
  toFun := ![ij.val.1, ij.val.2]
  inj' := by
    intro i j h
    have hne := ne_of_lt ij.property
    fin_cases i <;> fin_cases j <;> simp_all

/-- The coincident pattern has the same mass at any two different sample indices. -/
theorem coincident_indices_mass {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (e : Fin 2 ↪ Fin k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n |
        (s (e 0)).1 = (s (e 1)).1 ∧ (s (e 0)).2 = (s (e 1)).2} = cellSquareSum P := by
  have h := eventMass_restrict (fun a : Fin m × Fin n ↦ P a.1 a.2)
    ((sum_cell_weights P).trans hP.2) e
    {s : Fin 2 → Fin m × Fin n | (s 0).1 = (s 1).1 ∧ (s 0).2 = (s 1).2}
  exact h.trans (coincident_pattern_mass P)

/-- The overlapping pattern has the same mass at any three different sample indices. -/
theorem overlapping_indices_mass {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (e : Fin 3 ↪ Fin k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n |
        (s (e 0)).1 = (s (e 1)).1 ∧ (s (e 0)).2 = (s (e 2)).2} =
        mixedCollisionMoment P := by
  have h := eventMass_restrict (fun a : Fin m × Fin n ↦ P a.1 a.2)
    ((sum_cell_weights P).trans hP.2) e
    {s : Fin 3 → Fin m × Fin n | (s 0).1 = (s 1).1 ∧ (s 0).2 = (s 2).2}
  exact h.trans (overlapping_pattern_mass P)

/-- The disjoint pattern has the same mass at any four different sample indices. -/
theorem disjoint_indices_mass {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (e : Fin 4 ↪ Fin k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n |
        (s (e 0)).1 = (s (e 1)).1 ∧ (s (e 2)).2 = (s (e 3)).2} =
        rowSquareSum P * colSquareSum P := by
  have h := eventMass_restrict (fun a : Fin m × Fin n ↦ P a.1 a.2)
    ((sum_cell_weights P).trans hP.2) e
    {s : Fin 4 → Fin m × Fin n | (s 0).1 = (s 1).1 ∧ (s 2).2 = (s 3).2}
  exact h.trans (disjoint_pattern_mass P)

/-- A witness with coincident row and column pairs contributes the cell square sum. -/
theorem collisionEvent_mass_of_same_pair {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (ij : SampleIndexPair k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent (ij, ij) s} = cellSquareSum P := by
  exact coincident_indices_mass hP (sampleIndexPairEmbedding ij)

/-- The total contribution of coincident witness pairs, with its exact coefficient. -/
theorem coincident_witness_sum {m n k : ℕ} {P : Board m n} (hP : IsProbability P) :
    (∑ ij : SampleIndexPair k, eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent (ij, ij) s}) =
        (k.choose 2 : ℝ) * cellSquareSum P := by
  simp_rw [collisionEvent_mass_of_same_pair hP]
  simp [card_sampleIndexPair]

/-- Membership in a sample-index pair, without introducing an orientation. -/
def PairContains {k : ℕ} (ij : SampleIndexPair k) (t : Fin k) : Prop :=
  t = ij.val.1 ∨ t = ij.val.2

/-- Canonically sort two different sample indices. -/
def sortedIndexPair {k : ℕ} (i j : Fin k) (hij : i ≠ j) : SampleIndexPair k :=
  if h : i < j then ⟨(i, j), h⟩ else ⟨(j, i), lt_of_le_of_ne (le_of_not_gt h) hij.symm⟩

theorem pairContains_sorted {k : ℕ} (i j t : Fin k) (hij : i ≠ j) :
    PairContains (sortedIndexPair i j hij) t ↔ t = i ∨ t = j := by
  by_cases h : i < j <;> simp [sortedIndexPair, h, PairContains, or_comm]

theorem sampleIndexPair_eq_iff {k : ℕ} (r c : SampleIndexPair k) :
    r = c ↔ PairContains c r.val.1 ∧ PairContains c r.val.2 := by
  constructor
  · rintro rfl
    simp [PairContains]
  · intro h
    have hr := r.property
    have hc := c.property
    rcases h with ⟨hrc, hcr⟩
    rcases hrc with hrc | hrc <;> rcases hcr with hcr | hcr
    · omega
    · apply Subtype.ext
      exact Prod.ext hrc hcr
    · omega
    · omega

/-- Distinct row/column pairs that share a sample index. -/
def PairsOverlap {k : ℕ} (w : CollisionWitness k) : Prop :=
  w.1 ≠ w.2 ∧ ∃ t, PairContains w.1 t ∧ PairContains w.2 t

/-- Overlapping witnesses, as a finite subtype of all witnesses. -/
abbrev OverlappingWitness (k : ℕ) := {w : CollisionWitness k // PairsOverlap w}

noncomputable instance (k : ℕ) : Fintype (OverlappingWitness k) := Fintype.ofFinite _

private theorem embedding_three_ne {k : ℕ} (e : Fin 3 ↪ Fin k) :
    e 0 ≠ e 1 ∧ e 0 ≠ e 2 ∧ e 1 ≠ e 2 := by
  constructor
  · exact e.injective.ne (by decide)
  constructor
  · exact e.injective.ne (by decide)
  · exact e.injective.ne (by decide)

/-- An injective triple specifies its shared, row-only, and column-only indices. -/
def overlappingWitnessOfTriple {k : ℕ} (e : Fin 3 ↪ Fin k) : OverlappingWitness k := by
  let r := sortedIndexPair (e 0) (e 1) (embedding_three_ne e).1
  let c := sortedIndexPair (e 0) (e 2) (embedding_three_ne e).2.1
  refine ⟨(r, c), ?_, e 0, ?_, ?_⟩
  · intro heq
    change r = c at heq
    have hmem : PairContains c (e 1) := by
      rw [← heq]
      exact (pairContains_sorted _ _ _ _).mpr (Or.inr rfl)
    have hcases := (pairContains_sorted _ _ _ _).mp hmem
    rcases hcases with h | h
    · exact (embedding_three_ne e).1 h.symm
    · exact (embedding_three_ne e).2.2 h
  · exact (pairContains_sorted (e 0) (e 1) (e 0) (embedding_three_ne e).1).mpr (Or.inl rfl)
  · exact (pairContains_sorted (e 0) (e 2) (e 0) (embedding_three_ne e).2.1).mpr (Or.inl rfl)

theorem overlappingWitnessOfTriple_injective {k : ℕ} :
    Function.Injective (overlappingWitnessOfTriple (k := k)) := by
  intro e f h
  have hr := congrArg (fun w : OverlappingWitness k ↦ w.val.1) h
  have hc := congrArg (fun w : OverlappingWitness k ↦ w.val.2) h
  have he := embedding_three_ne e
  have hf := embedding_three_ne f
  have hr0 : e 0 = f 0 ∨ e 0 = f 1 := by
    have hm := (pairContains_sorted (e 0) (e 1) (e 0) he.1).mpr (Or.inl rfl)
    change PairContains (overlappingWitnessOfTriple e).val.1 (e 0) at hm
    rw [hr] at hm
    exact (pairContains_sorted (f 0) (f 1) (e 0) hf.1).mp hm
  have hc0 : e 0 = f 0 ∨ e 0 = f 2 := by
    have hm := (pairContains_sorted (e 0) (e 2) (e 0) he.2.1).mpr (Or.inl rfl)
    change PairContains (overlappingWitnessOfTriple e).val.2 (e 0) at hm
    rw [hc] at hm
    exact (pairContains_sorted (f 0) (f 2) (e 0) hf.2.1).mp hm
  have h0 : e 0 = f 0 := by
    rcases hr0 with h0 | h1
    · exact h0
    rcases hc0 with h0 | h2
    · exact h0
    exact False.elim (hf.2.2 (h1.symm.trans h2))
  have hr1 : e 1 = f 0 ∨ e 1 = f 1 := by
    have hm := (pairContains_sorted (e 0) (e 1) (e 1) he.1).mpr (Or.inr rfl)
    change PairContains (overlappingWitnessOfTriple e).val.1 (e 1) at hm
    rw [hr] at hm
    exact (pairContains_sorted (f 0) (f 1) (e 1) hf.1).mp hm
  have hc2 : e 2 = f 0 ∨ e 2 = f 2 := by
    have hm := (pairContains_sorted (e 0) (e 2) (e 2) he.2.1).mpr (Or.inr rfl)
    change PairContains (overlappingWitnessOfTriple e).val.2 (e 2) at hm
    rw [hc] at hm
    exact (pairContains_sorted (f 0) (f 2) (e 2) hf.2.1).mp hm
  have h1 : e 1 = f 1 := hr1.resolve_left (fun h1 ↦ he.1 (h0.trans h1.symm))
  have h2 : e 2 = f 2 := hc2.resolve_left (fun h2 ↦ he.2.1 (h0.trans h2.symm))
  apply Function.Embedding.ext
  intro t
  fin_cases t <;> assumption

private theorem exists_other_index {k : ℕ} (r : SampleIndexPair k) (t : Fin k)
    (ht : PairContains r t) : ∃ u, ∃ htu : t ≠ u, sortedIndexPair t u htu = r := by
  rcases ht with rfl | rfl
  · refine ⟨r.val.2, ne_of_lt r.property, ?_⟩
    simp only [sortedIndexPair, dif_pos r.property]
  · refine ⟨r.val.1, (ne_of_lt r.property).symm, ?_⟩
    simp only [sortedIndexPair, dif_neg (not_lt_of_gt r.property)]

private def tripleEmbedding {k : ℕ} (t u v : Fin k) (htu : t ≠ u) (htv : t ≠ v)
    (huv : u ≠ v) : Fin 3 ↪ Fin k where
  toFun := ![t, u, v]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

theorem overlappingWitnessOfTriple_surjective {k : ℕ} :
    Function.Surjective (overlappingWitnessOfTriple (k := k)) := by
  rintro ⟨⟨r, c⟩, hne, t, htr, htc⟩
  obtain ⟨u, htu, hr⟩ := exists_other_index r t htr
  obtain ⟨v, htv, hc⟩ := exists_other_index c t htc
  have huv : u ≠ v := by
    intro heq
    subst v
    exact hne (hr.symm.trans hc)
  refine ⟨tripleEmbedding t u v htu htv huv, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hr
  · exact hc

/-- The overlap coefficient is the number of ordered injective triples. -/
theorem card_overlappingWitness (k : ℕ) :
    Nat.card (OverlappingWitness k) = 6 * k.choose 3 := by
  rw [← Nat.card_congr (Equiv.ofBijective (overlappingWitnessOfTriple (k := k))
    ⟨overlappingWitnessOfTriple_injective, overlappingWitnessOfTriple_surjective⟩)]
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  norm_num [Nat.factorial]

theorem collisionEvent_mass_of_triple {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (e : Fin 3 ↪ Fin k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent (overlappingWitnessOfTriple e).val s} =
        mixedCollisionMoment P := by
  have hevent : {s : Fin k → Fin m × Fin n |
      CollisionEvent (overlappingWitnessOfTriple e).val s} =
      {s : Fin k → Fin m × Fin n |
        (s (e 0)).1 = (s (e 1)).1 ∧ (s (e 0)).2 = (s (e 2)).2} := by
    ext s
    by_cases hr : e 0 < e 1 <;> by_cases hc : e 0 < e 2 <;>
      simp [overlappingWitnessOfTriple, sortedIndexPair, CollisionEvent, hr, hc, eq_comm]
  rw [hevent]
  exact overlapping_indices_mass hP e

/-- Every overlapping witness contributes the same mixed moment. -/
theorem collisionEvent_mass_of_overlap {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (w : OverlappingWitness k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent w.val s} = mixedCollisionMoment P := by
  obtain ⟨e, rfl⟩ := overlappingWitnessOfTriple_surjective w
  exact collisionEvent_mass_of_triple hP e

/-- The total overlap contribution, including the exact factor `6 choose(k,3)`. -/
theorem overlapping_witness_sum {m n k : ℕ} {P : Board m n} (hP : IsProbability P) :
    (∑ w : OverlappingWitness k, eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent w.val s}) =
        (6 * k.choose 3 : ℝ) * mixedCollisionMoment P := by
  classical
  simp_rw [collisionEvent_mass_of_overlap hP]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_overlappingWitness]
  simp

/-- Row and column pairs with no common sample index. -/
def PairsDisjoint {k : ℕ} (w : CollisionWitness k) : Prop :=
  ¬ ∃ t, PairContains w.1 t ∧ PairContains w.2 t

abbrev DisjointWitness (k : ℕ) := {w : CollisionWitness k // PairsDisjoint w}

noncomputable instance (k : ℕ) : Fintype (DisjointWitness k) := Fintype.ofFinite _

theorem disjoint_pairs_ne {k : ℕ} (w : DisjointWitness k) : w.val.1 ≠ w.val.2 := by
  intro h
  apply w.property
  refine ⟨w.val.1.val.1, Or.inl rfl, ?_⟩
  rw [← h]
  exact Or.inl rfl

/-- Read a disjoint witness as an injective ordered four-tuple. -/
def disjointWitnessEmbedding {k : ℕ} (w : DisjointWitness k) : Fin 4 ↪ Fin k where
  toFun := ![w.val.1.val.1, w.val.1.val.2, w.val.2.val.1, w.val.2.val.2]
  inj' := by
    have hr := ne_of_lt w.val.1.property
    have hc := ne_of_lt w.val.2.property
    have h00 : w.val.1.val.1 ≠ w.val.2.val.1 :=
      fun h ↦ w.property ⟨_, Or.inl rfl, Or.inl h⟩
    have h01 : w.val.1.val.1 ≠ w.val.2.val.2 :=
      fun h ↦ w.property ⟨_, Or.inl rfl, Or.inr h⟩
    have h10 : w.val.1.val.2 ≠ w.val.2.val.1 :=
      fun h ↦ w.property ⟨_, Or.inr rfl, Or.inl h⟩
    have h11 : w.val.1.val.2 ≠ w.val.2.val.2 :=
      fun h ↦ w.property ⟨_, Or.inr rfl, Or.inr h⟩
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

theorem collisionEvent_mass_of_disjoint {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (w : DisjointWitness k) :
    eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent w.val s} =
        rowSquareSum P * colSquareSum P := by
  exact disjoint_indices_mass hP (disjointWitnessEmbedding w)

/-- Partition all witnesses into the three possible intersection patterns. -/
noncomputable def collisionWitnessCasesEquiv (k : ℕ) :
    CollisionWitness k ≃ SampleIndexPair k ⊕ OverlappingWitness k ⊕ DisjointWitness k := by
  classical
  exact
    { toFun := fun w ↦ if heq : w.1 = w.2 then Sum.inl w.1
        else if hmeet : ∃ t, PairContains w.1 t ∧ PairContains w.2 t then
          Sum.inr (Sum.inl ⟨w, heq, hmeet⟩)
        else Sum.inr (Sum.inr ⟨w, hmeet⟩)
      invFun := fun w ↦ match w with
        | Sum.inl r => (r, r)
        | Sum.inr (Sum.inl w) => w.val
        | Sum.inr (Sum.inr w) => w.val
      left_inv := by
        intro w
        by_cases heq : w.1 = w.2
        · simp [heq]
          exact Prod.ext heq.symm rfl
        · by_cases hmeet : ∃ t, PairContains w.1 t ∧ PairContains w.2 t <;>
            simp [heq, hmeet]
      right_inv := by
        intro w
        rcases w with r | w
        · simp
        rcases w with w | w
        · simp [w.property.1, w.property.2]
        · have hn : ¬ ∃ t, PairContains w.val.1 t ∧ PairContains w.val.2 t := w.property
          simp [disjoint_pairs_ne w, hn] }

/-- The three pattern counts sum to the number of all witnesses. -/
theorem collision_pattern_count_partition (k : ℕ) :
    (k.choose 2) ^ 2 = k.choose 2 + (6 * k.choose 3 + Nat.card (DisjointWitness k)) := by
  have h := Nat.card_congr (collisionWitnessCasesEquiv k)
  have hi : Nat.card (SampleIndexPair k) = k.choose 2 := by
    rw [Nat.card_eq_fintype_card, card_sampleIndexPair]
  have hw : Nat.card (CollisionWitness k) = (k.choose 2) ^ 2 := by
    rw [Nat.card_eq_fintype_card, card_collisionWitness]
  simpa only [Nat.card_sum, hi, hw, card_overlappingWitness] using h

private theorem choose_two_square {k : ℕ} (hk : 4 ≤ k) :
    (k.choose 2) ^ 2 = k.choose 2 + 6 * k.choose 3 + 6 * k.choose 4 := by
  have h2 := Nat.descFactorial_eq_factorial_mul_choose k 2
  have h3 := Nat.descFactorial_eq_factorial_mul_choose k 3
  have h4 := Nat.descFactorial_eq_factorial_mul_choose k 4
  norm_num [Nat.descFactorial, Nat.factorial] at h2 h3 h4
  obtain ⟨q, hq⟩ : ∃ q, k = q + 4 := ⟨k - 4, by omega⟩
  have hs1 : k - 1 = q + 3 := by omega
  have hs2 : k - 2 = q + 2 := by omega
  have hs3 : k - 3 = q + 1 := by omega
  rw [hs1, hq] at h2
  rw [hs1, hs2, hq] at h3
  rw [hs1, hs2, hs3, hq] at h4
  have hs := congrArg (fun x : ℕ ↦ x ^ 2) h2
  rw [hq]
  nlinarith [hs]

/-- The remaining disjoint witnesses number exactly `6 choose(k,4)`. -/
theorem card_disjointWitness {k : ℕ} (hk : 4 ≤ k) :
    Nat.card (DisjointWitness k) = 6 * k.choose 4 := by
  have hc := collision_pattern_count_partition k
  have hb := choose_two_square hk
  omega

theorem disjoint_witness_sum {m n k : ℕ} {P : Board m n} (hP : IsProbability P)
    (hk : 4 ≤ k) :
    (∑ w : DisjointWitness k, eventMass (fun a : Fin m × Fin n ↦ P a.1 a.2)
      {s : Fin k → Fin m × Fin n | CollisionEvent w.val s}) =
        (6 * k.choose 4 : ℝ) * (rowSquareSum P * colSquareSum P) := by
  simp_rw [collisionEvent_mass_of_disjoint hP]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_disjointWitness hk]
  simp

/-- The exact first collision sum, for every probability matrix and `k ≥ 4`.

The three coefficients count coincident, overlapping, and disjoint pairs.
All sample-event identities are proved above from independent sampling;
zeros and arbitrary row and column marginals are allowed.
-/
theorem collisionFirstSum_formula {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (hk : 4 ≤ k) :
    collisionFirstSum P k = (k.choose 2 : ℝ) * cellSquareSum P +
      (6 * k.choose 3 : ℝ) * mixedCollisionMoment P +
      (6 * k.choose 4 : ℝ) * (rowSquareSum P * colSquareSum P) := by
  classical
  unfold collisionFirstSum
  rw [← (collisionWitnessCasesEquiv k).symm.sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  change (∑ ij : SampleIndexPair k, eventMass _ {s | CollisionEvent (ij, ij) s}) +
    ((∑ w : OverlappingWitness k, eventMass _ {s | CollisionEvent w.val s}) +
      ∑ w : DisjointWitness k, eventMass _ {s | CollisionEvent w.val s}) = _
  rw [coincident_witness_sum hP, overlapping_witness_sum hP, disjoint_witness_sum hP hk]
  ring

end DittertRybin
