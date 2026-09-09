import DR.Definitions
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Finite capacity transport

A transport matrix has a prescribed common row and column mass and lies
entrywise below a nonnegative capacity matrix. This file proves the exact cut
criterion for finite real capacities, including zero demand and empty matrices.

For sufficiency, first maximize transported mass and then minimize the sum of
squared row sums on that compact set of maximizers. Let I be the deficient
rows and T the columns with a slack-capacity edge from I. One-cell augmentation
forces T to be full. A two-cell shift from a full row to a deficient row would
lower the secondary objective, so the I-complement by T rectangle is zero.
The I by T-complement rectangle is saturated by definition. A deficient row
therefore supplies a violated cut. This argument uses compactness and finite
sums directly; it does not invoke a general flow or linear-programming theorem.
-/

open scoped BigOperators
open Finset Set

namespace DittertRybin

/-- The mass in a rectangle of row and column indices. -/
def cutMass {m n : ℕ} (A : Board m n) (I : Finset (Fin m))
    (J : Finset (Fin n)) : ℝ := ∑ i ∈ I, ∑ j ∈ J, A i j

theorem cutMass_nonneg {m n : ℕ} {A : Board m n}
    (hA : ∀ i j, 0 ≤ A i j) (I : Finset (Fin m)) (J : Finset (Fin n)) :
    0 ≤ cutMass A I J :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA i j

theorem cutMass_mono {m n : ℕ} {A B : Board m n}
    (h : ∀ i j, A i j ≤ B i j) (I : Finset (Fin m)) (J : Finset (Fin n)) :
    cutMass A I J ≤ cutMass B I J :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

theorem cutMass_add_compl_cols {m n : ℕ} (A : Board m n)
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    cutMass A I J + cutMass A I Jᶜ = ∑ i ∈ I, rowSum A i := by
  unfold cutMass rowSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_add_sum_compl J (fun j => A i j)

theorem cutMass_add_compl_rows {m n : ℕ} (A : Board m n)
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    cutMass A I J + cutMass A Iᶜ J = ∑ j ∈ J, colSum A j := by
  unfold cutMass colSum
  calc
    _ = (∑ j ∈ J, ∑ i ∈ I, A i j) + (∑ j ∈ J, ∑ i ∈ Iᶜ, A i j) :=
      congrArg₂ (· + ·) (Finset.sum_comm (s := I) (t := J))
        (Finset.sum_comm (s := Iᶜ) (t := J))
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_add_sum_compl I (fun i => A i j)

/-- B is a nonnegative transport of common marginal q, within capacities A. -/
def IsTransport {n : ℕ} (A : Board n n) (q : ℝ) (B : Board n n) : Prop :=
  (∀ i j, 0 ≤ B i j) ∧ (∀ i j, B i j ≤ A i j) ∧
    (∀ i, rowSum B i = q) ∧ (∀ j, colSum B j = q)

/-- The proposed capacity criterion. Cardinalities are cast before subtraction;
negative and zero-capacity cuts are included. -/
def TransportCuts {n : ℕ} (A : Board n n) (q : ℝ) : Prop :=
  ∀ I J : Finset (Fin n),
    q * ((I.card : ℝ) + (J.card : ℝ) - n) ≤ cutMass A I J

/-- Common row/column sums give an exact complementary-rectangle identity. -/
theorem cutMass_eq_demand_add_complement {n : ℕ} (B : Board n n) (q : ℝ)
    (hr : ∀ i, rowSum B i = q) (hc : ∀ j, colSum B j = q)
    (I J : Finset (Fin n)) :
    cutMass B I J = q * ((I.card : ℝ) + (J.card : ℝ) - n) +
      cutMass B Iᶜ Jᶜ := by
  have hrows := cutMass_add_compl_cols B I J
  have hcols := cutMass_add_compl_rows B I Jᶜ
  simp only [hr, hc, Finset.sum_const, nsmul_eq_mul] at hrows hcols
  have hcard : (J.card : ℝ) + (Jᶜ.card : ℝ) = n := by
    exact_mod_cast (show J.card + Jᶜ.card = n by simp)
  have hcompl : (Jᶜ.card : ℝ) = n - (J.card : ℝ) := by linarith
  rw [hcompl] at hcols
  nlinarith

/-- Every feasible transport satisfies every capacity cut inequality. -/
theorem IsTransport.cuts {n : ℕ} {A B : Board n n} {q : ℝ}
    (h : IsTransport A q B) : TransportCuts A q := by
  intro I J
  have hcomp := cutMass_nonneg h.1 Iᶜ Jᶜ
  have heq := cutMass_eq_demand_add_complement B q h.2.2.1 h.2.2.2 I J
  have hmono := cutMass_mono h.2.1 I J
  linarith

/-- Zero demand is feasible for every nonnegative capacity matrix. -/
theorem zero_isTransport {n : ℕ} {A : Board n n} (hA : ∀ i j, 0 ≤ A i j) :
    IsTransport A 0 0 := by
  exact ⟨by simp, hA, by simp [rowSum], by simp [colSum]⟩

/-- The full criterion at q=0 needs no positivity or division by q. -/
theorem transport_iff_cuts_zero {n : ℕ} {A : Board n n}
    (hA : ∀ i j, 0 ≤ A i j) :
    (∃ B, IsTransport A 0 B) ↔ TransportCuts A 0 := by
  constructor
  · rintro ⟨B, hB⟩
    exact hB.cuts
  · intro _
    exact ⟨0, zero_isTransport hA⟩

/-- A partial transport can leave some marginal demand unsatisfied. -/
def IsPartialTransport {n : ℕ} (A : Board n n) (q : ℝ) (B : Board n n) : Prop :=
  (∀ i j, 0 ≤ B i j) ∧ (∀ i j, B i j ≤ A i j) ∧
    (∀ i, rowSum B i ≤ q) ∧ (∀ j, colSum B j ≤ q)

theorem IsTransport.isPartialTransport {n : ℕ} {A B : Board n n} {q : ℝ}
    (h : IsTransport A q B) : IsPartialTransport A q B :=
  ⟨h.1, h.2.1, fun i => (h.2.2.1 i).le, fun j => (h.2.2.2 j).le⟩

theorem zero_isPartialTransport {n : ℕ} {A : Board n n} {q : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hq : 0 ≤ q) : IsPartialTransport A q 0 := by
  exact ⟨by simp, hA, fun _ => by simpa [rowSum] using hq,
    fun _ => by simpa [colSum] using hq⟩

theorem IsPartialTransport.totalMass_le {n : ℕ} {A B : Board n n} {q : ℝ}
    (h : IsPartialTransport A q B) : totalMass B ≤ n * q := by
  calc
    _ ≤ ∑ _ : Fin n, q := Finset.sum_le_sum fun i _ => h.2.2.1 i
    _ = _ := by simp

/-- Saturating the total demand saturates every row and every column. -/
theorem IsPartialTransport.isTransport_of_totalMass_eq {n : ℕ}
    {A B : Board n n} {q : ℝ} (h : IsPartialTransport A q B)
    (hmass : totalMass B = n * q) : IsTransport A q B := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · have hsum : ∑ i : Fin n, (q - rowSum B i) = 0 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      change n * q - totalMass B = 0
      rw [hmass, sub_self]
    have heach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sub_nonneg.mpr (h.2.2.1 i))).mp hsum
    intro i
    have hi := heach i (Finset.mem_univ i)
    linarith
  · have hsum : ∑ j : Fin n, (q - colSum B j) = 0 := by
      simp [Finset.sum_sub_distrib, ← totalMass_eq_sum_colSum, hmass]
    have heach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sub_nonneg.mpr (h.2.2.2 j))).mp hsum
    intro j
    have hj := heach j (Finset.mem_univ j)
    linarith

theorem IsTransport.totalMass {n : ℕ} {A B : Board n n} {q : ℝ}
    (h : IsTransport A q B) : totalMass B = n * q := by
  simp [DittertRybin.totalMass, h.2.2.1]

theorem transport_iff_partial_totalMass {n : ℕ} (A : Board n n) (q : ℝ) :
    (∃ B, IsTransport A q B) ↔
      ∃ B, IsPartialTransport A q B ∧ totalMass B = n * q := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, hB.isPartialTransport, hB.totalMass⟩
  · rintro ⟨B, hB, hmass⟩
    exact ⟨B, hB.isTransport_of_totalMass_eq hmass⟩

theorem continuous_rowSum {m n : ℕ} (i : Fin m) :
    Continuous (fun B : Board m n => rowSum B i) := by
  unfold rowSum
  fun_prop

theorem continuous_colSum {m n : ℕ} (j : Fin n) :
    Continuous (fun B : Board m n => colSum B j) := by
  unfold colSum
  fun_prop

theorem continuous_totalMass {m n : ℕ} :
    Continuous (fun B : Board m n => totalMass B) := by
  unfold totalMass rowSum
  fun_prop

/-- Real capacities need no integrality assumption: bounded partial transports
form a compact set in a finite-dimensional real matrix space. -/
theorem isCompact_partialTransport {n : ℕ} (A : Board n n) (q : ℝ) :
    IsCompact {B | IsPartialTransport A q B} := by
  have hrows : IsClosed {B : Board n n | ∀ i, rowSum B i ≤ q} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (continuous_rowSum i) continuous_const
  have hcols : IsClosed {B : Board n n | ∀ j, colSum B j ≤ q} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (continuous_colSum j) continuous_const
  let box : Set (Board n n) := {B | ∀ i j, B i j ∈ Set.Icc 0 (A i j)}
  have hbox : IsCompact box := by
    change IsCompact {B : Fin n → Fin n → ℝ | ∀ i j, B i j ∈ Set.Icc 0 (A i j)}
    exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc
  have hset : {B | IsPartialTransport A q B} = box ∩
        ({B | ∀ i, rowSum B i ≤ q} ∩ {B | ∀ j, colSum B j ≤ q}) := by
    ext B
    change ((∀ i j, 0 ≤ B i j) ∧ (∀ i j, B i j ≤ A i j) ∧
      (∀ i, rowSum B i ≤ q) ∧ (∀ j, colSum B j ≤ q)) ↔
      (∀ i j, 0 ≤ B i j ∧ B i j ≤ A i j) ∧
        (∀ i, rowSum B i ≤ q) ∧ (∀ j, colSum B j ≤ q)
    constructor
    · rintro ⟨h0, hA, hr, hc⟩
      exact ⟨fun i j => ⟨h0 i j, hA i j⟩, hr, hc⟩
    · rintro ⟨hB, hr, hc⟩
      exact ⟨fun i j => (hB i j).1, fun i j => (hB i j).2, hr, hc⟩
  rw [hset]
  exact hbox.inter_right (hrows.inter hcols)

/-- There is a partial transport of maximal total mass. No rational-capacity
or algorithm-termination hypothesis is used. -/
theorem exists_maximal_partialTransport {n : ℕ} {A : Board n n} {q : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hq : 0 ≤ q) :
    ∃ B, IsPartialTransport A q B ∧
      ∀ C, IsPartialTransport A q C → totalMass C ≤ totalMass B := by
  obtain ⟨B, hB, hmax⟩ := (isCompact_partialTransport A q).exists_isMaxOn
    ⟨0, zero_isPartialTransport hA hq⟩ continuous_totalMass.continuousOn
  exact ⟨B, hB, fun C hC => hmax hC⟩

/-- A secondary objective distinguishing partial transports of equal mass. -/
def rowEnergy {n : ℕ} (B : Board n n) : ℝ := ∑ i, (rowSum B i) ^ 2

theorem continuous_rowEnergy {n : ℕ} :
    Continuous (fun B : Board n n => rowEnergy B) := by
  unfold rowEnergy rowSum
  fun_prop

/-- First maximize transported mass, then minimize squared row sums. -/
def IsOptimalPartialTransport {n : ℕ} (A : Board n n) (q : ℝ)
    (B : Board n n) : Prop :=
  IsPartialTransport A q B ∧
    (∀ C, IsPartialTransport A q C → totalMass C ≤ totalMass B) ∧
    (∀ C, IsPartialTransport A q C → totalMass C = totalMass B →
      rowEnergy B ≤ rowEnergy C)

theorem exists_optimal_partialTransport {n : ℕ} {A : Board n n} {q : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hq : 0 ≤ q) :
    ∃ B, IsOptimalPartialTransport A q B := by
  obtain ⟨B₀, hB₀, hmax₀⟩ := exists_maximal_partialTransport hA hq
  have hcompact : IsCompact {B | IsPartialTransport A q B ∧
      totalMass B = totalMass B₀} :=
    (isCompact_partialTransport A q).inter_right
      (isClosed_eq continuous_totalMass continuous_const)
  obtain ⟨B, hB, hmin⟩ := hcompact.exists_isMinOn ⟨B₀, hB₀, rfl⟩
    continuous_rowEnergy.continuousOn
  refine ⟨B, hB.1, ?_, ?_⟩
  · intro C hC
    exact (hmax₀ C hC).trans_eq hB.2.symm
  · intro C hC hmass
    exact hmin ⟨hC, hmass.trans hB.2⟩

/-- Change one cell by t. Negative changes are permitted in this algebraic definition. -/
def addCell {n : ℕ} (B : Board n n) (i j : Fin n) (t : ℝ) : Board n n :=
  fun u v => B u v + if u = i ∧ v = j then t else 0

theorem rowSum_addCell {n : ℕ} (B : Board n n) (i j u : Fin n) (t : ℝ) :
    rowSum (addCell B i j t) u = rowSum B u + if u = i then t else 0 := by
  by_cases hu : u = i <;> simp [addCell, rowSum, Finset.sum_add_distrib, hu]

theorem colSum_addCell {n : ℕ} (B : Board n n) (i j v : Fin n) (t : ℝ) :
    colSum (addCell B i j t) v = colSum B v + if v = j then t else 0 := by
  by_cases hv : v = j <;> simp [addCell, colSum, Finset.sum_add_distrib, hv]

theorem totalMass_addCell {n : ℕ} (B : Board n n) (i j : Fin n) (t : ℝ) :
    totalMass (addCell B i j t) = totalMass B + t := by
  simp [totalMass, rowSum_addCell, Finset.sum_add_distrib]

theorem rowEnergy_addCell {n : ℕ} (B : Board n n) (i j : Fin n) (t : ℝ) :
    rowEnergy (addCell B i j t) = rowEnergy B + 2 * t * rowSum B i + t ^ 2 := by
  have hrow (u : Fin n) : (rowSum (addCell B i j t) u) ^ 2 =
      (rowSum B u) ^ 2 + if u = i then 2 * t * rowSum B i + t ^ 2 else 0 := by
    rw [rowSum_addCell]
    by_cases hu : u = i
    · subst u
      simp only [↓reduceIte]
      ring
    · simp [hu]
  simp only [rowEnergy, hrow, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  ring

/-- Move t from row l to row i inside column j. -/
def shiftCell {n : ℕ} (B : Board n n) (i l j : Fin n) (t : ℝ) : Board n n :=
  addCell (addCell B i j t) l j (-t)

theorem rowSum_shiftCell {n : ℕ} (B : Board n n) (i l j u : Fin n) (t : ℝ) :
    rowSum (shiftCell B i l j t) u =
      rowSum B u + (if u = i then t else 0) + (if u = l then -t else 0) := by
  simp only [shiftCell, rowSum_addCell]

theorem colSum_shiftCell {n : ℕ} (B : Board n n) (i l j v : Fin n) (t : ℝ) :
    colSum (shiftCell B i l j t) v = colSum B v := by
  simp only [shiftCell, colSum_addCell]
  by_cases hv : v = j <;> simp [hv]

theorem totalMass_shiftCell {n : ℕ} (B : Board n n) (i l j : Fin n) (t : ℝ) :
    totalMass (shiftCell B i l j t) = totalMass B := by
  simp [shiftCell, totalMass_addCell]

theorem rowEnergy_shiftCell {n : ℕ} (B : Board n n) (i l j : Fin n) (t : ℝ)
    (hil : i ≠ l) : rowEnergy (shiftCell B i l j t) =
      rowEnergy B + 2 * t * (rowSum B i - rowSum B l + t) := by
  simp only [shiftCell, rowEnergy_addCell, rowSum_addCell, Ne.symm hil,
    ↓reduceIte, add_zero]
  ring

theorem IsPartialTransport.addCell {n : ℕ} {A B : Board n n} {q : ℝ}
    (h : IsPartialTransport A q B) (i j : Fin n) {t : ℝ}
    (ht : 0 ≤ t) (hcap : t ≤ A i j - B i j)
    (hrow : t ≤ q - rowSum B i) (hcol : t ≤ q - colSum B j) :
    IsPartialTransport A q (addCell B i j t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    by_cases hc : u = i ∧ v = j
    · rcases hc with ⟨hu, hv⟩
      subst u
      subst v
      simpa [DittertRybin.addCell] using add_nonneg (h.1 i j) ht
    · simpa only [DittertRybin.addCell, if_neg hc, add_zero] using h.1 u v
  · intro u v
    by_cases hc : u = i ∧ v = j
    · rcases hc with ⟨hu, hv⟩
      subst u
      subst v
      simp only [DittertRybin.addCell, and_self, ↓reduceIte]
      linarith
    · simpa only [DittertRybin.addCell, if_neg hc, add_zero] using h.2.1 u v
  · intro u
    rw [rowSum_addCell]
    by_cases hu : u = i
    · subst u
      simp only [↓reduceIte]
      linarith
    · simpa [hu] using h.2.2.1 u
  · intro v
    rw [colSum_addCell]
    by_cases hv : v = j
    · subst v
      simp only [↓reduceIte]
      linarith
    · simpa [hv] using h.2.2.2 v

theorem IsPartialTransport.shiftCell {n : ℕ} {A B : Board n n} {q : ℝ}
    (h : IsPartialTransport A q B) (i l j : Fin n) (hil : i ≠ l) {t : ℝ}
    (ht : 0 ≤ t) (hcap : t ≤ A i j - B i j) (hdonor : t ≤ B l j)
    (hrow : t ≤ q - rowSum B i) : IsPartialTransport A q (shiftCell B i l j t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    by_cases hc : u = i ∧ v = j
    · rcases hc with ⟨hu, hv⟩
      subst u
      subst v
      simp only [DittertRybin.shiftCell, DittertRybin.addCell, hil, false_and,
        and_self, ↓reduceIte, add_zero]
      exact add_nonneg (h.1 i j) ht
    · by_cases hd : u = l ∧ v = j
      · rcases hd with ⟨hu, hv⟩
        subst u
        subst v
        simp only [DittertRybin.shiftCell, DittertRybin.addCell, Ne.symm hil,
          false_and, and_self, ↓reduceIte, add_zero]
        linarith
      · simpa only [DittertRybin.shiftCell, DittertRybin.addCell, if_neg hc,
          if_neg hd, add_zero] using h.1 u v
  · intro u v
    by_cases hc : u = i ∧ v = j
    · rcases hc with ⟨hu, hv⟩
      subst u
      subst v
      simp only [DittertRybin.shiftCell, DittertRybin.addCell, hil, false_and,
        and_self, ↓reduceIte, add_zero]
      linarith
    · by_cases hd : u = l ∧ v = j
      · rcases hd with ⟨hu, hv⟩
        subst u
        subst v
        simp only [DittertRybin.shiftCell, DittertRybin.addCell, Ne.symm hil,
          false_and, and_self, ↓reduceIte, add_zero]
        linarith [h.2.1 l j]
      · simpa only [DittertRybin.shiftCell, DittertRybin.addCell, if_neg hc,
          if_neg hd, add_zero] using h.2.1 u v
  · intro u
    rw [rowSum_shiftCell]
    by_cases hu : u = i
    · subst u
      simp only [hil, ↓reduceIte, add_zero]
      linarith
    · by_cases hl : u = l
      · subst u
        simp only [Ne.symm hil, ↓reduceIte, add_zero]
        linarith [h.2.2.1 l]
      · simpa [hu, hl] using h.2.2.1 u
  · intro v
    rw [colSum_shiftCell]
    exact h.2.2.2 v

private theorem exists_pos_lt_three {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : ∃ t, 0 < t ∧ t < a ∧ t < b ∧ t < c := by
  obtain ⟨t, ht0, ht⟩ := exists_between (lt_min ha (lt_min hb hc))
  exact ⟨t, ht0, (lt_min_iff.mp ht).1, (lt_min_iff.mp (lt_min_iff.mp ht).2).1,
    (lt_min_iff.mp (lt_min_iff.mp ht).2).2⟩

/-- A slack edge from a deficient row can only end in a full column,
otherwise a one-cell augmentation increases total transported mass. -/
theorem IsOptimalPartialTransport.full_col_of_slack {n : ℕ}
    {A B : Board n n} {q : ℝ} (h : IsOptimalPartialTransport A q B)
    (i j : Fin n) (hrow : rowSum B i < q) (hcap : B i j < A i j) :
    colSum B j = q := by
  apply le_antisymm (h.1.2.2.2 j)
  by_contra! hcol
  obtain ⟨t, ht, htrow, htcap, htcol⟩ := exists_pos_lt_three
    (sub_pos.mpr hrow) (sub_pos.mpr hcap) (sub_pos.mpr hcol)
  have hnew := h.1.addCell i j ht.le htcap.le htrow.le htcol.le
  have hmass := h.2.1 _ hnew
  rw [totalMass_addCell] at hmass
  linarith

/-- In a column reachable from a deficient row through a slack edge,
every full row contributes zero mass. Otherwise an equal-mass two-cell shift
strictly lowers the secondary row energy. -/
theorem IsOptimalPartialTransport.zero_of_full_row_slack {n : ℕ}
    {A B : Board n n} {q : ℝ} (h : IsOptimalPartialTransport A q B)
    (i l j : Fin n) (hrow : rowSum B i < q) (hfull : rowSum B l = q)
    (hcap : B i j < A i j) : B l j = 0 := by
  apply le_antisymm _ (h.1.1 l j)
  by_contra! hdonor
  have hil : i ≠ l := by
    intro heq
    subst l
    linarith
  obtain ⟨t, ht, htrow, htcap, htdonor⟩ := exists_pos_lt_three
    (sub_pos.mpr hrow) (sub_pos.mpr hcap) hdonor
  have hnew := h.1.shiftCell i l j hil ht.le htcap.le htdonor.le htrow.le
  have henergy := h.2.2 _ hnew (totalMass_shiftCell B i l j t)
  rw [rowEnergy_shiftCell B i l j t hil, hfull] at henergy
  have hneg : 2 * t * (rowSum B i - q + t) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

/-- The cut inequalities force every optimal partial transport to meet all
demand. The proof uses the secondary row energy to produce a deficient cut
from any deficient row; no general flow theorem is assumed. -/
theorem IsOptimalPartialTransport.isTransport_of_cuts {n : ℕ}
    {A B : Board n n} {q : ℝ} (h : IsOptimalPartialTransport A q B)
    (hcuts : TransportCuts A q) : IsTransport A q B := by
  classical
  have hrows (i₀ : Fin n) : rowSum B i₀ = q := by
    apply le_antisymm (h.1.2.2.1 i₀)
    by_contra! hdef
    let I : Finset (Fin n) := Finset.univ.filter (fun i => rowSum B i < q)
    let T : Finset (Fin n) := Finset.univ.filter (fun j => ∃ i ∈ I, B i j < A i j)
    have hi₀ : i₀ ∈ I := by simp [I, hdef]
    have hI (i : Fin n) (hi : i ∈ I) : rowSum B i < q :=
      (Finset.mem_filter.mp hi).2
    have hT (j : Fin n) (hj : j ∈ T) : colSum B j = q := by
      obtain ⟨i, hi, hij⟩ := (Finset.mem_filter.mp hj).2
      exact h.full_col_of_slack i j (hI i hi) hij
    have hzero (i j : Fin n) (hi : i ∈ Iᶜ) (hj : j ∈ T) : B i j = 0 := by
      have hnot : ¬ rowSum B i < q := by
        simpa [I] using (Finset.mem_compl.mp hi)
      have hfull : rowSum B i = q := le_antisymm (h.1.2.2.1 i) (not_lt.mp hnot)
      obtain ⟨l, hl, hlj⟩ := (Finset.mem_filter.mp hj).2
      exact h.zero_of_full_row_slack l i j (hI l hl) hfull hlj
    have hsat (i j : Fin n) (hi : i ∈ I) (hj : j ∈ Tᶜ) : B i j = A i j := by
      apply le_antisymm (h.1.2.1 i j)
      by_contra! hlt
      have hmem : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hi, hlt⟩
      exact (Finset.mem_compl.mp hj) hmem
    have hzeroMass : cutMass B Iᶜ T = 0 := by
      exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => hzero i j hi hj
    have hsatMass : cutMass B I Tᶜ = cutMass A I Tᶜ := by
      exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hsat i j hi hj
    have hfullMass : cutMass B I T = (T.card : ℝ) * q := by
      have hc := cutMass_add_compl_rows B I T
      rw [hzeroMass, add_zero] at hc
      calc
        _ = ∑ j ∈ T, colSum B j := hc
        _ = ∑ _j ∈ T, q := Finset.sum_congr rfl fun j hj => hT j hj
        _ = _ := by simp
    have hstrict : (∑ i ∈ I, rowSum B i) < (I.card : ℝ) * q := by
      calc
        _ < ∑ _i ∈ I, q := Finset.sum_lt_sum
          (fun i hi => (hI i hi).le) ⟨i₀, hi₀, hdef⟩
        _ = _ := by simp
    have hsplit := cutMass_add_compl_cols B I T
    rw [hfullMass, hsatMass] at hsplit
    have hcard : (Tᶜ.card : ℝ) = n - (T.card : ℝ) := by
      have hsum : (T.card : ℝ) + (Tᶜ.card : ℝ) = n := by
        exact_mod_cast (show T.card + Tᶜ.card = n by simp)
      linarith
    have hcut := hcuts I Tᶜ
    rw [hcard] at hcut
    nlinarith
  apply h.1.isTransport_of_totalMass_eq
  simp [DittertRybin.totalMass, hrows]

/-- Finite real-capacity transport criterion, including n=0 and q=0. -/
theorem transport_iff_cuts {n : ℕ} {A : Board n n} {q : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hq : 0 ≤ q) :
    (∃ B, IsTransport A q B) ↔ TransportCuts A q := by
  constructor
  · rintro ⟨B, hB⟩
    exact hB.cuts
  · intro hcuts
    obtain ⟨B, hB⟩ := exists_optimal_partialTransport hA hq
    exact ⟨B, hB.isTransport_of_cuts hcuts⟩

/-- Matrix form of the cut criterion used by the square spectral argument. -/
theorem exists_doublyStochastic_dominated_of_cuts {n : ℕ}
    {A : Board n n} {q : ℝ} (hA : ∀ i j, 0 ≤ A i j) (hq : 0 ≤ q)
    (hcuts : TransportCuts A q) :
    ∃ B ∈ doublyStochastic ℝ (Fin n), ∀ i j, q * B i j ≤ A i j := by
  obtain ⟨C, hC⟩ := (transport_iff_cuts hA hq).mpr hcuts
  obtain ⟨B, hB, hCB⟩ := (exists_mem_doublyStochastic_eq_smul_iff hq).mpr
    ⟨hC.1, hC.2.2.1, hC.2.2.2⟩
  refine ⟨B, hB, ?_⟩
  intro i j
  have hle := hC.2.1 i j
  simpa only [hCB, Matrix.smul_apply, smul_eq_mul] using hle

end DittertRybin
