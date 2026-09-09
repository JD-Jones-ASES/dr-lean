import DR.Square.WeightedSweep
import Mathlib.Data.Fintype.EquivFin

/-! Transport the finite weighted sweep along genuine equivalences of vertex sets. -/

namespace DittertRybin

open scoped BigOperators

theorem sweepMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (π f : β → ℝ) : sweepMean (π ∘ e) (f ∘ e) = sweepMean π f :=
  Equiv.sum_comp e (fun v => π v * f v)

theorem sweepVariance_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (π f : β → ℝ) : sweepVariance (π ∘ e) (f ∘ e) = sweepVariance π f := by
  unfold sweepVariance
  rw [sweepMean_equiv]
  exact Equiv.sum_comp e (fun v => π v * (f v - sweepMean π f) ^ 2)

theorem sweepEnergy_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (c : β → β → ℝ) (f : β → ℝ) :
    sweepEnergy (fun i j => c (e i) (e j)) (f ∘ e) = sweepEnergy c f := by
  unfold sweepEnergy
  congr 1
  apply Fintype.sum_equiv e
  intro i
  exact Equiv.sum_comp e (fun j => c (e i) j * (f (e i) - f j) ^ 2)

theorem sweepMass_equiv {α β : Type*} (e : α ≃ β) (π : β → ℝ) (S : Finset α) :
    sweepMass π (S.map e.toEmbedding) = sweepMass (π ∘ e) S := by simp [sweepMass]

theorem sweepBoundary_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (c : β → β → ℝ) (S : Finset α) :
    sweepBoundary (fun i j => c (e i) (e j)) S = sweepBoundary c (S.map e.toEmbedding) := by
  rw [sweepBoundary_eq_sum_ite, sweepBoundary_eq_sum_ite]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp

/-- The sweep theorem on any finite vertex type, with the actual cardinality in its factor. -/
theorem exists_weighted_sweep_cut_fintype {α : Type*} [Fintype α] [DecidableEq α]
    (hN : 2 ≤ Fintype.card α) (π : α → ℝ) (hπpos : ∀ v, 0 < π v) (hπ : ∑ v, π v = 1)
    (c : α → α → ℝ) (hc0 : ∀ v w, 0 ≤ c v w) (hcsym : ∀ v w, c v w = c w v)
    (f : α → ℝ) (hV : 0 < sweepVariance π f) :
    ∃ S : Finset α, S.Nonempty ∧ S ≠ Finset.univ ∧ sweepMass π S ≤ 1 / 2 ∧
      sweepBoundary c S ≤ ((Fintype.card α - 1 : ℕ) : ℝ) * sweepEnergy c f / (4 * sweepVariance π f) := by
  let e := (Fintype.equivFin α).symm
  have hπsum : ∑ v, (π ∘ e) v = 1 := (Equiv.sum_comp e π).trans hπ
  have hV' : 0 < sweepVariance (π ∘ e) (f ∘ e) := by rwa [sweepVariance_equiv]
  obtain ⟨T, hT, hproper, hmass, hbound⟩ := exists_weighted_sweep_cut hN (π ∘ e)
    (fun v => hπpos (e v)) hπsum (fun v w => c (e v) (e w))
    (fun v w => hc0 (e v) (e w)) (fun v w => hcsym (e v) (e w)) (f ∘ e) hV'
  refine ⟨T.map e.toEmbedding, Finset.map_nonempty.mpr hT, ?_, ?_, ?_⟩
  · intro h
    apply hproper
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi : e i ∈ T.map e.toEmbedding := h ▸ Finset.mem_univ _
    simpa using hi
  · rwa [sweepMass_equiv]
  · rw [← sweepBoundary_equiv]
    simpa only [sweepEnergy_equiv, sweepVariance_equiv] using hbound

end DittertRybin
