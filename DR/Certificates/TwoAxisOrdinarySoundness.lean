import DR.Certificates.TwoAxisOrdinaryDecomposition

/-! Positivity and exact kernels from the literal four ordinary-axis sectors. -/
namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section
variable {α β ρ γ : Type*}

theorem ordinaryPairFluctuation_zero_of_card_one [Fintype ρ]
    (hR : Fintype.card ρ = 1) (p : (α ⊕ ρ) × β → ℝ) (r : ρ) :
    ordinaryPairFluctuation p r = 0 :=
  ordinaryColumn_fluctuation_eq_zero_of_card_one hR (fun s j => p (.inr s,j)) r

theorem twoAxisRowFluctuationAggregate_zero_of_card_one [Fintype ρ] [Fintype γ]
    (hR : Fintype.card ρ = 1) (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (r : ρ) :
    twoAxisRowFluctuationAggregate p r = 0 := by
  unfold twoAxisRowFluctuationAggregate
  rw [ordinaryPairFluctuation_zero_of_card_one hR]
  funext j
  cases j <;> simp [ordinaryScalarAggregateVector]

theorem twoAxisColumnFluctuationAggregate_zero_of_card_one [Fintype ρ] [Fintype γ]
    (hC : Fintype.card γ = 1) (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (c : γ) :
    twoAxisColumnFluctuationAggregate p c = 0 :=
  ordinaryColumn_fluctuation_eq_zero_of_card_one hC
    (fun d i => ordinaryPairAggregateVector p (i,.inr d)) c

theorem twoAxisInteractionFluctuation_zero_of_row_card_one [Fintype ρ] [Fintype γ]
    (hR : Fintype.card ρ = 1) (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (r : ρ) (c : γ) :
    twoAxisInteractionFluctuation p r c = 0 := by
  unfold twoAxisInteractionFluctuation
  rw [ordinaryPairFluctuation_zero_of_card_one hR]
  simp [ordinaryScalarFluctuation]

theorem twoAxisInteractionFluctuation_zero_of_column_card_one [Fintype ρ] [Fintype γ]
    (hC : Fintype.card γ = 1) (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (r : ρ) (c : γ) :
    twoAxisInteractionFluctuation p r c = 0 := by
  have h := ordinaryColumn_fluctuation_eq_zero_of_card_one hC
    (fun d (_ : Unit) => ordinaryPairFluctuation p r (.inr d)) c
  exact congrFun h ()

variable [Fintype α] [Fintype β] [Fintype ρ] [Fintype γ] [DecidableEq ρ] [DecidableEq γ]

theorem quadraticValue_twoAxis_nonneg
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K)
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (hC : (Fintype.card γ : ℝ) ≠ 0)
    (hT : (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ)).PosSemidef)
    (hRow : Fintype.card ρ = 1 ∨ (twoAxisRowStandardMatrix K (Fintype.card γ)).PosSemidef)
    (hCol : Fintype.card γ = 1 ∨ (twoAxisColumnStandardMatrix K (Fintype.card ρ)).PosSemidef)
    (hInter : Fintype.card ρ = 1 ∨ Fintype.card γ = 1 ∨ 0 ≤ twoAxisInteraction K)
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) :
    0 ≤ quadraticValue (twoAxisOrdinaryMatrix K) p := by
  have ht : 0 ≤ quadraticValue (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ))
      (twoAxisAggregateVector p) := by
    simpa only [quadraticValue_eq_dotProduct,star_trivial] using
      hT.dotProduct_mulVec_nonneg (twoAxisAggregateVector p)
  have hr (r : ρ) : 0 ≤ quadraticValue (twoAxisRowStandardMatrix K (Fintype.card γ))
      (twoAxisRowFluctuationAggregate p r) := by
    rcases hRow with h | h
    · rw [twoAxisRowFluctuationAggregate_zero_of_card_one h]
      simp [quadraticValue]
    · simpa only [quadraticValue_eq_dotProduct,star_trivial] using
        h.dotProduct_mulVec_nonneg (twoAxisRowFluctuationAggregate p r)
  have hc (c : γ) : 0 ≤ quadraticValue (twoAxisColumnStandardMatrix K (Fintype.card ρ))
      (twoAxisColumnFluctuationAggregate p c) := by
    rcases hCol with h | h
    · rw [twoAxisColumnFluctuationAggregate_zero_of_card_one h]
      simp [quadraticValue]
    · simpa only [quadraticValue_eq_dotProduct,star_trivial] using
        h.dotProduct_mulVec_nonneg (twoAxisColumnFluctuationAggregate p c)
  have hi (r : ρ) (c : γ) : 0 ≤ twoAxisInteraction K*(twoAxisInteractionFluctuation p r c)^2 := by
    rcases hInter with h | h | h
    · rw [twoAxisInteractionFluctuation_zero_of_row_card_one h]
      simp
    · rw [twoAxisInteractionFluctuation_zero_of_column_card_one h]
      simp
    · exact mul_nonneg h (sq_nonneg _)
  rw [quadraticValue_twoAxis_decomposition K hK hR hC p]
  exact add_nonneg (add_nonneg (add_nonneg ht (Finset.sum_nonneg fun c _ => hc c))
    (Finset.sum_nonneg fun r _ => hr r))
    (Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun c _ => hi r c)

/-- All four small sectors imply PSD on the complete physical matrix. -/
theorem twoAxisOrdinaryMatrix_posSemidef
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K)
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (hC : (Fintype.card γ : ℝ) ≠ 0)
    (hT : (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ)).PosSemidef)
    (hRow : Fintype.card ρ = 1 ∨ (twoAxisRowStandardMatrix K (Fintype.card γ)).PosSemidef)
    (hCol : Fintype.card γ = 1 ∨ (twoAxisColumnStandardMatrix K (Fintype.card ρ)).PosSemidef)
    (hInter : Fintype.card ρ = 1 ∨ Fintype.card γ = 1 ∨ 0 ≤ twoAxisInteraction K) :
    (twoAxisOrdinaryMatrix (ρ := ρ) (γ := γ) K).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (twoAxisOrdinaryMatrix_isSymm K hK))
  intro p
  simpa only [quadraticValue_eq_dotProduct,star_trivial] using
    quadraticValue_twoAxis_nonneg K hK hR hC hT hRow hCol hInter p

end
end DittertRybin.Certificates
