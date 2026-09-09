import DR.Certificates.TwoAxisOrdinarySoundness

/-! Exact constant-kernel transport, including absent ordinary sectors. -/
namespace DittertRybin.Certificates
open scoped BigOperators
noncomputable section
variable {α β ρ γ : Type*}

private theorem quadratic_nonneg_zero_or_posDef {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) (h : v = 0 ∨ M.PosDef) :
    0 ≤ quadraticValue M v := by
  rcases h with h | h
  · simp [h,quadraticValue]
  · simpa only [quadraticValue_eq_dotProduct,star_trivial] using
      h.posSemidef.dotProduct_mulVec_nonneg v

private theorem vector_zero_of_nonpos_zero_or_posDef {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) (h : v = 0 ∨ M.PosDef)
    (hle : quadraticValue M v ≤ 0) : v = 0 := by
  rcases h with h | h
  · exact h
  · by_contra hn
    have hp : 0 < quadraticValue M v := by
      simpa only [quadraticValue_eq_dotProduct,star_trivial] using h.dotProduct_mulVec_pos hn
    linarith

variable [Fintype α] [Fintype β] [Fintype ρ] [Fintype γ] [DecidableEq ρ] [DecidableEq γ]

/-- Vanishing of the full quadratic forces every present standard component to vanish. -/
theorem twoAxis_zero_structure
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K)
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (hC : (Fintype.card γ : ℝ) ≠ 0)
    (hT : (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ)).PosSemidef)
    (hRow : Fintype.card ρ = 1 ∨ (twoAxisRowStandardMatrix K (Fintype.card γ)).PosDef)
    (hCol : Fintype.card γ = 1 ∨ (twoAxisColumnStandardMatrix K (Fintype.card ρ)).PosDef)
    (hInter : Fintype.card ρ = 1 ∨ Fintype.card γ = 1 ∨ 0 < twoAxisInteraction K)
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (hz : quadraticValue (twoAxisOrdinaryMatrix K) p = 0) :
    quadraticValue (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ))
        (twoAxisAggregateVector p) = 0 ∧
      (∀ r, twoAxisRowFluctuationAggregate p r = 0) ∧
      (∀ c, twoAxisColumnFluctuationAggregate p c = 0) ∧
      ∀ r c, twoAxisInteractionFluctuation p r c = 0 := by
  classical
  let a := quadraticValue (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ))
    (twoAxisAggregateVector p)
  let b (r : ρ) := quadraticValue (twoAxisRowStandardMatrix K (Fintype.card γ))
    (twoAxisRowFluctuationAggregate p r)
  let c (j : γ) := quadraticValue (twoAxisColumnStandardMatrix K (Fintype.card ρ))
    (twoAxisColumnFluctuationAggregate p j)
  let d (r : ρ) (j : γ) := twoAxisInteraction K*(twoAxisInteractionFluctuation p r j)^2
  have hr (r : ρ) : twoAxisRowFluctuationAggregate p r = 0 ∨
      (twoAxisRowStandardMatrix K (Fintype.card γ)).PosDef :=
    hRow.imp_left fun h => twoAxisRowFluctuationAggregate_zero_of_card_one h p r
  have hc (j : γ) : twoAxisColumnFluctuationAggregate p j = 0 ∨
      (twoAxisColumnStandardMatrix K (Fintype.card ρ)).PosDef :=
    hCol.imp_left fun h => twoAxisColumnFluctuationAggregate_zero_of_card_one h p j
  have hi (r : ρ) (j : γ) : twoAxisInteractionFluctuation p r j = 0 ∨ 0 < twoAxisInteraction K := by
    rcases hInter with h | h | h
    · exact Or.inl (twoAxisInteractionFluctuation_zero_of_row_card_one h p r j)
    · exact Or.inl (twoAxisInteractionFluctuation_zero_of_column_card_one h p r j)
    · exact Or.inr h
  have ha : 0 ≤ a := by
    simpa only [a,quadraticValue_eq_dotProduct,star_trivial] using
      hT.dotProduct_mulVec_nonneg (twoAxisAggregateVector p)
  have hb (r : ρ) : 0 ≤ b r := quadratic_nonneg_zero_or_posDef _ _ (hr r)
  have hcn (j : γ) : 0 ≤ c j := quadratic_nonneg_zero_or_posDef _ _ (hc j)
  have hd (r : ρ) (j : γ) : 0 ≤ d r j := by
    rcases hi r j with h | h
    · simp [d,h]
    · exact mul_nonneg h.le (sq_nonneg _)
  have hbs : 0 ≤ ∑ r, b r := Finset.sum_nonneg fun r _ => hb r
  have hcs : 0 ≤ ∑ j, c j := Finset.sum_nonneg fun j _ => hcn j
  have hds : 0 ≤ ∑ r, ∑ j, d r j :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun j _ => hd r j
  have he : a + (∑ j, c j) + (∑ r, b r) + (∑ r, ∑ j, d r j) = 0 := by
    have h := quadraticValue_twoAxis_decomposition K hK hR hC p
    rw [hz] at h
    exact h.symm
  refine ⟨le_antisymm (by linarith) ha, ?_, ?_, ?_⟩
  · intro r
    apply vector_zero_of_nonpos_zero_or_posDef _ _ (hr r)
    have hh := Finset.single_le_sum (fun s _ => hb s) (Finset.mem_univ r)
    change b r ≤ 0
    linarith
  · intro j
    apply vector_zero_of_nonpos_zero_or_posDef _ _ (hc j)
    have hh := Finset.single_le_sum (fun s _ => hcn s) (Finset.mem_univ j)
    change c j ≤ 0
    linarith
  · intro r j
    rcases hi r j with h | h
    · exact h
    · have hs1 := Finset.single_le_sum (fun s _ => hd r s) (Finset.mem_univ j)
      have hs2 : (∑ k, d r k) ≤ ∑ s, ∑ k, d s k := Finset.single_le_sum
        (fun s _ => Finset.sum_nonneg fun k _ => hd s k) (Finset.mem_univ r)
      have hle : d r j ≤ 0 := by linarith
      have hw : (twoAxisInteractionFluctuation p r j)^2 ≤ 0 :=
        nonpos_of_mul_nonpos_right hle h
      exact sq_eq_zero_iff.mp (le_antisymm hw (sq_nonneg _))

omit [Fintype α] [Fintype β] [DecidableEq ρ] [DecidableEq γ] in
/-- Sum coordinates and zero centered coordinates reconstruct every physical entry. -/
theorem twoAxis_constant_of_aggregate_fluctuations
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (hC : (Fintype.card γ : ℝ) ≠ 0)
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) (t : ℝ)
    (hA : ∀ q, twoAxisAggregateVector p q =
      t*twoAxisAggregateWeight (Fintype.card ρ) (Fintype.card γ) q)
    (hRow : ∀ r, twoAxisRowFluctuationAggregate p r = 0)
    (hCol : ∀ c, twoAxisColumnFluctuationAggregate p c = 0)
    (hInter : ∀ r c, twoAxisInteractionFluctuation p r c = 0) :
    ∀ q, p q = t := by
  have hw (r : ρ) (j : β ⊕ γ) : ordinaryPairFluctuation p r j = 0 := by
    cases j with
    | inl j => exact congrFun (hRow r) (.inl j)
    | inr c =>
      have hi := hInter r c
      have hs := congrFun (hRow r) (.inr ())
      change (∑ d, ordinaryPairFluctuation p r (.inr d)) = 0 at hs
      change ordinaryPairFluctuation p r (.inr c) -
        (∑ d, ordinaryPairFluctuation p r (.inr d))/(Fintype.card γ : ℝ) = 0 at hi
      simpa only [hs,zero_div,sub_zero] using hi
  have hz (i : α ⊕ Unit) (j : β ⊕ γ) : ordinaryPairAggregateVector p (i,j) =
      t*ordinaryAxisWeight (Fintype.card ρ) i := by
    cases j with
    | inl j =>
      simpa only [twoAxisAggregateVector,ordinaryColumnAggregateVector,
        twoAxisAggregateWeight,ordinaryAxisWeight,mul_one] using hA (i,.inl j)
    | inr c =>
      have hi := congrFun (hCol c) i
      have hs : (∑ d, ordinaryPairAggregateVector p (i,.inr d)) =
          (t*ordinaryAxisWeight (Fintype.card ρ) i)*(Fintype.card γ : ℝ) := by
        simpa only [twoAxisAggregateVector,ordinaryColumnAggregateVector,
          twoAxisAggregateWeight,ordinaryAxisWeight,mul_assoc] using hA (i,.inr ())
      change ordinaryPairAggregateVector p (i,.inr c) -
        (∑ d, ordinaryPairAggregateVector p (i,.inr d))/(Fintype.card γ : ℝ) = 0 at hi
      rw [hs,mul_div_cancel_right₀ _ hC] at hi
      exact sub_eq_zero.mp hi
  intro q
  rcases q with ⟨i,j⟩
  cases i with
  | inl i => simpa only [ordinaryPairAggregateVector,ordinaryAxisWeight,mul_one] using hz (.inl i) j
  | inr r =>
    have hi := hw r j
    have hs := hz (.inr ()) j
    change (∑ s, p (.inr s,j)) = t*(Fintype.card ρ : ℝ) at hs
    change p (.inr r,j) - (∑ s, p (.inr s,j))/(Fintype.card ρ : ℝ) = 0 at hi
    rw [hs,mul_div_cancel_right₀ _ hR] at hi
    exact sub_eq_zero.mp hi

omit [Fintype α] [Fintype β] [DecidableEq ρ] [DecidableEq γ] in
theorem twoAxis_constant_fluctuations
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (hC : (Fintype.card γ : ℝ) ≠ 0) (t : ℝ) :
    (∀ r : ρ, twoAxisRowFluctuationAggregate (α := α) (β := β) (γ := γ) (fun _ => t) r = 0) ∧
      (∀ c : γ, twoAxisColumnFluctuationAggregate (α := α) (β := β) (ρ := ρ) (fun _ => t) c = 0) ∧
      ∀ (r : ρ) (c : γ), twoAxisInteractionFluctuation (α := α) (β := β) (fun _ => t) r c = 0 := by
  have hr (r : ρ) : ordinaryPairFluctuation (α := α) (β := β ⊕ γ) (fun _ => t) r = 0 := by
    funext j
    simp only [ordinaryPairFluctuation,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      mul_div_cancel_left₀ t hR,sub_self,Pi.zero_apply]
  refine ⟨?_,?_,?_⟩
  · intro r
    unfold twoAxisRowFluctuationAggregate
    rw [hr]
    funext j
    cases j <;> simp [ordinaryScalarAggregateVector]
  · intro c
    funext i
    cases i <;>
      simp only [twoAxisColumnFluctuationAggregate,ordinaryColumnFluctuation,
        ordinaryPairAggregateVector,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        mul_div_cancel_left₀ _ hC,sub_self,Pi.zero_apply]
  · intro r c
    unfold twoAxisInteractionFluctuation
    rw [hr]
    simp [ordinaryScalarFluctuation]

/-- The weighted trivial kernel is precisely the constant kernel of the full matrix. -/
theorem twoAxisOrdinaryMatrix_constant_kernel
    (K : OrdinaryPair α → OrdinaryPair β → ℝ) (hK : TwoAxisOrdinarySymm K)
    (hR : (Fintype.card ρ : ℝ) ≠ 0) (hC : (Fintype.card γ : ℝ) ≠ 0)
    (hT : (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ)).PosSemidef)
    (hRow : Fintype.card ρ = 1 ∨ (twoAxisRowStandardMatrix K (Fintype.card γ)).PosDef)
    (hCol : Fintype.card γ = 1 ∨ (twoAxisColumnStandardMatrix K (Fintype.card ρ)).PosDef)
    (hInter : Fintype.card ρ = 1 ∨ Fintype.card γ = 1 ∨ 0 < twoAxisInteraction K)
    (hkernel : ∀ z : (α ⊕ Unit) × (β ⊕ Unit) → ℝ,
      quadraticValue (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ)) z = 0 ↔
        ∃ t : ℝ, ∀ q, z q = t*twoAxisAggregateWeight (Fintype.card ρ) (Fintype.card γ) q)
    (p : (α ⊕ ρ) × (β ⊕ γ) → ℝ) :
    quadraticValue (twoAxisOrdinaryMatrix K) p = 0 ↔ ∃ t : ℝ, ∀ q, p q = t := by
  constructor
  · intro hz
    obtain ⟨ha,hr,hc,hi⟩ := twoAxis_zero_structure K hK hR hC hT hRow hCol hInter p hz
    obtain ⟨t,ht⟩ := (hkernel _).mp ha
    exact ⟨t,twoAxis_constant_of_aggregate_fluctuations hR hC p t ht hr hc hi⟩
  · rintro ⟨t,hp⟩
    have he : p = fun _ => t := funext hp
    rw [he]
    obtain ⟨hr,hc,hi⟩ := twoAxis_constant_fluctuations (α := α) (β := β) hR hC t
    have ha : quadraticValue (twoAxisTrivialMatrix K (Fintype.card ρ) (Fintype.card γ))
        (twoAxisAggregateVector (fun _ : (α ⊕ ρ) × (β ⊕ γ) => t)) = 0 :=
      (hkernel _).mpr ⟨t,fun q => twoAxisAggregateVector_constant t q⟩
    rw [quadraticValue_twoAxis_decomposition K hK hR hC,ha]
    simp only [hr,hc,hi,quadraticValue,Pi.zero_apply,zero_mul,mul_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0),Finset.sum_const_zero,add_zero]

end
end DittertRybin.Certificates
