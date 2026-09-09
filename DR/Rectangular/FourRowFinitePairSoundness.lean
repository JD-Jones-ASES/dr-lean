import DR.Rectangular.FourRowFinitePairCriterion

/-! The actual seed block conditions imply PSD and exactly the constant
kernel on the full distinguished/ordinary physical product. -/

namespace DittertRybin
open Certificates
noncomputable section

theorem fourRowFiniteSeedRelation_criterion {N : ℕ} (hN : 5 ≤ N)
    (s : Fin 10) (h : ℕ → ℝ)
    (hk : (fourRowFiniteSeedFullMatrix s N h).mulVec
      (fun j => fourRowFiniteSeedWeight s N j.val) = 0)
    (hp : (fourRowFiniteSeedTrivialMatrix s N h).PosDef)
    (hrow : fourRowFiniteSeedRows s < 3 → (fourRowFiniteSeedRowMatrix s N h).PosDef)
    (hcol : (fourRowFiniteSeedColumnMatrix s h).PosDef)
    (hinter : fourRowFiniteSeedRows s < 3 →
      (fourRowFiniteSeedInteractionMatrix s h).PosDef) :
    (twoAxisOrdinaryMatrix (ρ := Fin (4-fourRowFiniteSeedRows s))
      (γ := Fin (N-fourRowFiniteSeedColumns s)) (fourRowFiniteSeedRelationKernel s h)).PosSemidef ∧
      ∀ x : (Fin (fourRowFiniteSeedRows s) ⊕ Fin (4-fourRowFiniteSeedRows s)) ×
        (Fin (fourRowFiniteSeedColumns s) ⊕ Fin (N-fourRowFiniteSeedColumns s)) → ℝ,
        quadraticValue (twoAxisOrdinaryMatrix (fourRowFiniteSeedRelationKernel s h)) x = 0 ↔
          ∃ t : ℝ, ∀ i, x i = t := by
  have hnr := (fourRowFiniteSeed_counts s).2.2.1
  have hnc := (fourRowFiniteSeed_counts s).2.2.2.2
  have hnr' : (fourRowFiniteSeedRows s : ℝ) ≤ 3 := by exact_mod_cast hnr
  have hnc' : (fourRowFiniteSeedColumns s : ℝ) ≤ 3 := by exact_mod_cast hnc
  have hN' : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have hRcast : ((4-fourRowFiniteSeedRows s : ℕ) : ℝ) = 4-fourRowFiniteSeedRows s := by
    rw [Nat.cast_sub (by omega),Nat.cast_ofNat]
  have hCcast : ((N-fourRowFiniteSeedColumns s : ℕ) : ℝ) = (N : ℝ)-fourRowFiniteSeedColumns s := by
    rw [Nat.cast_sub (by omega)]
  have hR : (Fintype.card (Fin (4-fourRowFiniteSeedRows s)) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin,hRcast]
    linarith
  have hC : (Fintype.card (Fin (N-fourRowFiniteSeedColumns s)) : ℝ) ≠ 0 := by
    rw [Fintype.card_fin,hCcast]
    linarith
  obtain ⟨hT,hTK⟩ := fourRowFiniteSeedTrivial_criterion s N h (by linarith) hk hp
  have hRow : Fintype.card (Fin (4-fourRowFiniteSeedRows s)) = 1 ∨
      (twoAxisRowStandardMatrix (fourRowFiniteSeedRelationKernel s h)
        (Fintype.card (Fin (N-fourRowFiniteSeedColumns s)))).PosDef := by
    by_cases hr : fourRowFiniteSeedRows s < 3
    · right
      rw [Fintype.card_fin,hCcast,←fourRowFiniteSeedRowMatrix_reindex s N h (by linarith)]
      exact (hrow hr).submatrix (fourRowFiniteCompressedEquiv _).injective
    · left
      simp only [Fintype.card_fin]
      omega
  have hCol : Fintype.card (Fin (N-fourRowFiniteSeedColumns s)) = 1 ∨
      (twoAxisColumnStandardMatrix (fourRowFiniteSeedRelationKernel s h)
        (Fintype.card (Fin (4-fourRowFiniteSeedRows s)))).PosDef := by
    right
    rw [Fintype.card_fin,hRcast,←fourRowFiniteSeedColumnMatrix_reindex s h (by linarith)]
    exact hcol.submatrix (fourRowFiniteCompressedEquiv _).injective
  have hInter : Fintype.card (Fin (4-fourRowFiniteSeedRows s)) = 1 ∨
      Fintype.card (Fin (N-fourRowFiniteSeedColumns s)) = 1 ∨
        0 < twoAxisInteraction (fourRowFiniteSeedRelationKernel s h) := by
    by_cases hr : fourRowFiniteSeedRows s < 3
    · right; right
      rw [fourRowFiniteSeedRelation_interaction]
      have hv := (hinter hr).diag_pos (i := (0 : Fin 1))
      exact hv
    · left
      simp only [Fintype.card_fin]
      omega
  have hT' : (twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s h)
      (Fintype.card (Fin (4-fourRowFiniteSeedRows s)))
      (Fintype.card (Fin (N-fourRowFiniteSeedColumns s)))).PosSemidef := by
    simpa only [Fintype.card_fin,hRcast,hCcast] using hT
  refine ⟨twoAxisOrdinaryMatrix_posSemidef _ (fourRowFiniteSeedRelationKernel_symm s h)
    hR hC hT' (hRow.imp_right Matrix.PosDef.posSemidef)
      (hCol.imp_right Matrix.PosDef.posSemidef) (hInter.imp_right (Or.imp_right le_of_lt)),?_⟩
  intro x
  apply twoAxisOrdinaryMatrix_constant_kernel _ (fourRowFiniteSeedRelationKernel_symm s h)
    hR hC hT' hRow hCol hInter
  simpa only [Fintype.card_fin,hRcast,hCcast] using hTK

end
end DittertRybin
