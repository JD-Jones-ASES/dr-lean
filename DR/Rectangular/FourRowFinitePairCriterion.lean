import DR.Rectangular.FourRowFinitePairIndex
import DR.Rectangular.FourRowFiniteSeedKernelEvaluation
import DR.Certificates.TwoAxisOrdinaryKernel
import DR.Certificates.PrincipalKernel

/-! The checked principal blocks and full weighted kernel give the exact
trivial-sector criterion. All matrices here retain their actual entries. -/

namespace DittertRybin
open Certificates
noncomputable section

theorem fourRowFiniteSeedTrivial_isSymm (s : Fin 10) (R C : ℝ) (h : ℕ → ℝ) :
    (twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s h) R C).IsSymm := by
  apply Matrix.IsSymm.ext
  intro p q
  unfold twoAxisTrivialMatrix
  rw [ordinaryPairAverage_swap]
  apply congrArg (fun f => ordinaryPairAverage R f p.1 q.1)
  funext r
  rw [ordinaryPairAverage_swap]
  apply congrArg (fun f => ordinaryPairAverage C f p.2 q.2)
  funext c
  exact fourRowFiniteSeedRelationKernel_symm s h r c

theorem fourRowFiniteSeedFullMatrix_isSymm (s : Fin 10) (N : ℝ) (h : ℕ → ℝ)
    (hR : (4 : ℝ)-fourRowFiniteSeedRows s ≠ 0)
    (hC : N-fourRowFiniteSeedColumns s ≠ 0) :
    (fourRowFiniteSeedFullMatrix s N h).IsSymm := by
  have hs := (fourRowFiniteSeedTrivial_isSymm s (4-fourRowFiniteSeedRows s)
    (N-fourRowFiniteSeedColumns s) h).submatrix (fourRowFiniteSeedCompressedEquiv s).symm
  rw [← fourRowFiniteSeedFullMatrix_reindex s N h hR hC] at hs
  have he : ((fourRowFiniteSeedFullMatrix s N h).submatrix
      (fourRowFiniteSeedCompressedEquiv s) (fourRowFiniteSeedCompressedEquiv s)).submatrix
      (fourRowFiniteSeedCompressedEquiv s).symm (fourRowFiniteSeedCompressedEquiv s).symm =
      fourRowFiniteSeedFullMatrix s N h := by
    ext i j
    simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
  rw [he] at hs
  exact hs

theorem fourRowFiniteSeedFullMatrix_criterion (s : Fin 10) (N : ℝ) (h : ℕ → ℝ)
    (hN : 3 < N)
    (hk : (fourRowFiniteSeedFullMatrix s N h).mulVec
      (fun j => fourRowFiniteSeedWeight s N j.val) = 0)
    (hp : (fourRowFiniteSeedTrivialMatrix s N h).PosDef) :
    (fourRowFiniteSeedFullMatrix s N h).PosSemidef ∧
      ∀ x : Fin (fourRowFiniteSeedFullSize s) → ℝ,
        quadraticValue (fourRowFiniteSeedFullMatrix s N h) x = 0 ↔
          ∃ t : ℝ, ∀ i, x i = t*fourRowFiniteSeedWeight s N i.val := by
  have hr : (fourRowFiniteSeedRows s : ℝ) ≤ 3 := by
    exact_mod_cast (fourRowFiniteSeed_counts s).2.2.1
  have hc : (fourRowFiniteSeedColumns s : ℝ) ≤ 3 := by
    exact_mod_cast (fourRowFiniteSeed_counts s).2.2.2.2
  have hn : 1 ≤ fourRowFiniteSeedFullSize s := by
    unfold fourRowFiniteSeedFullSize
    exact Nat.mul_pos (by omega) (by omega)
  let e : Fin (fourRowFiniteSeedFullSize s-1+1) ≃ Fin (fourRowFiniteSeedFullSize s) :=
    finCongr (Nat.sub_add_cancel hn)
  apply principal_kernel_criterion (fourRowFiniteSeedFullMatrix s N h)
    (fourRowFiniteSeedFullMatrix_isSymm s N h (by linarith) (by linarith))
    (fun j => fourRowFiniteSeedWeight s N j.val) hk e
  · exact (fourRowFiniteSeedWeight_pos s hN _).ne'
  · exact hp

theorem fourRowFiniteSeedTrivial_criterion (s : Fin 10) (N : ℝ) (h : ℕ → ℝ)
    (hN : 3 < N)
    (hk : (fourRowFiniteSeedFullMatrix s N h).mulVec
      (fun j => fourRowFiniteSeedWeight s N j.val) = 0)
    (hp : (fourRowFiniteSeedTrivialMatrix s N h).PosDef) :
    (twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s h)
      (4-fourRowFiniteSeedRows s) (N-fourRowFiniteSeedColumns s)).PosSemidef ∧
      ∀ x : (Fin (fourRowFiniteSeedRows s) ⊕ Unit) ×
        (Fin (fourRowFiniteSeedColumns s) ⊕ Unit) → ℝ,
        quadraticValue (twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s h)
          (4-fourRowFiniteSeedRows s) (N-fourRowFiniteSeedColumns s)) x = 0 ↔
          ∃ t : ℝ, ∀ i, x i = t*twoAxisAggregateWeight
            (4-fourRowFiniteSeedRows s) (N-fourRowFiniteSeedColumns s) i := by
  have hr : (fourRowFiniteSeedRows s : ℝ) ≤ 3 := by
    exact_mod_cast (fourRowFiniteSeed_counts s).2.2.1
  have hc : (fourRowFiniteSeedColumns s : ℝ) ≤ 3 := by
    exact_mod_cast (fourRowFiniteSeed_counts s).2.2.2.2
  have he := fourRowFiniteSeedFullMatrix_reindex s N h (by linarith) (by linarith)
  obtain ⟨hq,hker⟩ := fourRowFiniteSeedFullMatrix_criterion s N h hN hk hp
  rw [← he]
  refine ⟨hq.submatrix _,?_⟩
  intro x
  rw [quadraticValue_submatrix_equiv,hker]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t,fun i => ?_⟩
    simpa only [Equiv.symm_apply_apply,fourRowFiniteSeedWeight_reindex]
      using ht (fourRowFiniteSeedCompressedEquiv s i)
  · rintro ⟨t,ht⟩
    refine ⟨t,fun i => ?_⟩
    have hh := ht ((fourRowFiniteSeedCompressedEquiv s).symm i)
    rw [← fourRowFiniteSeedWeight_reindex,Equiv.apply_symm_apply] at hh
    exact hh

end
end DittertRybin
