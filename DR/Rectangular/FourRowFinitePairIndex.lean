import DR.Rectangular.FourRowFinitePairAverages
import DR.Rectangular.FourRowFiniteSeedKernel
import Mathlib.Logic.Equiv.Fin.Basic

/-! Explicit lexicographic indices for the actual compressed seed matrices. -/

namespace DittertRybin
open Certificates
noncomputable section

def fourRowFiniteCompressedEquiv (r : ℕ) : Fin r ⊕ Unit ≃ Fin (r+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv

theorem fourRowFiniteCompressedEquiv_val {r : ℕ} (p : Fin r ⊕ Unit) :
    (fourRowFiniteCompressedEquiv r p).val = fourRowFiniteCompressedLabel p := by
  cases p <;> simp [fourRowFiniteCompressedEquiv, fourRowFiniteCompressedLabel,
    finSumFinEquiv, finOneEquiv]

def fourRowFiniteSeedCompressedEquiv (s : Fin 10) :
    ((Fin (fourRowFiniteSeedRows s) ⊕ Unit) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Unit)) ≃ Fin (fourRowFiniteSeedFullSize s) :=
  (Equiv.prodCongr (fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s))
    (fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s))).trans finProdFinEquiv

theorem fourRowFiniteSeedCompressedEquiv_point (s : Fin 10)
    (p : (Fin (fourRowFiniteSeedRows s) ⊕ Unit) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Unit)) :
    fourRowFiniteSeedPoint s (fourRowFiniteSeedCompressedEquiv s p).val =
      (fourRowFiniteCompressedLabel p.1,fourRowFiniteCompressedLabel p.2) := by
  have he := finProdFinEquiv.symm_apply_apply
    (fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s) p.1,
      fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s) p.2)
  have hv := congrArg (fun q : Fin (fourRowFiniteSeedRows s+1) ×
      Fin (fourRowFiniteSeedColumns s+1) => (q.1.val,q.2.val)) he
  change fourRowFiniteSeedPoint s (fourRowFiniteSeedCompressedEquiv s p).val =
    ((fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s) p.1).val,
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s) p.2).val) at hv
  simpa only [fourRowFiniteCompressedEquiv_val] using hv

theorem fourRowFiniteSeedFullMatrix_reindex (s : Fin 10) (N : ℝ) (h : ℕ → ℝ)
    (hR : (4 : ℝ)-fourRowFiniteSeedRows s ≠ 0)
    (hC : N-fourRowFiniteSeedColumns s ≠ 0) :
    (fourRowFiniteSeedFullMatrix s N h).submatrix
      (fourRowFiniteSeedCompressedEquiv s) (fourRowFiniteSeedCompressedEquiv s) =
      twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s h)
        (4-fourRowFiniteSeedRows s) (N-fourRowFiniteSeedColumns s) := by
  ext p q
  simp only [Matrix.submatrix,fourRowFiniteSeedFullMatrix,fourRowFiniteSeedCompressedEquiv_point]
  exact (fourRowFiniteSeedRelation_trivial s N h hR hC p q).symm

theorem fourRowFiniteSeedRowMatrix_reindex (s : Fin 10) (N : ℝ) (h : ℕ → ℝ)
    (hC : N-fourRowFiniteSeedColumns s ≠ 0) :
    (fourRowFiniteSeedRowMatrix s N h).submatrix
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s))
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedColumns s)) =
      twoAxisRowStandardMatrix (fourRowFiniteSeedRelationKernel s h)
        (N-fourRowFiniteSeedColumns s) := by
  ext p q
  simp only [Matrix.submatrix,fourRowFiniteSeedRowMatrix,fourRowFiniteCompressedEquiv_val]
  exact (fourRowFiniteSeedRelation_row s N h hC p q).symm

theorem fourRowFiniteSeedColumnMatrix_reindex (s : Fin 10) (h : ℕ → ℝ)
    (hR : (4 : ℝ)-fourRowFiniteSeedRows s ≠ 0) :
    (fourRowFiniteSeedColumnMatrix s h).submatrix
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s))
      (fourRowFiniteCompressedEquiv (fourRowFiniteSeedRows s)) =
      twoAxisColumnStandardMatrix (fourRowFiniteSeedRelationKernel s h)
        (4-fourRowFiniteSeedRows s) := by
  ext p q
  simp only [Matrix.submatrix,fourRowFiniteSeedColumnMatrix,fourRowFiniteCompressedEquiv_val]
  exact (fourRowFiniteSeedRelation_column s h hR p q).symm

theorem fourRowFiniteSeedWeight_reindex (s : Fin 10) (N : ℝ)
    (p : (Fin (fourRowFiniteSeedRows s) ⊕ Unit) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Unit)) :
    fourRowFiniteSeedWeight s N (fourRowFiniteSeedCompressedEquiv s p).val =
      twoAxisAggregateWeight (4-fourRowFiniteSeedRows s) (N-fourRowFiniteSeedColumns s) p := by
  unfold fourRowFiniteSeedWeight fourRowFiniteSeedRowWeight
  rw [fourRowFiniteSeedCompressedEquiv_point]
  rcases p with ⟨i,j⟩
  cases i <;> cases j <;>
    simp [fourRowFiniteCompressedLabel,twoAxisAggregateWeight,ordinaryAxisWeight,
      Nat.ne_of_lt]

end
end DittertRybin
