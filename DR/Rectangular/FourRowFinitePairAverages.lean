import DR.Rectangular.FourRowFinitePairModel

/-! The pair-relation averages are the literal seed block entries. -/

namespace DittertRybin
open Certificates
noncomputable section

def fourRowFiniteCompressedLabel {r : ℕ} : Fin r ⊕ Unit → ℕ
  | .inl i => i.val
  | .inr _ => r

theorem fourRowFinitePairAverage_eq {r : ℕ} (ell : ℝ) (hell : ell ≠ 0)
    (f : ℕ → ℕ → ℝ) (i j : Fin r ⊕ Unit) :
    ordinaryPairAverage ell (fun p => f (fourRowFinitePairLabels p).1
      (fourRowFinitePairLabels p).2) i j =
      fourRowFiniteOrdinaryAverage r ell f
        (fourRowFiniteCompressedLabel i) (fourRowFiniteCompressedLabel j) := by
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [ordinaryPairAverage, fourRowFinitePairLabels,
        fourRowFiniteCompressedLabel, fourRowFiniteOrdinaryAverage, Nat.ne_of_lt i.isLt]
    | inr j => simp [ordinaryPairAverage, fourRowFinitePairLabels,
        fourRowFiniteCompressedLabel, fourRowFiniteOrdinaryAverage, Nat.ne_of_lt i.isLt]
  | inr i =>
    cases j with
    | inl j => simp [ordinaryPairAverage, fourRowFinitePairLabels,
        fourRowFiniteCompressedLabel, fourRowFiniteOrdinaryAverage, Nat.ne_of_lt j.isLt]
    | inr j =>
      simp only [ordinaryPairAverage, fourRowFinitePairLabels, fourRowFiniteCompressedLabel,
        fourRowFiniteOrdinaryAverage, and_self, ite_true]
      field_simp
      ring

theorem fourRowFiniteSeedRelation_trivial (s : Fin 10) (N : ℝ) (h : ℕ → ℝ)
    (hR : (4 : ℝ)-fourRowFiniteSeedRows s ≠ 0)
    (hC : N-fourRowFiniteSeedColumns s ≠ 0)
    (p q : (Fin (fourRowFiniteSeedRows s) ⊕ Unit) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Unit)) :
    twoAxisTrivialMatrix (fourRowFiniteSeedRelationKernel s h)
      (4-fourRowFiniteSeedRows s) (N-fourRowFiniteSeedColumns s) p q =
      fourRowFiniteTrivialEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
        N h (fourRowFiniteSeedMark s)
        (fourRowFiniteCompressedLabel p.1,fourRowFiniteCompressedLabel p.2)
        (fourRowFiniteCompressedLabel q.1,fourRowFiniteCompressedLabel q.2) := by
  unfold twoAxisTrivialMatrix
  trans ordinaryPairAverage (4-fourRowFiniteSeedRows s)
    (fun r => fourRowFiniteOrdinaryAverage (fourRowFiniteSeedColumns s)
      (N-fourRowFiniteSeedColumns s)
      (fun j l => fourRowFiniteRealRoleEntry h (fourRowFiniteSeedMark s)
        ((fourRowFinitePairLabels r).1,j) ((fourRowFinitePairLabels r).2,l))
      (fourRowFiniteCompressedLabel p.2) (fourRowFiniteCompressedLabel q.2)) p.1 q.1
  · apply congrArg (fun f => ordinaryPairAverage (4-fourRowFiniteSeedRows s) f p.1 q.1)
    funext r
    exact fourRowFinitePairAverage_eq _ hC
      (fun j l => fourRowFiniteRealRoleEntry h (fourRowFiniteSeedMark s)
        ((fourRowFinitePairLabels r).1,j) ((fourRowFinitePairLabels r).2,l)) p.2 q.2
  · exact fourRowFinitePairAverage_eq _ hR
      (fun i k => fourRowFiniteOrdinaryAverage (fourRowFiniteSeedColumns s)
        (N-fourRowFiniteSeedColumns s)
        (fun j l => fourRowFiniteRealRoleEntry h (fourRowFiniteSeedMark s) (i,j) (k,l))
        (fourRowFiniteCompressedLabel p.2) (fourRowFiniteCompressedLabel q.2)) p.1 q.1

theorem fourRowFiniteSeedRelation_row (s : Fin 10) (N : ℝ) (h : ℕ → ℝ)
    (hC : N-fourRowFiniteSeedColumns s ≠ 0)
    (p q : Fin (fourRowFiniteSeedColumns s) ⊕ Unit) :
    twoAxisRowStandardMatrix (fourRowFiniteSeedRelationKernel s h)
      (N-fourRowFiniteSeedColumns s) p q =
      fourRowFiniteRowStandardEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
        N h (fourRowFiniteSeedMark s)
        (fourRowFiniteCompressedLabel p) (fourRowFiniteCompressedLabel q) := by
  exact fourRowFinitePairAverage_eq _ hC
    (fun k t => fourRowFiniteRealRoleEntry h (fourRowFiniteSeedMark s)
      (fourRowFiniteSeedRows s,k) (fourRowFiniteSeedRows s,t) -
      fourRowFiniteRealRoleEntry h (fourRowFiniteSeedMark s)
        (fourRowFiniteSeedRows s,k) (fourRowFiniteSeedRows s+1,t)) p q

theorem fourRowFiniteSeedRelation_column (s : Fin 10) (h : ℕ → ℝ)
    (hR : (4 : ℝ)-fourRowFiniteSeedRows s ≠ 0)
    (p q : Fin (fourRowFiniteSeedRows s) ⊕ Unit) :
    twoAxisColumnStandardMatrix (fourRowFiniteSeedRelationKernel s h)
      (4-fourRowFiniteSeedRows s) p q =
      fourRowFiniteColumnStandardEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
        h (fourRowFiniteSeedMark s)
        (fourRowFiniteCompressedLabel p) (fourRowFiniteCompressedLabel q) := by
  exact fourRowFinitePairAverage_eq _ hR
    (fun j l => fourRowFiniteRealRoleEntry h (fourRowFiniteSeedMark s)
      (j,fourRowFiniteSeedColumns s) (l,fourRowFiniteSeedColumns s) -
      fourRowFiniteRealRoleEntry h (fourRowFiniteSeedMark s)
        (j,fourRowFiniteSeedColumns s) (l,fourRowFiniteSeedColumns s+1)) p q

theorem fourRowFiniteSeedRelation_interaction (s : Fin 10) (h : ℕ → ℝ) :
    twoAxisInteraction (fourRowFiniteSeedRelationKernel s h) =
      fourRowFiniteInteractionEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
        h (fourRowFiniteSeedMark s) := rfl

end
end DittertRybin
