import DR.Rectangular.FourRowFinitePairModel

/-! Replacing an actual pair of ordinary labels by its same/different
representatives preserves the complete five-position equality pattern.
The prefix can have repeated labels; ordinary counts may be zero or one. -/
namespace DittertRybin
open Certificates

/-- Actual distinguished labels followed by the ordinary host labels. -/
def fourRowFiniteHostLabel {r R : ℕ} : Fin r ⊕ Fin R → ℕ
  | .inl i => i.val
  | .inr k => r + k.val

/-- The actual prefix and the final two physical labels. -/
def fourRowFinitePhysicalFiveLabels {r R : ℕ} (a : Fin 3 → Fin r)
    (p q : Fin r ⊕ Fin R) : Fin 5 → ℕ :=
  ![(a 0).val, (a 1).val, (a 2).val, fourRowFiniteHostLabel p, fourRowFiniteHostLabel q]

/-- The same prefix with canonical pair representatives. -/
def fourRowFiniteCompressedFiveLabels {r R : ℕ} (a : Fin 3 → Fin r)
    (p q : Fin r ⊕ Fin R) : Fin 5 → ℕ :=
  ![(a 0).val, (a 1).val, (a 2).val,
    (fourRowFinitePairLabels (ordinaryPair p q)).1,
    (fourRowFinitePairLabels (ordinaryPair p q)).2]

theorem fourRowFinitePairLabels_fst_distinguished {r R : ℕ}
    (i : Fin r) (p q : Fin r ⊕ Fin R) :
    fourRowFiniteHostLabel p = i.val ↔
      (fourRowFinitePairLabels (ordinaryPair p q)).1 = i.val := by
  cases p with
  | inl p => cases q <;> simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]
  | inr p =>
    cases q with
    | inl q => simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]; omega
    | inr q =>
      by_cases h : p = q <;>
        simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels, h] <;> omega

theorem fourRowFinitePairLabels_snd_distinguished {r R : ℕ}
    (i : Fin r) (p q : Fin r ⊕ Fin R) :
    fourRowFiniteHostLabel q = i.val ↔
      (fourRowFinitePairLabels (ordinaryPair p q)).2 = i.val := by
  cases p with
  | inl p =>
    cases q with
    | inl q => simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]
    | inr q => simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]; omega
  | inr p =>
    cases q with
    | inl q => simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]
    | inr q =>
      by_cases h : p = q <;>
        simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels, h] <;> omega

theorem fourRowFinitePairLabels_eq_iff {r R : ℕ} (p q : Fin r ⊕ Fin R) :
    fourRowFiniteHostLabel p = fourRowFiniteHostLabel q ↔
      (fourRowFinitePairLabels (ordinaryPair p q)).1 =
        (fourRowFinitePairLabels (ordinaryPair p q)).2 := by
  cases p with
  | inl p =>
    cases q with
    | inl q => simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]
    | inr q => simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]; omega
  | inr p =>
    cases q with
    | inl q => simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels]; omega
    | inr q =>
      by_cases h : p = q
      · simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels, h]
      · have hv : p.val ≠ q.val := fun he => h (Fin.ext he)
        simp [fourRowFiniteHostLabel, ordinaryPair, fourRowFinitePairLabels, h, hv]

theorem fourRowFinitePhysicalFiveLabels_eq_iff {r R : ℕ} (a : Fin 3 → Fin r)
    (p q : Fin r ⊕ Fin R) (i j : Fin 5) :
    fourRowFinitePhysicalFiveLabels a p q i = fourRowFinitePhysicalFiveLabels a p q j ↔
      fourRowFiniteCompressedFiveLabels a p q i = fourRowFiniteCompressedFiveLabels a p q j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact iff_of_true rfl rfl
    | exact Iff.rfl
    | exact fourRowFinitePairLabels_fst_distinguished _ p q
    | exact fourRowFinitePairLabels_snd_distinguished _ p q
    | exact fourRowFinitePairLabels_eq_iff p q
    | exact (eq_comm.trans (fourRowFinitePairLabels_fst_distinguished _ p q)).trans eq_comm
    | exact (eq_comm.trans (fourRowFinitePairLabels_snd_distinguished _ p q)).trans eq_comm
    | exact (eq_comm.trans (fourRowFinitePairLabels_eq_iff p q)).trans eq_comm

end DittertRybin
