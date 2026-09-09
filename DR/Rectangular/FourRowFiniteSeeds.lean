import DR.Rectangular.FourRowFiniteBlocks

/-! The ten literal multiplier triples used by the finite four-row certificates. -/

namespace DittertRybin
noncomputable section

def fourRowFiniteSeedMark : Fin 10 → List (ℕ × ℕ) :=
  ![[(0,0),(0,0),(0,0)], [(0,0),(0,0),(0,1)], [(0,0),(0,0),(1,0)],
    [(0,0),(0,0),(1,1)], [(0,0),(0,1),(0,2)], [(0,0),(0,1),(1,0)],
    [(0,0),(0,1),(1,2)], [(0,0),(1,0),(2,0)], [(0,0),(1,0),(2,1)],
    [(0,0),(1,1),(2,2)]]

def fourRowFiniteSeedRows : Fin 10 → ℕ := ![1,1,2,2,1,2,2,3,3,3]
def fourRowFiniteSeedColumns : Fin 10 → ℕ := ![1,2,1,2,3,2,3,1,2,3]

theorem fourRowFiniteSeed_counts : ∀ s : Fin 10,
    (fourRowFiniteSeedMark s).length = 3 ∧
    1 ≤ fourRowFiniteSeedRows s ∧ fourRowFiniteSeedRows s ≤ 3 ∧
    1 ≤ fourRowFiniteSeedColumns s ∧ fourRowFiniteSeedColumns s ≤ 3 := by
  decide +kernel

theorem fourRowFiniteSeed_labels : ∀ s : Fin 10,
    ((fourRowFiniteSeedMark s).map Prod.fst).toFinset = Finset.range (fourRowFiniteSeedRows s) ∧
    ((fourRowFiniteSeedMark s).map Prod.snd).toFinset = Finset.range (fourRowFiniteSeedColumns s) := by
  decide +kernel

def fourRowFiniteSeedPoint (s : Fin 10) (i : ℕ) : ℕ × ℕ :=
  (i/(fourRowFiniteSeedColumns s+1),i%(fourRowFiniteSeedColumns s+1))

def fourRowFiniteSeedFullSize (s : Fin 10) : ℕ :=
  (fourRowFiniteSeedRows s+1)*(fourRowFiniteSeedColumns s+1)

def fourRowFiniteSeedTrivialMatrix (s : Fin 10) (N : ℝ) (h : ℕ → ℝ) :
    Matrix (Fin (fourRowFiniteSeedFullSize s-1)) (Fin (fourRowFiniteSeedFullSize s-1)) ℝ :=
  fun i j => fourRowFiniteTrivialEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s) N h
    (fourRowFiniteSeedMark s) (fourRowFiniteSeedPoint s i.val) (fourRowFiniteSeedPoint s j.val)

def fourRowFiniteSeedRowMatrix (s : Fin 10) (N : ℝ) (h : ℕ → ℝ) :
    Matrix (Fin (fourRowFiniteSeedColumns s+1)) (Fin (fourRowFiniteSeedColumns s+1)) ℝ :=
  fun i j => fourRowFiniteRowStandardEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
    N h (fourRowFiniteSeedMark s) i.val j.val

def fourRowFiniteSeedColumnMatrix (s : Fin 10) (h : ℕ → ℝ) :
    Matrix (Fin (fourRowFiniteSeedRows s+1)) (Fin (fourRowFiniteSeedRows s+1)) ℝ :=
  fun i j => fourRowFiniteColumnStandardEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
    h (fourRowFiniteSeedMark s) i.val j.val

def fourRowFiniteSeedInteractionMatrix (s : Fin 10) (h : ℕ → ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => fourRowFiniteInteractionEntry (fourRowFiniteSeedRows s) (fourRowFiniteSeedColumns s)
    h (fourRowFiniteSeedMark s)

end
end DittertRybin
