import DR.Certificates.FiniteFiveTuplePattern
import DR.Certificates.TupleLabelPermutation
import DR.Rectangular.FourRowFiniteRole

/-! Equality-pattern compression for the actual quintic multiplier-triple
role formula. The ambient natural labels and their magnitude are arbitrary. -/

namespace DittertRybin.Certificates

noncomputable section

def finiteK4TupleRoleKey (cells : Fin 5 → ℕ × ℕ) : ℕ :=
  fourRowFiniteCanonicalRoleKey [cells 0, cells 1, cells 2] (cells 3) (cells 4)

theorem finiteK4TupleRoleKey_congr (s t : Fin 5 → ℕ × ℕ)
    (hr : ∀ i j, (s i).1 = (s j).1 ↔ (t i).1 = (t j).1)
    (hc : ∀ i j, (s i).2 = (s j).2 ↔ (t i).2 = (t j).2) :
    finiteK4TupleRoleKey s = finiteK4TupleRoleKey t := by
  obtain ⟨r, hρ⟩ := tupleLabelPermutation (fun i => (s i).1) (fun i => (t i).1) hr
  obtain ⟨c, hκ⟩ := tupleLabelPermutation (fun i => (s i).2) (fun i => (t i).2) hc
  have he (i : Fin 5) : Prod.map r c (s i) = t i := Prod.ext (hρ i) (hκ i)
  symm
  simpa only [List.map_cons, List.map_nil, he, finiteK4TupleRoleKey] using
    fourRowFiniteCanonicalRoleKey_map r c r.injective c.injective
      [s 0, s 1, s 2] (s 3) (s 4)

def finiteK4PatternCell (r c : Fin 52) (i : Fin 5) : ℕ × ℕ :=
  ((fiveTuplePatterns r i).val, (fiveTuplePatterns c i).val)

/-- Every physical five-cell role is one of the complete 52-by-52 pattern pairs. -/
theorem finiteK4TupleRoleKey_compress (s : Fin 5 → ℕ × ℕ) :
    finiteK4TupleRoleKey s = finiteK4TupleRoleKey
      (finiteK4PatternCell (fiveTuplePatternIndex (fun i => (s i).1))
        (fiveTuplePatternIndex (fun i => (s i).2))) := by
  apply finiteK4TupleRoleKey_congr
  · intro i j
    exact (fiveTuplePatternIndex_eq_iff (fun i => (s i).1) i j).symm.trans Fin.ext_iff
  · intro i j
    exact (fiveTuplePatternIndex_eq_iff (fun i => (s i).2) i j).symm.trans Fin.ext_iff

end
end DittertRybin.Certificates
