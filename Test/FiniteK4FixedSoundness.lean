import DR.Certificates.FiniteK4FixedSoundness

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

-- The omitted ordinary/ordinary coordinate uses both multiplicities.
example : (finiteK4FixedWeight 5 5 9
    (fourRowFiniteSeedCompressedEquiv 9 (.inr (),.inr ())) : ℝ)=4 := by
  rw [finiteK4FixedWeight_reindex]
  change ((5-3:ℕ):ℝ)*((5-3:ℕ):ℝ)=4
  norm_num
example : (finiteK4FixedWeight 20 20 9
    (fourRowFiniteSeedCompressedEquiv 9 (.inr (),.inr ())) : ℝ)=289 := by
  rw [finiteK4FixedWeight_reindex]
  change ((20-3:ℕ):ℝ)*((20-3:ℕ):ℝ)=289
  norm_num

private def seedZeroCoordinate : Fin (fourRowFiniteSeedFullSize 0) := ⟨0,by decide +kernel⟩

-- Arbitrary coefficient inputs need not be positive: a distinguished diagonal
-- entry in the actual matrix can already be negative.
example : finiteK4FixedFullMatrix (fun _ => (-1:ℝ)) 5 5 0 seedZeroCoordinate seedZeroCoordinate = -1 := by
  rfl
example : ¬(finiteK4FixedFullMatrix (fun _ => (-1:ℝ)) 5 5 0).PosSemidef := by
  intro h
  have hd := h.diag_nonneg (i:=seedZeroCoordinate)
  change 0≤(-1:ℝ) at hd
  norm_num at hd

-- Strict positivity of the known omitted weight follows at every actual index.
example (s : Fin 10) (i : Fin (fourRowFiniteSeedFullSize s)) :
    (finiteK4FixedWeight 5 20 s i : ℝ)≠0 :=
  (finiteK4FixedWeight_pos (by decide) (by decide) s i).ne'

#print axioms finiteK4FixedWeight_pos
#print axioms finiteK4FixedFullMatrix_isSymm
#print axioms finiteK4FixedFullMatrix_criterion
#print axioms finiteK4FixedTrivial_criterion
#print axioms finiteK4FixedSeed_criterion
#print axioms finiteK4Fixed_uniformMaximizer
end DittertRybin.Tests
