import DR.Rectangular.ThreeRowSingleDoubletNormal

namespace DittertRybin.Tests

-- Arbitrary physical positions, signed weights, and zero entries are retained in the formulas.
example : rowSum (threeRowSingleDoubletBoard (0 : Fin 3) ({0,2} : Finset (Fin 4)) (-1) 2 3) 0 = 4 := by
  rw [rowSum_threeRowSingleDoubletBoard, if_pos rfl]
  have hc : (({0,2} : Finset (Fin 4))ᶜ).card = 2 := by decide
  rw [hc]
  norm_num

example : rowSum (threeRowSingleDoubletBoard (0 : Fin 3) ({0,2} : Finset (Fin 4)) (-1) 2 3) 1 = 4 := by
  norm_num [rowSum_threeRowSingleDoubletBoard, Fin.ext_iff, Finset.card_compl]

example : threeRowPair (threeRowSingleDoubletBoard (0 : Fin 3) ({0} : Finset (Fin 3)) 1 2 3) 0 = 19 := by
  have h := (threeRowPair_threeRowSingleDoubletBoard (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) ({0} : Finset (Fin 3)) 1 2 3).1
  norm_num [Finset.card_compl] at h
  exact h

example : threeRowPair (threeRowSingleDoubletBoard (0 : Fin 3) ({0} : Finset (Fin 3)) 1 2 3) 1 = 12 := by
  have h := (threeRowPair_threeRowSingleDoubletBoard (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) ({0} : Finset (Fin 3)) 1 2 3).2
  norm_num [Finset.card_compl] at h
  exact h

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (i : Fin 3) (a : Fin n) (ha : ThreeRowDoublet P i a)
    (htypes : ∀ r j, ThreeRowDoublet P r j → r = i) : False :=
  hmax.threeRow_not_single_doublet_type hP hn i a ha htypes

#print axioms IsSeparationGlobalMax.threeRow_single_doublet_board_kkt
#print axioms IsSeparationGlobalMax.threeRow_single_doublet_representative
#print axioms IsSeparationGlobalMax.threeRow_not_single_doublet_type
end DittertRybin.Tests
