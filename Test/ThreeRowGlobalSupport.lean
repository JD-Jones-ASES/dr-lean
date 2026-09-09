import DR.Rectangular.ThreeRowFullColumn

namespace DittertRybin.Tests

-- A doubleton requires two positive entries; a merely permitted zero mask does not suffice.
example : ¬ ThreeRowDoublet (fun (_ : Fin 3) (_ : Fin 1) => (0 : ℝ)) 0 0 := by
  norm_num [ThreeRowDoublet]

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (i : Fin 3) (c : Fin n) : ¬ ThreeRowSingleton P i c :=
  fun h => hmax.threeRow_no_singleton hP hn i c h

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (c : Fin n) : ThreeRowFullColumn P c ∨ ∃ i, ThreeRowDoublet P i c :=
  hmax.threeRow_columns_full_or_doublet hP hn c

-- The bound is on the number of physical columns, with no multiplicity cap assumed.
example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (hcols : ∀ c, ∃ i, ThreeRowDoublet P i c) : n ≤ 3 :=
  hmax.threeRow_doublet_only_dimension hP hn hcols

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) : ∃ c, ∀ r, 0 < P r c := hmax.threeRow_exists_full_column hP hn

example {m : ℕ} {P : Board m 3} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hm : 3 ≤ m) : ∃ r, ∀ c, 0 < P r c := hmax.threeColumn_exists_full_row hP hm

#print axioms IsSeparationGlobalMax.threeRow_no_singleton
#print axioms IsSeparationGlobalMax.threeRow_doublet_only_dimension
#print axioms IsSeparationGlobalMax.threeRow_not_doublet_only
#print axioms IsSeparationGlobalMax.threeRow_exists_full_column
end DittertRybin.Tests
