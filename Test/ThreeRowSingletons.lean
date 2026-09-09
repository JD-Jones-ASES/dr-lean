import DR.Rectangular.ThreeRowSingletons

namespace DittertRybin.Tests

-- Both actual zeros are essential to the singleton classification.
example : ThreeRowSingleton (fun i (_ : Fin 1) => if i.val = 0 then (1 : ℝ) else 0) 0 0 := by
  norm_num [ThreeRowSingleton]

example : ¬ ThreeRowSingleton (fun (_ : Fin 3) (_ : Fin 1) => (1 : ℝ)) 0 0 := by
  norm_num [ThreeRowSingleton]

-- The third residual row cannot be discarded: at z=0 the two scalar conditions can hold.
example : ((1 : ℝ) + 0 + 0) * (2 - 1) = (1 + 0) * 1 ∧
    0 ≤ (1 + 0) * (2 - 1) - (1 + 0 + 0) * 1 := by norm_num

example {a b c x y z : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z)
    (heq : (x + y + z) * (a - b) = (x + y) * c) :
    ¬ 0 ≤ (x + y) * (a - b) - (x + y + z) * c :=
  fun h => threeRow_singleton_containing_pair_impossible hc hx hy hz heq h

-- These exclusions leave all other columns unrestricted.
example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (i h : Fin 3) (a b : Fin n) (ha : ThreeRowSingleton P i a) (hb : ThreeRowSingleton P h b) :
    i = h := hmax.threeRow_singleton_rows_eq hP i h a b ha hb

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (i h : Fin 3) (hih : i ≠ h) (a b : Fin n) (ha : ThreeRowSingleton P i a)
    (hb : ThreeRowDoublet P h b) : False :=
  hmax.threeRow_no_singleton_containing_doublet hP i h hih a b ha hb

example {n : ℕ} {P : Board 3 n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3)
    (hn : 3 ≤ n) (i : Fin 3) (a b : Fin n) (ha : ThreeRowSingleton P i a) :
    ThreeRowSingleton P i b ∨ ThreeRowDoublet P i b ∨ ThreeRowFullColumn P b :=
  hmax.threeRow_supports_of_singleton hP hn i a ha b

#print axioms IsSeparationGlobalMax.threeRow_singleton_rows_eq
#print axioms IsSeparationGlobalMax.threeRow_no_singleton_containing_doublet
#print axioms IsSeparationGlobalMax.threeRow_supports_of_singleton
end DittertRybin.Tests
