import DR.Square.OrderFourOrbitCoverage
import DR.Certificates.SpectralFour
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Sym

/-!
# The quantitative bound for every physical multiplier matrix

Sorting is only a representative choice for an unordered multiset. The
finite coverage theorem gives an actual seed and actual physical permutation,
and the semantic conjugacy theorem transports the seed's quadratic bound.
-/

namespace DittertRybin

open Certificates
open scoped BigOperators

set_option maxRecDepth 10000

theorem orderFour_quadraticValue_submatrix (Q : Matrix (Fin 16) (Fin 16) ℝ)
    (e : Equiv.Perm (Fin 16)) (x : Fin 16 → ℝ) :
    quadraticValue (Q.submatrix e e) (fun i => x (e i)) = quadraticValue Q x := by
  unfold quadraticValue
  conv_rhs => rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [← Equiv.sum_comp e]
  rfl

theorem orderFourMultiplierMatrix_lower_of_orbit
    (m : Vector ℕ 4) (s : Fin 33) (r c : Equiv.Perm (Fin 4))
    (hm : ((spectralFourMultipliers.get s).map (orderFourCellMapNat r c)).toList.Perm m.toList)
    (x : Fin 16 → ℝ) :
    (1/10:ℝ)*((∑ i, x i^2)-(∑ i, x i)^2/16) ≤
      quadraticValue ((orderFourMultiplierMatrix m).map (fun q : ℚ => (q : ℝ))) x := by
  have hmat := orderFourMultiplierMatrix_physical r c (spectralFourMultipliers.get s)
  rw [orderFourMultiplierMatrix_perm hm, orderFourMultiplierMatrix_seed] at hmat
  let e := orderFourPhysicalPermutation r c
  have hreal : (((orderFourMultiplierMatrix m).map (fun q : ℚ => (q : ℝ))).submatrix e e) =
      (spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ)) := by
    funext i j
    exact congrArg (Rat.castHom ℝ) (congrFun (congrFun hmat i) j)
  have h := spectralFourSeedMatrix_lower s (fun i => x (e i))
  rw [← hreal, orderFour_quadraticValue_submatrix] at h
  simpa only [Equiv.sum_comp e (fun i => x i^2), Equiv.sum_comp e x] using h

/-- The sorted physical representative of an unordered four-cell multiplier. -/
def orderFourSortedMultiplier (s : Sym (Fin 16) 4) : Vector ℕ 4 :=
  ⟨((s.val.sort (· ≤ ·)).map Fin.val).toArray, by simp⟩

theorem orderFourSortedMultiplier_toList (s : Sym (Fin 16) 4) :
    (orderFourSortedMultiplier s).toList = (s.val.sort (· ≤ ·)).map Fin.val := by
  simp [orderFourSortedMultiplier]

theorem orderFourSortedMultiplier_orbit (s : Sym (Fin 16) 4) :
    ∃ (t : Fin 33) (r c : Equiv.Perm (Fin 4)),
      ((spectralFourMultipliers.get t).map (orderFourCellMapNat r c)).toList.Perm
        (orderFourSortedMultiplier s).toList := by
  have hlen : (s.val.sort (· ≤ ·)).length = 4 := by simp
  obtain ⟨a,b,c,d,habcd⟩ := List.length_eq_four.mp hlen
  have hsort := Multiset.pairwise_sort (s := s.val) (· ≤ ·)
  rw [habcd] at hsort
  simp at hsort
  let w := orderFourOrbitWitness a b c d
  refine ⟨w.1, orderFourLabelPermutation w.2.1, orderFourLabelPermutation w.2.2, ?_⟩
  have h := orderFourOrbitCoverage a b c d hsort.1.1 hsort.2.1.1 hsort.2.2
  simpa only [orderFourSortedMultiplier_toList, habcd, List.map_cons, List.map_nil,
    orderFourOrbitWitnessValid, w] using h

theorem orderFourSortedMultiplier_lower (s : Sym (Fin 16) 4) (x : Fin 16 → ℝ) :
    (1/10:ℝ)*((∑ i, x i^2)-(∑ i, x i)^2/16) ≤
      quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
        (fun q : ℚ => (q : ℝ))) x := by
  obtain ⟨t,r,c,h⟩ := orderFourSortedMultiplier_orbit s
  exact orderFourMultiplierMatrix_lower_of_orbit _ t r c h x

end DittertRybin
