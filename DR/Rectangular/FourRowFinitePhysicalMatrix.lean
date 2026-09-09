import DR.Rectangular.FourRowFinitePhysicalIndex
import DR.Rectangular.FourRowFinitePhysicalPattern
import DR.Certificates.FiniteK4SeedTransport

/-! The actual finite-role matrix is precisely the ordinary-pair seed matrix
after the explicit permutation of its physical host indices. -/

namespace DittertRybin
open Certificates
noncomputable section

theorem fourRowFinitePhysicalAxisEquiv_val {m r : ℕ} (hr : r ≤ m)
    (p : Fin r ⊕ Fin (m-r)) :
    (fourRowFinitePhysicalAxisEquiv hr p).val = fourRowFiniteHostLabel p := by
  cases p <;> rfl

theorem fourRowFiniteSeedRole_physical {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (s : Fin 10)
    (p q : (Fin (fourRowFiniteSeedRows s) ⊕ Fin (m-fourRowFiniteSeedRows s)) ×
      (Fin (fourRowFiniteSeedColumns s) ⊕ Fin (n-fourRowFiniteSeedColumns s))) :
    finiteK4RoleKeys.get (finiteK4RoleIndex
      ![((finiteTriplePhysicalSeed hm hn s 0).1.val,(finiteTriplePhysicalSeed hm hn s 0).2.val),
        ((finiteTriplePhysicalSeed hm hn s 1).1.val,(finiteTriplePhysicalSeed hm hn s 1).2.val),
        ((finiteTriplePhysicalSeed hm hn s 2).1.val,(finiteTriplePhysicalSeed hm hn s 2).2.val),
        ((fourRowFiniteSeedPhysicalEquiv hm hn s p).1.val,(fourRowFiniteSeedPhysicalEquiv hm hn s p).2.val),
        ((fourRowFiniteSeedPhysicalEquiv hm hn s q).1.val,(fourRowFiniteSeedPhysicalEquiv hm hn s q).2.val)]) =
      fourRowFiniteSeedPairKey s (ordinaryPair p.1 q.1) (ordinaryPair p.2 q.2) := by
  let actual : Fin 5 → ℕ × ℕ := fun i =>
    (fourRowFinitePhysicalFiveLabels (fourRowFiniteTripleSeedRow s) p.1 q.1 i,
      fourRowFinitePhysicalFiveLabels (fourRowFiniteTripleSeedColumn s) p.2 q.2 i)
  let compressed : Fin 5 → ℕ × ℕ := fun i =>
    (fourRowFiniteCompressedFiveLabels (fourRowFiniteTripleSeedRow s) p.1 q.1 i,
      fourRowFiniteCompressedFiveLabels (fourRowFiniteTripleSeedColumn s) p.2 q.2 i)
  have ha :
      ![((finiteTriplePhysicalSeed hm hn s 0).1.val,(finiteTriplePhysicalSeed hm hn s 0).2.val),
        ((finiteTriplePhysicalSeed hm hn s 1).1.val,(finiteTriplePhysicalSeed hm hn s 1).2.val),
        ((finiteTriplePhysicalSeed hm hn s 2).1.val,(finiteTriplePhysicalSeed hm hn s 2).2.val),
        ((fourRowFiniteSeedPhysicalEquiv hm hn s p).1.val,(fourRowFiniteSeedPhysicalEquiv hm hn s p).2.val),
        ((fourRowFiniteSeedPhysicalEquiv hm hn s q).1.val,(fourRowFiniteSeedPhysicalEquiv hm hn s q).2.val)] =
      actual := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact Prod.ext
        (fourRowFinitePhysicalAxisEquiv_val ((fourRowFiniteSeed_counts s).2.2.1.trans hm) p.1)
        (fourRowFinitePhysicalAxisEquiv_val ((fourRowFiniteSeed_counts s).2.2.2.2.trans hn) p.2)
    · exact Prod.ext
        (fourRowFinitePhysicalAxisEquiv_val ((fourRowFiniteSeed_counts s).2.2.1.trans hm) q.1)
        (fourRowFinitePhysicalAxisEquiv_val ((fourRowFiniteSeed_counts s).2.2.2.2.trans hn) q.2)
  rw [ha,←finiteK4RoleIndex_spec]
  have he : finiteK4TupleRoleKey actual = finiteK4TupleRoleKey compressed :=
    finiteK4TupleRoleKey_congr actual compressed
      (fourRowFinitePhysicalFiveLabels_eq_iff (fourRowFiniteTripleSeedRow s) p.1 q.1)
      (fourRowFinitePhysicalFiveLabels_eq_iff (fourRowFiniteTripleSeedColumn s) p.2 q.2)
  rw [he]
  change fourRowFiniteCanonicalRoleKey
    [((finiteTripleSeed s 0).1.val,(finiteTripleSeed s 0).2.val),
      ((finiteTripleSeed s 1).1.val,(finiteTripleSeed s 1).2.val),
      ((finiteTripleSeed s 2).1.val,(finiteTripleSeed s 2).2.val)] _ _ = _
  have hm' :
      [((finiteTripleSeed s 0).1.val,(finiteTripleSeed s 0).2.val),
        ((finiteTripleSeed s 1).1.val,(finiteTripleSeed s 1).2.val),
        ((finiteTripleSeed s 2).1.val,(finiteTripleSeed s 2).2.val)] =
      fourRowFiniteSeedMark s := by
    simpa only [List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two] using finiteTripleSeed_mark s
  rw [hm']
  rfl

theorem fourRowFiniteSeedMatrix_physical {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (s : Fin 10) (h : ℕ → ℝ) :
    (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k)) (finiteTriplePhysicalSeed hm hn s)).submatrix
      (fourRowFiniteSeedPhysicalEquiv hm hn s) (fourRowFiniteSeedPhysicalEquiv hm hn s) =
      twoAxisOrdinaryMatrix (fourRowFiniteSeedRelationKernel s h) := by
  ext p q
  exact congrArg h (fourRowFiniteSeedRole_physical hm hn s p q)

end
end DittertRybin
