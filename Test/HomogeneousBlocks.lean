import DR.Square.HomogeneousBlocks

/-! Exact normalization for independently labeled two-by-two blocks. -/
namespace DittertRybin.Tests
open scoped BigOperators

example {n : ℕ} (A : Board n n) (hA : ∀ i j, 0 ≤ A i j)
    (I J : Finset (Fin n)) (e : I ≃ J) (hI : I.card = 2) :
    (∏ i : I, ∑ j ∈ J, A i j) + (∏ j : J, ∑ i ∈ I, A i j) -
      (3/2) * (cutMass A I J / 2)^2 ≤ (squareCutBlock A I J e).permanent := by
  have hd : DittertMaximizer I.card := hI ▸ dittert_order_two
  have h := hd.squareCutBlock_lower A hA I J e (by omega)
  norm_num [hI, dittertConstant, Nat.factorial] at h ⊢
  exact h

#print axioms DittertMaximizer.permanent_lower_fintype
#print axioms DittertMaximizer.squareCutBlock_lower

end DittertRybin.Tests
