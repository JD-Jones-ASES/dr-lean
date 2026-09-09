import DR.Square.SpectralSix

/-! The full closed-simplex order-six interface and its kernel audit. -/

namespace DittertRybin.Tests

-- Only the original Dittert domain remains: entrywise nonnegativity and total mass six.
example (A : Board 6 6) (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6) :
    dittertFunctional A ≤ 2 - dittertConstant 6 :=
  (dittert_order_six A hA hmass).1

-- Unique equality is part of the principal statement, including every boundary matrix.
example (A : Board 6 6) (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 6) :
    dittertFunctional A = 2 - dittertConstant 6 ↔ A = uniformDittertMatrix 6 :=
  (dittert_order_six A hA hmass).2

#print axioms six_sorted_energy_bound
#print axioms six_odd_prefix_boundary
#print axioms six_oriented_cut_of_score_prefix
#print axioms dittert_globalMax_cut_six
#print axioms six_balanced_cut_contradiction
#print axioms dittert_globalMax_uniform_six
#print axioms dittert_order_six

end DittertRybin.Tests
