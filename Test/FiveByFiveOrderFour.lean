import DR.Rectangular.FiveByFiveOrderFour

namespace DittertRybin.Tests
open Certificates

-- A zero cell forces a strict gap: the boundary belongs to the theorem's
-- domain and cannot attain its sharp value.
example {P : Board 5 5} (hP : IsProbability P) (i j : Fin 5) (hz : P i j=0) :
    separationProbability P 4 < 5424/15625 := by
  obtain ⟨hle,heq⟩ := fiveByFive_orderFour_closed_simplex P hP
  apply lt_of_le_of_ne hle
  intro hval
  have hu := heq.mp hval
  rw [hu] at hz
  norm_num [uniformBoard] at hz

example : separationProbability (uniformBoard 5 5) 4 = 5424/15625 := by
  exact (fiveByFive_orderFour_closed_simplex _
    (uniformBoard_isProbability (by decide) (by decide))).2.mpr rfl

-- The sharp target is exact, so lowering its numerator by one is invalid.
example : ¬(separationProbability (uniformBoard 5 5) 4 ≤ 5423/15625) := by
  rw [separationProbability_uniform (by decide) (by decide),finiteK4Fixed5_uniform_value]
  norm_num

#print axioms uniform_maximum_five_by_five_order_four
#print axioms fiveByFive_orderFour_closed_simplex
end DittertRybin.Tests
