import DR.Rectangular.TwentyByTwentyOrderFour

namespace DittertRybin.Tests
open Certificates

example {P : Board 20 20} (hP : IsProbability P) (i j : Fin 20) (hz : P i j=0) :
    separationProbability P 4 < 14805351/16000000 := by
  obtain ⟨hle,heq⟩ := twentyByTwenty_orderFour_closed_simplex P hP
  apply lt_of_le_of_ne hle
  intro hval
  have hu := heq.mp hval
  rw [hu] at hz
  norm_num [uniformBoard] at hz

example : separationProbability (uniformBoard 20 20) 4 = 14805351/16000000 := by
  exact (twentyByTwenty_orderFour_closed_simplex _
    (uniformBoard_isProbability (by decide) (by decide))).2.mpr rfl

example : ¬(separationProbability (uniformBoard 20 20) 4 ≤ 14805350/16000000) := by
  rw [separationProbability_uniform (by decide) (by decide),finiteK4Fixed20_uniform_value]
  norm_num

#print axioms uniform_maximum_twenty_by_twenty_order_four
#print axioms twentyByTwenty_orderFour_closed_simplex
end DittertRybin.Tests
