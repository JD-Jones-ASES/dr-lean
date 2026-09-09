import DR.Square.OrderFourOrbitPSD
import DR.Square.OrderFourPolynomial

/-! The full physical multiplier domain and actual quartic interpretation. -/

open scoped BigOperators
open DittertRybin DittertRybin.Certificates

example (s : Sym (Fin 16) 4) (x : Fin 16 → ℝ) :
    (1/10:ℝ)*((∑ i, x i^2)-(∑ i, x i)^2/16) ≤
      quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
        (fun q : ℚ => (q : ℝ))) x := orderFourSortedMultiplier_lower s x

example : separationProbability (uniformBoard 4 4) 4 = (183/1024:ℝ) := orderFour_uniform_value

#print axioms DittertRybin.orderFourQuarticPolynomial_eval
#print axioms DittertRybin.orderFourOrbitCoverage
#print axioms DittertRybin.orderFourSortedMultiplier_lower
