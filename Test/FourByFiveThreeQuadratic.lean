import DR.Rectangular.FourByFiveThreeQuadratic

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- This reindexing identity does not require probability or positivity.
example (P : Board 4 5) (e f : Fin 4 × Fin 5) :
    quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
      (fun a => P a.1 a.2) =
      quadraticValue ((fourByFiveThreeMatrix (fourByFiveThreeCell e)
        (fourByFiveThreeCell f)).map (fun q : ℚ => (q:ℝ))) (fourByFiveThreeFlat P) :=
  fourByFiveThree_cell_quadratic P e f

-- Signed, mass-one matrices retain the spectral bound for each multiplier pair.
example (P : Board 4 5) (hmass : totalMass P=1) (e f : Fin 4 × Fin 5) :
    (2/5:ℝ)*fourByFiveThreeEnergy P≤
      quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
        (fun a => P a.1 a.2) :=
  fourByFiveThree_cell_quadratic_lower P hmass e f

-- Summing multiplier weights uses only nonnegative entries and total mass one.
example {P : Board 4 5} (hP : IsProbability P) :
    (1/5:ℝ)*fourByFiveThreeEnergy P≤
      ∑ e : Fin 4 × Fin 5,∑ f : Fin 4 × Fin 5,
        unorderedPairWeight e f*P e.1 e.2*P f.1 f.2*
          quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
            (fun a => P a.1 a.2) :=
  fourByFiveThree_weighted_quadratic_lower hP

#print axioms fourByFiveThree_cell_quadratic
#print axioms fourByFiveThree_cell_quadratic_lower
#print axioms fourByFiveThree_weighted_quadratic_lower
end DittertRybin.Tests
