import DR.Definitions

/-!
# The homogeneous cubic for three-sample failure

This signed polynomial is defined on arbitrary real boards. Its connection
to the actual iid sampling event is proved separately in OrderThreeSampling;
the definition alone is not a probability or optimization claim.
-/

namespace DittertRybin
open scoped BigOperators

def orderThreeFailurePolynomial {m n : ℕ} (P : Board m n) : ℝ :=
  3 * totalMass P * (∑ i, ∑ j, P i j ^ 2) +
    6 * (∑ i, ∑ j, P i j * rowSum P i * colSum P j) -
    6 * (∑ i, ∑ j, P i j ^ 2 * (rowSum P i + colSum P j)) +
    4 * (∑ i, ∑ j, P i j ^ 3)

end DittertRybin
