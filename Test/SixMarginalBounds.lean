import DR.Square.SixMarginalBounds

/-! Exact controls for the sharp constants and their domain restrictions. -/

namespace DittertRybin.SixMarginalBoundsTests

/-- The tempting smaller constant does not majorize the entropy square root. -/
theorem understated_envelope_rejected : ¬ ((97 / 100 : ℝ) ^ 2 ≥ 17 / 18) := by
  norm_num

/-- Empty and full subsets carry the required exact zero coefficient. -/
theorem boundary_coefficients (t : ℝ) :
    sixCutCoefficient 0 t = 0 ∧ sixCutCoefficient 6 t = 0 := by
  norm_num [sixCutCoefficient]

/-- The adjacent middle pair attains the asserted worst ratio, whose
cardinality difference is exactly one. -/
theorem middle_pair_saturates (t : ℝ) :
    sixCutCoefficient 2 t + sixCutCoefficient 3 t = sixCutStar t := by
  norm_num [sixCutCoefficient, sixCutStar]
  ring

/-- Dropping the certified parameter interval makes the coefficient cap false. -/
theorem unrestricted_coefficient_cap_rejected : sixCutCoefficient 2 1 > 3 := by
  norm_num [sixCutCoefficient]

end DittertRybin.SixMarginalBoundsTests
