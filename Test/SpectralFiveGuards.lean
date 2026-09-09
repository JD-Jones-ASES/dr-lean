import DR.Certificates.SpectralFiveGuards

namespace DittertRybin.Tests
open Certificates.SpectralFiveGuards

-- Polynomial positivity extends beyond the physical interval, while energy nonnegativity does not.
example : energy (9 / 20) < 0 := by norm_num [energy, height]
example : domination (9 / 20) = 11 / 20 := by norm_num [domination]
example : crossingBound 0 < 13 / 50 := crossingBound_lt_thirteen_fiftieths 0 (by norm_num) (by norm_num)

#print axioms denominator_pos
#print axioms crossingBound_lt_thirteen_fiftieths
#print axioms physical_crossingBound_nonneg
#print axioms energy_of_deficit
#print axioms fiveDeficitParameter_inverse
end DittertRybin.Tests
