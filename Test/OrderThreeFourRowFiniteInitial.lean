import DR.Rectangular.OrderThreeFourRowFiniteInitial

open DittertRybin

example : UniformMaximizer 4 6 3 :=
  uniformMaximizer_orderThree_four_rows_six_to_twentyOne (by decide) (by decide)
example : UniformMaximizer 4 21 3 :=
  uniformMaximizer_orderThree_four_rows_six_to_twentyOne (by decide) (by decide)

#print axioms uniformMaximizer_orderThree_four_rows_six_to_twentyOne
