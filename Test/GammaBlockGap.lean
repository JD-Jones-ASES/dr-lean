import DR.Endpoint.GammaBlockGap

namespace DittertRybin.Tests

example : 2*dittertConstant 2=dittertConstant 1*dittertConstant 1 := by
  norm_num [dittertConstant]
example : 2*dittertConstant 6≤dittertConstant 1*dittertConstant 5 :=
  dittertConstant_mul_ge_twice (k:=1) (l:=5) (by decide) (by decide)
example : 2*dittertConstant 100≤dittertConstant 37*dittertConstant 63 :=
  dittertConstant_mul_ge_twice (k:=37) (l:=63) (by decide) (by decide)
example : gammaBinomialTerm 1 1 1/2=gammaBinomialTerm 1 1 0 ∧
    gammaBinomialTerm 1 1 1/2=gammaBinomialTerm 1 1 2 := by
  norm_num [gammaBinomialTerm]
example : ¬2*dittertConstant 1≤dittertConstant 0*dittertConstant 1 := by
  norm_num [dittertConstant]
example : ¬3*dittertConstant 2≤dittertConstant 1*dittertConstant 1 := by
  norm_num [dittertConstant]

#print axioms gammaBinomialTerm_successor
#print axioms gammaBinomialTerm_predecessor
#print axioms gammaBinomialTerm_middle_le_half
#print axioms dittertConstant_mul_ge_twice

end DittertRybin.Tests
