import DR.Rectangular.FourRowScalarGaugePolynomial

/-! Generated exact sorted-gap certificate. Reproduce with
`scripts/generate_four_row_scalar_gauge.py --check`.
The literal target has 116 positive coefficients. Its quantitative residual
below has 115 positive integer coefficients after multiplication by 1024. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowScalarGaugeResidual (a b c d : ℝ) : ℝ :=
    ((((((((488 : ℝ)*a^6*b) +
    (((976 : ℝ)*a^6*c) +
    ((1464 : ℝ)*a^6*d))) +
    ((((5368 : ℝ)*a^5*b^2) +
    ((15320 : ℝ)*a^5*b*c)) +
    (((19904 : ℝ)*a^5*b*d) +
    ((12392 : ℝ)*a^5*c^2)))) +
    ((((31024 : ℝ)*a^5*c*d) +
    (((21072 : ℝ)*a^5*d^2) +
    ((24400 : ℝ)*a^4*b^3))) +
    ((((90008 : ℝ)*a^4*b^2*c) +
    ((106816 : ℝ)*a^4*b^2*d)) +
    (((120224 : ℝ)*a^4*b*c^2) +
    ((279392 : ℝ)*a^4*b*c*d))))) +
    (((((172576 : ℝ)*a^4*b*d^2) +
    (((59496 : ℝ)*a^4*c^3) +
    ((201832 : ℝ)*a^4*c^2*d))) +
    ((((239792 : ℝ)*a^4*c*d^2) +
    ((102336 : ℝ)*a^4*d^3)) +
    (((58560 : ℝ)*a^3*b^4) +
    ((265472 : ℝ)*a^3*b^3*c)))) +
    ((((296704 : ℝ)*a^3*b^3*d) +
    (((468784 : ℝ)*a^3*b^2*c^2) +
    ((1033216 : ℝ)*a^3*b^2*c*d))) +
    ((((588160 : ℝ)*a^3*b^2*d^2) +
    ((394992 : ℝ)*a^3*b*c^3)) +
    (((1284608 : ℝ)*a^3*b*c^2*d) +
    ((1433728 : ℝ)*a^3*b*c*d^2)))))) +
    ((((((563712 : ℝ)*a^3*b*d^3) +
    (((138000 : ℝ)*a^3*c^4) +
    ((587296 : ℝ)*a^3*c^3*d))) +
    ((((954144 : ℝ)*a^3*c^2*d^2) +
    ((718080 : ℝ)*a^3*c*d^3)) +
    (((218112 : ℝ)*a^3*d^4) +
    ((78080 : ℝ)*a^2*b^5)))) +
    ((((422976 : ℝ)*a^2*b^4*c) +
    (((455552 : ℝ)*a^2*b^4*d) +
    ((920736 : ℝ)*a^2*b^3*c^2))) +
    ((((1959424 : ℝ)*a^2*b^3*c*d) +
    ((1048320 : ℝ)*a^2*b^3*d^2)) +
    (((1029168 : ℝ)*a^2*b^2*c^3) +
    ((3236736 : ℝ)*a^2*b^2*c^2*d))))) +
    (((((3405696 : ℝ)*a^2*b^2*c*d^2) +
    (((1222144 : ℝ)*a^2*b^2*d^3) +
    ((613480 : ℝ)*a^2*b*c^4))) +
    ((((2526272 : ℝ)*a^2*b*c^3*d) +
    ((3883968 : ℝ)*a^2*b*c^2*d^2)) +
    (((2688512 : ℝ)*a^2*b*c*d^3) +
    ((733184 : ℝ)*a^2*b*d^4)))) +
    (((((162592 : ℝ)*a^2*c^5) +
    ((822664 : ℝ)*a^2*c^4*d)) +
    (((1635168 : ℝ)*a^2*c^3*d^2) +
    ((1611392 : ℝ)*a^2*c^2*d^3))) +
    ((((812032 : ℝ)*a^2*c*d^4) +
    ((178176 : ℝ)*a^2*d^5)) +
    (((54656 : ℝ)*a*b^6) +
    ((348288 : ℝ)*a*b^5*c))))))) +
    (((((((368640 : ℝ)*a*b^5*d) +
    (((912320 : ℝ)*a*b^4*c^2) +
    ((1905920 : ℝ)*a*b^4*c*d))) +
    ((((984320 : ℝ)*a*b^4*d^2) +
    ((1268352 : ℝ)*a*b^3*c^3)) +
    (((3904256 : ℝ)*a*b^3*c^2*d) +
    ((3943936 : ℝ)*a*b^3*c*d^2)))) +
    ((((1316864 : ℝ)*a*b^3*d^3) +
    (((1012440 : ℝ)*a*b^2*c^4) +
    ((4055040 : ℝ)*a*b^2*c^3*d))) +
    ((((5927040 : ℝ)*a*b^2*c^2*d^2) +
    ((3757056 : ℝ)*a*b^2*c*d^3)) +
    (((890880 : ℝ)*a*b^2*d^4) +
    ((462136 : ℝ)*a*b*c^5))))) +
    (((((2246464 : ℝ)*a*b*c^4*d) +
    (((4165248 : ℝ)*a*b*c^3*d^2) +
    ((3634688 : ℝ)*a*b*c^2*d^3))) +
    ((((1484800 : ℝ)*a*b*c*d^4) +
    ((237568 : ℝ)*a*b*d^5)) +
    (((99848 : ℝ)*a*c^6) +
    ((569520 : ℝ)*a*c^5*d)))) +
    (((((1265040 : ℝ)*a*c^4*d^2) +
    ((1348864 : ℝ)*a*c^3*d^3)) +
    (((672768 : ℝ)*a*c^2*d^4) +
    ((118784 : ℝ)*a*c*d^5))) +
    ((((15616 : ℝ)*b^7) +
    ((116096 : ℝ)*b^6*c)) +
    (((122880 : ℝ)*b^6*d) +
    ((364928 : ℝ)*b^5*c^2)))))) +
    ((((((762368 : ℝ)*b^5*c*d) +
    (((393728 : ℝ)*b^5*d^2) +
    ((634176 : ℝ)*b^4*c^3))) +
    ((((1952128 : ℝ)*b^4*c^2*d) +
    ((1971968 : ℝ)*b^4*c*d^2)) +
    (((658432 : ℝ)*b^4*d^3) +
    ((674960 : ℝ)*b^3*c^4)))) +
    ((((2703360 : ℝ)*b^3*c^3*d) +
    (((3951360 : ℝ)*b^3*c^2*d^2) +
    ((2504704 : ℝ)*b^3*c*d^3))) +
    ((((593920 : ℝ)*b^3*d^4) +
    ((462136 : ℝ)*b^2*c^5)) +
    (((2246464 : ℝ)*b^2*c^4*d) +
    ((4165248 : ℝ)*b^2*c^3*d^2))))) +
    (((((3634688 : ℝ)*b^2*c^2*d^3) +
    (((1484800 : ℝ)*b^2*c*d^4) +
    ((237568 : ℝ)*b^2*d^5))) +
    ((((199696 : ℝ)*b*c^6) +
    ((1139040 : ℝ)*b*c^5*d)) +
    (((2530080 : ℝ)*b*c^4*d^2) +
    ((2697728 : ℝ)*b*c^3*d^3)))) +
    (((((1345536 : ℝ)*b*c^2*d^4) +
    ((237568 : ℝ)*b*c*d^5)) +
    (((42792 : ℝ)*c^7) +
    ((284760 : ℝ)*c^6*d))) +
    ((((759024 : ℝ)*c^5*d^2) +
    ((1011648 : ℝ)*c^4*d^3)) +
    (((672768 : ℝ)*c^3*d^4) +
    ((178176 : ℝ)*c^2*d^5))))))))

theorem fourRowScalarGaugeResidual_nonneg {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ fourRowScalarGaugeResidual a b c d := by
  unfold fourRowScalarGaugeResidual
  positivity

/-- The finite identity is proved by ordinary ring normalization of the literal source. -/
theorem fourRowScalarGaugeResidual_identity (a b c d : ℝ) :
    1024*(fourRowGaugeHomogeneous ![d,c+d,b+c+d,a+b+c+d] -
      (61/256)*fourRowGaugeHomogeneousVariance ![d,c+d,b+c+d,a+b+c+d]*
        (a+2*b+3*c+4*d)^5) = fourRowScalarGaugeResidual a b c d := by
  simp only [fourRowGaugeHomogeneous, fourRowGaugeHomogeneousVariance]
  simp_rw [fourRowGaugeCollision_moments]
  norm_num [Fin.sum_univ_succ, fourRowScalarGaugeResidual]
  ring

end DittertRybin
