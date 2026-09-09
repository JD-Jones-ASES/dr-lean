import DR.Certificates.FourByFiveThreeDefinitions
import DR.Certificates.FiniteK3QuarticData

/-! The 93 source coefficients discharge all 33 literal quartic equations.
This rational check is separate from both PSD and the iid semantic bridge. -/
namespace DittertRybin.Certificates
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourByFiveThree_equations_rational : ∀ a : Fin 33,
    (∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℚ)*fourByFiveThreeCoefficient k)=
      (finiteK3QuarticMultiplicity.get a:ℚ)*(27/40)-(finiteK3QuarticSuccesses.get a:ℚ) := by
  decide +kernel

theorem fourByFiveThree_equations_real (a : Fin 33) :
    (∑ k,(((finiteK3QuarticRows.get a).get k:Nat):ℝ)*(fourByFiveThreeCoefficient k:ℝ))=
      (finiteK3QuarticMultiplicity.get a:ℝ)*(27/40)-(finiteK3QuarticSuccesses.get a:ℝ) := by
  have h := congrArg (fun q : ℚ => (q:ℝ)) (fourByFiveThree_equations_rational a)
  simpa only [Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using h

end DittertRybin.Certificates
