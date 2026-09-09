import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact scalar square completion for the endpoint collision criterion.
The signed projections E,L,S are unrestricted except for their actual
Cauchy bounds. No matrix positivity is assumed. -/
namespace DittertRybin

theorem endpoint_scalar_completion_gap (M A sigma S E L N : ℝ)
    (hM : 0 < M) (hA : 0 ≤ A) (hAupper : A ≤ 3/2)
    (hsigma : 4*M^2 ≤ sigma)
    (hE : E^2 ≤ N/9) (hL : L^2 ≤ N/64) :
    (3/32)*N ≤ (1/2)*N+sigma*S^2-A*(M*S+E)^2-2*L*(M*S+E) := by
  let kappa := sigma-M^2*A
  have hM2 : 0 < M^2 := sq_pos_of_pos hM
  have hk : (5/2)*M^2 ≤ kappa := by
    have h := mul_le_mul_of_nonneg_left hAupper hM2.le
    dsimp [kappa]
    nlinarith
  have hkpos : 0 < kappa := by nlinarith
  have hr0 : 0 ≤ M^2/kappa := div_nonneg hM2.le hkpos.le
  have hr : M^2/kappa ≤ 2/5 := (div_le_iff₀ hkpos).mpr (by nlinarith)
  have hAE : A*E^2 ≤ N/6 := by
    have h := mul_le_mul_of_nonneg_right hAupper (sq_nonneg E)
    nlinarith
  have hcross : 2*E*L ≤ N/12 := by
    nlinarith [sq_nonneg (3*E-8*L)]
  have hA2 : A^2 ≤ 9/4 := by nlinarith
  have hAE2 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg E)
  have hG : (A*E+L)^2 ≤ (25/64)*N := by
    nlinarith [sq_nonneg (A*E-4*L)]
  have hnegative : (M^2/kappa)*(A*E+L)^2 ≤ (5/32)*N := by
    have h := mul_le_mul hr hG (sq_nonneg (A*E+L)) (by norm_num : (0:ℝ) ≤ 2/5)
    nlinarith
  have hpositive := mul_nonneg hkpos.le (sq_nonneg (S-M/kappa*(A*E+L)))
  have heq : (1/2)*N+sigma*S^2-A*(M*S+E)^2-2*L*(M*S+E) =
      (1/2)*N-A*E^2-2*E*L-(M^2/kappa)*(A*E+L)^2+
        kappa*(S-M/kappa*(A*E+L))^2 := by
    have hkn : kappa ≠ 0 := hkpos.ne'
    field_simp
    dsimp [kappa]
    ring
  nlinarith only [hAE,hcross,hnegative,hpositive,heq]

end DittertRybin
