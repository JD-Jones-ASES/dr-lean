import DR.Certificates.Bernstein
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite

/-!
# Exact spectral scalar certificates at dimension seven

These are the two degree-fourteen scalar certificates from Analytic-Lab
`probes/P0174_rybin_semimatchings/SPECTRAL_SQUARE_ENDPOINT.md`.
Their exact rational domains are [0,1/2] and [1/2,1]. Each coefficient
identity is proved as a rational polynomial identity. Both complete
coefficient tables have a positive checked margin. The two semantic box
bounds cover the full closed unit interval, including the shared endpoint.
The matrix argument and analytic dimension transfer remain separate.
-/

namespace DittertRybin.Certificates.SpectralSeven
open scoped BigOperators
noncomputable section
open MvPolynomial

def gapPolynomial : MvPolynomial (Fin 1) ℚ :=
  C ((7 / 6 : ℚ) ^ 6) *
    (1 - C (21 / 100 : ℚ) * X 0 - C (71 / 1000 : ℚ) * (1 - X 0 ^ 2)) ^ 7 - (1 - X 0 ^ 2)

def leftCoefficients : Fin 15 → ℚ := ![(23602397200367012858560241 : ℚ) / 46656000000000000000000000,
  (39263856073458959678208937 : ℚ) / 93312000000000000000000000,
  (5860406038906812547469352757 : ℚ) / 16982784000000000000000000000,
  (9449004782267279663992296481 : ℚ) / 33965568000000000000000000000,
  (14917538087240830174167325379 : ℚ) / 67931136000000000000000000000,
  (22936104107769082269810568067 : ℚ) / 135862272000000000000000000000,
  (7865128894658612261820502499 : ℚ) / 62705664000000000000000000000,
  (20739014692530432679405546501 : ℚ) / 232906752000000000000000000000,
  (27629996196232833663254684743 : ℚ) / 465813504000000000000000000000,
  (78101014554841044061935063443 : ℚ) / 2173796352000000000000000000000,
  (80855656476316376504943020293 : ℚ) / 4347592704000000000000000000000,
  (61437372347578661325716603521 : ℚ) / 8695185408000000000000000000000,
  (19095741522384818866783277651 : ℚ) / 17390370816000000000000000000000,
  (1291601214381152499360055951 : ℚ) / 2675441664000000000000000000000,
  (3842872456427458272785046727 : ℚ) / 764411904000000000000000000000]
def leftMargin : ℚ := 1291601214381152499360055951 / 2675441664000000000000000000000

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem left_coefficient_identity :
    affineNormalize (fun _ : Fin 1 ↦ 0) (fun _ ↦ (1/2 : ℚ)) gapPolynomial =
      tensorPolynomial (fun _ : Fin 1 ↦ 14) (fun a ↦ leftCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, gapPolynomial, leftCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem left_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 14)) :
    leftMargin ≤ leftCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [leftCoefficients, leftMargin]

def leftCertificate : BernsteinCertificate gapPolynomial (fun _ ↦ 0) (fun _ ↦ (1/2 : ℚ)) where
  degree := fun _ ↦ 14
  coefficients := fun a ↦ leftCoefficients (a 0)
  margin := leftMargin
  identity := left_coefficient_identity
  coefficient_bound := left_coefficients_ge_margin

def rightCoefficients : Fin 15 → ℚ := ![(3842872456427458272785046727 : ℚ) / 764411904000000000000000000000,
  (4268084330101842568355878523 : ℚ) / 445906944000000000000000000000,
  (167607751741686778353430537541 : ℚ) / 8695185408000000000000000000000,
  (9370755504559033353112073 : ℚ) / 276037632000000000000000000,
  (3870312443456490287658210247 : ℚ) / 72459878400000000000000000000,
  (2340392696873975058867811037 : ℚ) / 30191616000000000000000000000,
  (43253972114103947291587938923 : ℚ) / 407586816000000000000000000000,
  (674944619997188105395459717 : ℚ) / 4852224000000000000000000000,
  (1796835716606537521840049651 : ℚ) / 10189670400000000000000000000,
  (316050152141426548401281 : ℚ) / 1451520000000000000000000,
  (42570877103021603687113 : ℚ) / 161740800000000000000000,
  (235991407299407218271 : ℚ) / 754790400000000000000,
  (31080707344500880622237 : ℚ) / 84913920000000000000000,
  (46075909570793212907 : ℚ) / 108864000000000000000,
  (2259320688312620191 : ℚ) / 4665600000000000000]
def rightMargin : ℚ := 3842872456427458272785046727 / 764411904000000000000000000000

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem right_coefficient_identity :
    affineNormalize (fun _ : Fin 1 ↦ (1/2 : ℚ)) (fun _ ↦ 1) gapPolynomial =
      tensorPolynomial (fun _ : Fin 1 ↦ 14) (fun a ↦ rightCoefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, gapPolynomial, rightCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem right_coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 14)) :
    rightMargin ≤ rightCoefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [rightCoefficients, rightMargin]

def rightCertificate : BernsteinCertificate gapPolynomial (fun _ ↦ (1/2 : ℚ)) (fun _ ↦ 1) where
  degree := fun _ ↦ 14
  coefficients := fun a ↦ rightCoefficients (a 0)
  margin := rightMargin
  identity := right_coefficient_identity
  coefficient_bound := right_coefficients_ge_margin

theorem gap_pos (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < (7 / 6 : ℝ)^6 * (1 - (21/100:ℝ)*z - (71/1000:ℝ)*(1-z^2))^7 - (1-z^2) := by
  have h : 0 < rationalEval (fun _ : Fin 1 ↦ z) gapPolynomial := by
    by_cases hhalf : z ≤ 1/2
    · exact leftCertificate.pos (by intro i; norm_num) (by norm_num [leftCertificate, leftMargin])
        (fun _ ↦ z) (fun _ ↦ by norm_num; exact ⟨hz, hhalf⟩)
    · exact rightCertificate.pos (by intro i; norm_num) (by norm_num [rightCertificate, rightMargin])
        (fun _ ↦ z) (fun _ ↦ by norm_num; exact ⟨le_of_lt (lt_of_not_ge hhalf), hz1⟩)
  simpa [rationalEval, gapPolynomial] using h

end
end DittertRybin.Certificates.SpectralSeven
