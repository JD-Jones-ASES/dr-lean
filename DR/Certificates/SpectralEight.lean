import DR.Certificates.Bernstein
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
/-!
# Exact spectral scalar certificate at dimension eight

The degree-sixteen gap compares the spectral cut estimate with the
permanent lower bound at dimension eight.
The 17 rational coefficients are reconstructed from the displayed scalar
polynomial. Lean proves the exact polynomial identity, checks every rational
coefficient against the stated positive margin, and proves strict positivity
on the entire closed unit interval. No numerical solver output is used.
The analytic dimension-transfer and matrix argument are separate obligations.
-/

namespace DittertRybin.Certificates.SpectralEight
open scoped BigOperators
noncomputable section
open MvPolynomial

def gapPolynomial : MvPolynomial (Fin 1) ℚ :=
  C ((8 / 7 : ℚ) ^ 7) *
    (1 - C (7 / 50 : ℚ) * X 0 - C (73 / 1000 : ℚ) * (1 - X 0 ^ 2)) ^ 8 - (1 - X 0 ^ 2)
def coefficients : Fin 17 → ℚ := ![(152607078868323859243081 : ℚ) / 392695903778076171875000,
  (111429938862662583969871 : ℚ) / 392695903778076171875000,
  (1189352233975860869344609 : ℚ) / 5890438556671142578125000,
  (276756712592386866651159 : ℚ) / 1963479518890380859375000,
  (253048240468689788539231 : ℚ) / 2552523374557495117187500,
  (574631215328325072341023 : ℚ) / 7657570123672485351562500,
  (3790359232070777900905297 : ℚ) / 56155514240264892578125000,
  (21212572774921306553370759 : ℚ) / 280777571201324462890625000,
  (62173669041726897866579747 : ℚ) / 631749535202980041503906250,
  (1901722405675975517101981 : ℚ) / 14038878560066223144531250,
  (418203134923602201067387 : ℚ) / 2246220569610595703125000,
  (10217347982291512538167 : ℚ) / 40840373992919921875000,
  (1336107559774384460521 : ℚ) / 4084037399291992187500,
  (130972177181501444867 : ℚ) / 314156723022460937500,
  (65256159101806862783 : ℚ) / 125662689208984375000,
  (3188315592546242541 : ℚ) / 5026507568359375000,
  (95749736674107392 : ℚ) / 125662689208984375]
def margin : ℚ := 3790359232070777900905297 / 56155514240264892578125000

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem coefficient_identity : affineNormalize (fun _ : Fin 1 ↦ 0) (fun _ ↦ 1) gapPolynomial =
    tensorPolynomial (fun _ : Fin 1 ↦ 16) (fun a ↦ coefficients (a 0)) := by
  apply MvPolynomial.funext
  intro x
  rw [tensorPolynomial_one]
  norm_num [affineNormalize, gapPolynomial, coefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem coefficients_ge_margin (a : BernsteinIndex (fun _ : Fin 1 ↦ 16)) : margin ≤ coefficients (a 0) := by
  generalize a 0 = b
  fin_cases b <;> norm_num [coefficients, margin]

def certificate : BernsteinCertificate gapPolynomial (fun _ ↦ 0) (fun _ ↦ 1) where
  degree := fun _ ↦ 16
  coefficients := fun a ↦ coefficients (a 0)
  margin := margin
  identity := coefficient_identity
  coefficient_bound := coefficients_ge_margin

theorem gap_pos (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < (8 / 7 : ℝ)^7 * (1 - (7/50:ℝ)*z - (73/1000:ℝ)*(1-z^2))^8 - (1-z^2) := by
  have h := certificate.pos (by intro i; norm_num) (by norm_num [certificate, margin])
    (fun _ ↦ z) (fun _ ↦ by norm_num; exact ⟨hz, hz1⟩)
  simpa [rationalEval, gapPolynomial] using h

end
end DittertRybin.Certificates.SpectralEight
