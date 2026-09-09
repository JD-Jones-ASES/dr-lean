import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (6,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block48PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-163579563337018250537540638392192000000000000000 : ℚ) / 7, (136118283470253568765771793740831680000000000000 : ℚ) / 1, (-3185919546023275017191770590820606564000000000000 : ℚ) / 7, (6846066810882577319141859700647106366250000000000 : ℚ) / 7, (-9395197718845190955320331195601814357987500000000 : ℚ) / 7, (7602547692952814156275359577070659325537500000000 : ℚ) / 7, (-2766758836498323028312156524968192596643750000000 : ℚ) / 7, (342967629593271074878021136829842471384375000000 : ℚ) / 1, (-1385042643201608617316309062054294339190781250000 : ℚ) / 1, (2290427525411933739561986482613134453186406250000 : ℚ) / 1, (-1529947421369526817782940423786605766238968750000 : ℚ) / 1, (-1541050365615551755240065489811590370457756250000 : ℚ) / 7, (1021677859937315022844836587641981486494726250000 : ℚ) / 1, (-3543825785706517882779428692587639497797025000000 : ℚ) / 7, (-795679210976513343034880742576907456584570750000 : ℚ) / 7, (953569659101380707786947121983204815171459000000 : ℚ) / 7, (-332687052227862143728883503984022013151801000000 : ℚ) / 7, (-45793650973169997652573310609382530576342750000 : ℚ) / 7, (88263643605170018553069770448378651187385775000 : ℚ) / 7, (-2084742469922326977191722123854663146556725000 : ℚ) / 1, (-5270634367458485381285894521937287347947540000 : ℚ) / 7, (3076133535714510725662123809352917281601094000 : ℚ) / 7, (-121247945526106766604642420215635805780914600 : ℚ) / 7, (-160328093614903007435445478829550728888627000 : ℚ) / 7, (40298872002372484604007789920188099950819280 : ℚ) / 7, (138167098517326329953000741752197366587120 : ℚ) / 1, (-1830752156512785504261011055719260991445400 : ℚ) / 7, (249669126949762356191647968927760952412300 : ℚ) / 7, (32069291999367105323354733606834391368525 : ℚ) / 7, (-9035936763008271069739870782225976944645 : ℚ) / 7, (402950768781543369248361768385129332665 : ℚ) / 7, (195634790583717074926569087926201591425 : ℚ) / 7, (-11189197273648132684049734636035018200 : ℚ) / 7, (-772907530001630757167200055660915175 : ℚ) / 7, (47614745654498719762780663547104560 : ℚ) / 1, (22815398959447303219665734616320935 : ℚ) / 7]

def block48Margin0 : ℚ := (92055114720059554023379245110919981123640654708887444030572219151236920754120379428115057867 : ℚ) / 96207267430400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_0 : ∀ i : Fin 37, block48Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block48PowerCoefficients
      block48Margin0 (by norm_num) block48_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin1 : ℚ := (687094200371329208784181177610224085908311149354292477678217004293840900317934527 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_1 : ∀ i : Fin 37, block48Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block48PowerCoefficients
      block48Margin1 (by norm_num) block48_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin2 : ℚ := (3606510100859397234317929400263645310079562840982750995286078779062935569167365986191463341 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_2 : ∀ i : Fin 37, block48Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block48PowerCoefficients
      block48Margin2 (by norm_num) block48_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin3 : ℚ := (3387442952486656703221891592955582321057028804473280029898994950058982 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_3 : ∀ i : Fin 37, block48Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block48PowerCoefficients
      block48Margin3 (by norm_num) block48_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin4 : ℚ := (1177023033567742260429416087006117074176578088498555734776808647497 : ℚ) / 8264141345021879123968

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_4 : ∀ i : Fin 37, block48Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block48PowerCoefficients
      block48Margin4 (by norm_num) block48_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin5 : ℚ := (4708170799654657446692892035789017521097080376541481217135103524215 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_5 : ∀ i : Fin 37, block48Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block48PowerCoefficients
      block48Margin5 (by norm_num) block48_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin6 : ℚ := (223279584196624565484604726531488704433062335001308751707035091688181898908413007 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_6 : ∀ i : Fin 37, block48Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block48PowerCoefficients
      block48Margin6 (by norm_num) block48_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin7 : ℚ := (2800340868726531327254533414590618214854070643450030169672078136170899907401361819568385661 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_7 : ∀ i : Fin 37, block48Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block48PowerCoefficients
      block48Margin7 (by norm_num) block48_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block48Margin8 : ℚ := (5559566979092357936742332513829171782016896569957442881186818681864192 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block48_coefficient_bound_8 : ∀ i : Fin 37, block48Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block48PowerCoefficients) i := by
  decide +kernel

theorem block48_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block48Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block48PowerCoefficients
      block48Margin8 (by norm_num) block48_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block48_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block48PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block48_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block48_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block48_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block48_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block48_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block48_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block48_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block48_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block48_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
