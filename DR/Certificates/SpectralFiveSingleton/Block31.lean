import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (4,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block31PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-157546672971232420287578593641120000000000000000 : ℚ) / 7, (134633190111380182041919519798915400000000000000 : ℚ) / 1, (-3205919217218409087603766294245445593850000000000 : ℚ) / 7, (6863487592147932552795889903496833884615625000000 : ℚ) / 7, (-8613683415486038485271502911809593994327421875000 : ℚ) / 7, (3556936308280049661869343093698213424330351562500 : ℚ) / 7, (8116490863640734652171403671328847714020722656250 : ℚ) / 7, (-16070815034449920911169696961102021731161103515625 : ℚ) / 7, (10684001076723714426128844313310961907208087890625 : ℚ) / 7, (3474927526200968567051523085869641218707009765625 : ℚ) / 7, (-10372946857963868384238442571491316629685739453125 : ℚ) / 7, (5293593737570634301085799150798559533173837109375 : ℚ) / 7, (1934065010863806158445650990861938121619712093750 : ℚ) / 7, (-5352597615102022872719381695686209790682128953125 : ℚ) / 14, (376782238869636607018993505743431767969294918750 : ℚ) / 7, (109208097602074133342279588552722062070232690625 : ℚ) / 2, (-188679947494538560186255717697061133056260446875 : ℚ) / 7, (27293170269099276691736272834242757251467721875 : ℚ) / 14, (25291668840424957757625401951857662614347463125 : ℚ) / 7, (-17589927570907755627516017831788887610641891875 : ℚ) / 14, (-318253928759188155981145416666844321351003500 : ℚ) / 7, (1112686361258362771370149198487619209258849750 : ℚ) / 7, (-137603435963968755010995860034982941300142640 : ℚ) / 7, (-7521106204568413814713884850581046455129530 : ℚ) / 1, (11525872749004409620811330740640876027608852 : ℚ) / 7, (-45778684730313587670278231982093301193102 : ℚ) / 7, (-500730143982944482802124117251465024571800 : ℚ) / 7, (58558335734413235347036066467747382140580 : ℚ) / 7, (6545901787569754857570208243394125435630 : ℚ) / 7, (-340713054930253180315742093845657835414 : ℚ) / 1, (44905378297540465214592988080191870198 : ℚ) / 7, (39567828970582392537829356283865950550 : ℚ) / 7, (-3134109468220199613100592401622571150 : ℚ) / 7, (-307614017141612485675002323527562295 : ℚ) / 7, (59915221615244222368165668296773238 : ℚ) / 7, (4563079791889460643933146923264187 : ℚ) / 7]

def block31Margin0 : ℚ := (479067129991031892498078037962930258203122783166723743410080493728433207867679586366914210947 : ℚ) / 481036337152000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_0 : ∀ i : Fin 37, block31Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block31PowerCoefficients
      block31Margin0 (by norm_num) block31_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin1 : ℚ := (3921238184162593164629737960150983982639897532014034873564466849854949647490917067 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_1 : ∀ i : Fin 37, block31Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block31PowerCoefficients
      block31Margin1 (by norm_num) block31_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin2 : ℚ := (24317329809094010069110667353521523188148196880904243996253377160571707315522578215939980421 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_2 : ∀ i : Fin 37, block31Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block31PowerCoefficients
      block31Margin2 (by norm_num) block31_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin3 : ℚ := (27865566886568192736042201921381949447250027388198858846304764475798002 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_3 : ∀ i : Fin 37, block31Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block31PowerCoefficients
      block31Margin3 (by norm_num) block31_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin4 : ℚ := (69288069443556047043736293594899298180768708127117461370666053619310796331 : ℚ) / 266172765523641630720000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_4 : ∀ i : Fin 37, block31Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block31PowerCoefficients
      block31Margin4 (by norm_num) block31_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin5 : ℚ := (1238021099116112085369855423275945022031016597604425250140642445957 : ℚ) / 4722366482869645213696

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_5 : ∀ i : Fin 37, block31Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block31PowerCoefficients
      block31Margin5 (by norm_num) block31_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin6 : ℚ := (2040272735304052554242285885659202480751642170011343304109383962894771387335256787 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_6 : ∀ i : Fin 37, block31Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block31PowerCoefficients
      block31Margin6 (by norm_num) block31_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin7 : ℚ := (24141070379969910234338309574806903552771605501646799713862795658741972220271929627828758581 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_7 : ∀ i : Fin 37, block31Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block31PowerCoefficients
      block31Margin7 (by norm_num) block31_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block31Margin8 : ℚ := (45201163042005255789798029170914618120900362682717475188905985448599552 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block31_coefficient_bound_8 : ∀ i : Fin 37, block31Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block31PowerCoefficients) i := by
  decide +kernel

theorem block31_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block31Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block31PowerCoefficients
      block31Margin8 (by norm_num) block31_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block31_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block31PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block31_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block31_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block31_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block31_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block31_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block31_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block31_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block31_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block31_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
