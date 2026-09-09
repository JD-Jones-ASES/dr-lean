import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (3,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block24PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-151051997233859374558788108852384000000000000000 : ℚ) / 7, (897623325627500585628576201932493960000000000000 : ℚ) / 7, (-3047458992061127839229171674010110772550000000000 : ℚ) / 7, (6552616159443206282605612536821275722221875000000 : ℚ) / 7, (-8363923425902111370270479268084930763901015625000 : ℚ) / 7, (3976278766109514657231330790483639240887343750000 : ℚ) / 7, (6484359172354480657978400615760611541953964843750 : ℚ) / 7, (-13613738020699040967458886778010538768467636718750 : ℚ) / 7, (8912688083768627610774765166340896745380191406250 : ℚ) / 7, (3382763498598808083775603244558596564578832031250 : ℚ) / 7, (-8934604122820672047212771106086018932149700781250 : ℚ) / 7, (599651113281414618160436040809379170468689062500 : ℚ) / 1, (1975694282212563516440002453935276867883000968750 : ℚ) / 7, (-2231491124432100551023600435814514869203263312500 : ℚ) / 7, (201061194696326589454188489806333756069423475000 : ℚ) / 7, (354626174945179421255499745019445588593928243750 : ℚ) / 7, (-19638440890215042009093661966615720809278475000 : ℚ) / 1, (3808614376388598928185506999943977842416481250 : ℚ) / 7, (41163703576969184559721482941728535969690369375 : ℚ) / 14, (-12792140661455481092505157465484948228888963125 : ℚ) / 14, (-343828605543984192038834419422916888906533000 : ℚ) / 7, (937287763296857629000187700199428175569560125 : ℚ) / 7, (-182950035094920440536955348457602713015668765 : ℚ) / 14, (-50188634692483647516761070998990794297088780 : ℚ) / 7, (7837715416091890401789408773379272809294151 : ℚ) / 7, (46908741517724413849586933847747824901982 : ℚ) / 1, (-398287755953111088261573213905029047369800 : ℚ) / 7, (9083736041322748158760322451409599964765 : ℚ) / 2, (12476279590673034153372043447738459124455 : ℚ) / 14, (-3398930373632888583634782673338823981723 : ℚ) / 14, (-10348193468581338626610147289362830911 : ℚ) / 2, (51662981414038850789707409151492363775 : ℚ) / 14, (-277005307122594210125709968289573425 : ℚ) / 1, (-691349954586301597100882261230171795 : ℚ) / 14, (20037872129601544566836862576073169 : ℚ) / 7, (4563079791889460643933146923264187 : ℚ) / 14]

def block24Margin0 : ℚ := (989835829390105027340314631383811203243999179938480733310895394482210260934898350371599472947 : ℚ) / 962072674304000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_0 : ∀ i : Fin 37, block24Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block24PowerCoefficients
      block24Margin0 (by norm_num) block24_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin1 : ℚ := (8505530641972411615636676959087276884971039909327855198676127744367749841726648067 : ℚ) / 14000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_1 : ∀ i : Fin 37, block24Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block24PowerCoefficients
      block24Margin1 (by norm_num) block24_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin2 : ℚ := (55799933686406117275539048466327753510098102180902351161431739174970801458358533485799442421 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_2 : ∀ i : Fin 37, block24Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block24PowerCoefficients
      block24Margin2 (by norm_num) block24_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin3 : ℚ := (4746082809169734408244469259971166974356905644800650884974330025228643 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_3 : ∀ i : Fin 37, block24Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block24PowerCoefficients
      block24Margin3 (by norm_num) block24_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin4 : ℚ := (8146714093159103257700733491291455793744684595444853354544812419240726401269 : ℚ) / 26084931021316879810560000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_4 : ∀ i : Fin 37, block24Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block24PowerCoefficients
      block24Margin4 (by norm_num) block24_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin5 : ℚ := (20754119918351367906869689843914597357817942579642472723145194065299 : ℚ) / 66113130760175032991744

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_5 : ∀ i : Fin 37, block24Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block24PowerCoefficients
      block24Margin5 (by norm_num) block24_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin6 : ℚ := (4799386757705389587397155479734017922771081701707696603611818096693521461649873787 : ℚ) / 14000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_6 : ∀ i : Fin 37, block24Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block24PowerCoefficients
      block24Margin6 (by norm_num) block24_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin7 : ℚ := (55489683144018452306882784863556545328251282419792418216580350897607919285691900740450996581 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_7 : ∀ i : Fin 37, block24Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block24PowerCoefficients
      block24Margin7 (by norm_num) block24_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block24Margin8 : ℚ := (50907658342990424194946433255135749385966657345555039494038037627851776 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block24_coefficient_bound_8 : ∀ i : Fin 37, block24Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block24PowerCoefficients) i := by
  decide +kernel

theorem block24_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block24Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block24PowerCoefficients
      block24Margin8 (by norm_num) block24_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block24_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block24PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block24_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block24_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block24_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block24_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block24_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block24_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block24_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block24_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block24_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
