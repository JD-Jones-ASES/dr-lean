import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (7,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block52PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-25290100026193079639135721143904000000000000000 : ℚ) / 1, (153292635426592018429694484070616840000000000000 : ℚ) / 1, (-523061574820611149055569395340234190050000000000 : ℚ) / 1, (1105738458846909606794701170380349952893750000000 : ℚ) / 1, (-1326899862536939365502604680263172103383437500000 : ℚ) / 1, (326982487055869362499130377585683181649062500000 : ℚ) / 1, (1833114884408296275480315202120237471057968750000 : ℚ) / 1, (-3299320095721134687276548588218751012542734375000 : ℚ) / 1, (2238079765234821907930981001931656928476675781250 : ℚ) / 1, (550304445189591463728941011937597032813402343750 : ℚ) / 1, (-2093280790963478958808125995955850590691810156250 : ℚ) / 1, (1223645509416680997800885701210190508957605468750 : ℚ) / 1, (248180978124925826563853137431658486202285343750 : ℚ) / 1, (-573788114656970764244472371867074696463235656250 : ℚ) / 1, (137938735530653930458938446009501987788921131250 : ℚ) / 1, (61026572181570278606989883295646939242733868750 : ℚ) / 1, (-52742172055442947398079186806846514071831825000 : ℚ) / 1, (8877443259208670673910054603351453355132450000 : ℚ) / 1, (13598985077395215288313836521211695276356650625 : ℚ) / 2, (-5200265230576956379149404322318480496726306875 : ℚ) / 2, (-143235048198295372992940389799030288253758000 : ℚ) / 1, (255728006137547750062134562203519560600668375 : ℚ) / 1, (-67446462420819632011681346346172265462891515 : ℚ) / 2, (-7752053156319861336016144630118909840230730 : ℚ) / 1, (3745820966796174506495383701121521565488901 : ℚ) / 1, (-99361694157680331235865533991013051610326 : ℚ) / 1, (-108532897955625922380868229836308431240200 : ℚ) / 1, (50350447036441461079812519797182076931505 : ℚ) / 2, (3998599681916997058306526743986513884355 : ℚ) / 2, (-1040986617067644233775510065887259456623 : ℚ) / 2, (155298962323733799153763511201601629923 : ℚ) / 2, (34401366004810621840593294989393135875 : ℚ) / 2, (-440410809271282416770198101468368875 : ℚ) / 1, (150074673703016973796919129220265005 : ℚ) / 2, (39877349485642677801328805720700069 : ℚ) / 1, (4563079791889460643933146923264187 : ℚ) / 2]

def block52Margin0 : ℚ := (123145229064541486581749333662018098936171820149992437202826171672941610972296603285976868947 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_0 : ∀ i : Fin 37, block52Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block52PowerCoefficients
      block52Margin0 (by norm_num) block52_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin1 : ℚ := (829584298039805837909439447254894913232644540764270131835127969473329158404066067 : ℚ) / 2000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_1 : ∀ i : Fin 37, block52Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block52PowerCoefficients
      block52Margin1 (by norm_num) block52_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin2 : ℚ := (26320471253319610288023291510261703161748868246047811759321925492433013772987234809597308947 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_2 : ∀ i : Fin 37, block52Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block52PowerCoefficients
      block52Margin2 (by norm_num) block52_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin3 : ℚ := (1557467275712258994817636850464692901271074707003588962919935577582501 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_3 : ∀ i : Fin 37, block52Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block52PowerCoefficients
      block52Margin3 (by norm_num) block52_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin4 : ℚ := (31635040035999452899680885585720516507771256674045152819125667045289355529 : ℚ) / 338765337939180257280000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_4 : ∀ i : Fin 37, block52Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block52PowerCoefficients
      block52Margin4 (by norm_num) block52_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin5 : ℚ := (897998209141623532593466662115089920780781016676027773528693160499 : ℚ) / 9444732965739290427392

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_5 : ∀ i : Fin 37, block52Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block52PowerCoefficients
      block52Margin5 (by norm_num) block52_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin6 : ℚ := (243949117156308471970380251076276734660111100097995317467030457192809581515759787 : ℚ) / 2000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_6 : ∀ i : Fin 37, block52Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block52PowerCoefficients
      block52Margin6 (by norm_num) block52_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin7 : ℚ := (23868829356470356545274407771638401386176641943675850291961020885492463030722766329028124067 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_7 : ∀ i : Fin 37, block52Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block52PowerCoefficients
      block52Margin7 (by norm_num) block52_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block52Margin8 : ℚ := (3613559707352067413156066453443821143981340003584173534966827757387776 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block52_coefficient_bound_8 : ∀ i : Fin 37, block52Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block52PowerCoefficients) i := by
  decide +kernel

theorem block52_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block52Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block52PowerCoefficients
      block52Margin8 (by norm_num) block52_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block52_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block52PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block52_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block52_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block52_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block52_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block52_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block52_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block52_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block52_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block52_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
