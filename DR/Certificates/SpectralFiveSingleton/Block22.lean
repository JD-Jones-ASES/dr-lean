import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (3,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block22PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-155689637973166215363867392069984000000000000000 : ℚ) / 7, (2805766447668754647504854946738748880000000000000 : ℚ) / 21, (-3198139356490739451273628095577741651300000000000 : ℚ) / 7, (6847970767155756994297170883983389961943750000000 : ℚ) / 7, (-1200053027732353368517750789114951112683125000000 : ℚ) / 1, (7413303056749033187626361377117797633588125000000 : ℚ) / 21, (11110045594354640787742225392014646502299375000000 : ℚ) / 7, (-21288312570690157122961263795649042649342500000000 : ℚ) / 7, (49494504367670943232546614778920133211542625000000 : ℚ) / 21, (-248382835074351625656975485894175992899937500000 : ℚ) / 21, (-31324593085027359841963320937112955838469668750000 : ℚ) / 21, (22187923140036912392573389000166165143893287500000 : ℚ) / 21, (1204361938568369642630832915434742930483142750000 : ℚ) / 21, (-7568266412221102924858951348334285279325758000000 : ℚ) / 21, (2300210496890609469167192330360110064814614800000 : ℚ) / 21, (629156957285894542703456291189365563287674400000 : ℚ) / 21, (-513102861505066682738452560700293100667236662500 : ℚ) / 21, (110706937588817530891457821775005470314733387500 : ℚ) / 21, (28528257560438167723779552554628620574295390000 : ℚ) / 21, (-25066544065482347360355288555385182510385205000 : ℚ) / 21, (3737384010197990531931614659869342331149263500 : ℚ) / 21, (663104120191127432229941364567762467153400000 : ℚ) / 7, (-72426002876437233058573701589796599062018280 : ℚ) / 3, (-51246759962030306702658550994620084730345680 : ℚ) / 21, (20442747603517532656065131102091920840397928 : ℚ) / 21, (-2062620896364345646861376958635577901492916 : ℚ) / 21, (-69134672507847649169782738102129510345520 : ℚ) / 3, (34021250844677321351020276540010630388560 : ℚ) / 7, (-4233196489789083382543891290641584470355 : ℚ) / 42, (-5350913576157112107128144602596703058029 : ℚ) / 42, (296913750913370473880423546151218899633 : ℚ) / 42, (12919304554578242871712698769027883795 : ℚ) / 14, (-4746611537704327842345706654164964595 : ℚ) / 21, (-153272987480069861107903853672517525 : ℚ) / 14, (38290191297159387142569450269129917 : ℚ) / 21, (4563079791889460643933146923264187 : ℚ) / 42]

def block22Margin0 : ℚ := (968557213991463976223223023487590566707979805831997371325454846712633041009180653594008370289 : ℚ) / 962072674304000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_0 : ∀ i : Fin 37, block22Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block22PowerCoefficients
      block22Margin0 (by norm_num) block22_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin1 : ℚ := (8085402614091121932634573603038867140104864398067952911829062844436355273839855009 : ℚ) / 14000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_1 : ∀ i : Fin 37, block22Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block22PowerCoefficients
      block22Margin1 (by norm_num) block22_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin2 : ℚ := (51448007945491650065370575898574462636173302657766014441386038659169731272339223971937853447 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_2 : ∀ i : Fin 37, block22Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block22PowerCoefficients
      block22Margin2 (by norm_num) block22_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin3 : ℚ := (30020570585668536638415628593819860992573534740850913793991685359355247 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_3 : ∀ i : Fin 37, block22Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block22PowerCoefficients
      block22Margin3 (by norm_num) block22_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin4 : ℚ := (6016757963442143692826012969086010408726377490027321879354669298720709297 : ℚ) / 21416199524890705920000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_4 : ∀ i : Fin 37, block22Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block22PowerCoefficients
      block22Margin4 (by norm_num) block22_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin5 : ℚ := (2667422786724550922733657252159558046899910223786634720852978779943 : ℚ) / 9444732965739290427392

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_5 : ∀ i : Fin 37, block22Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block22PowerCoefficients
      block22Margin5 (by norm_num) block22_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin6 : ℚ := (4338355928074755777565940956635956687547815210440837428103736928841713891189176169 : ℚ) / 14000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_6 : ∀ i : Fin 37, block22Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block22PowerCoefficients
      block22Margin6 (by norm_num) block22_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin7 : ℚ := (50476773859115820984427229367564237692648883843240327144004782584370665212690212170883084887 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_7 : ∀ i : Fin 37, block22Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block22PowerCoefficients
      block22Margin7 (by norm_num) block22_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block22Margin8 : ℚ := (46528318814079858602815626921566539411183941180970530657592549372588032 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block22_coefficient_bound_8 : ∀ i : Fin 37, block22Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block22PowerCoefficients) i := by
  decide +kernel

theorem block22_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block22Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block22PowerCoefficients
      block22Margin8 (by norm_num) block22_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block22_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block22PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block22_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block22_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block22_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block22_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block22_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block22_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block22_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block22_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block22_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
