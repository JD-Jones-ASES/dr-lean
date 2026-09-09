import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (2,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block14PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-151513782605446590037616548890048000000000000000 : ℚ) / 7, (128548224312772001171636661167058840000000000000 : ℚ) / 1, (-9164944127896318673892330609727207368800000000000 : ℚ) / 21, (6491677230868058497636603564003044588000000000000 : ℚ) / 7, (-23519190155318285698623865992470499875360000000000 : ℚ) / 21, (5901409522545880974520035806367432159200000000000 : ℚ) / 21, (11167191033682232485202072618974576074280000000000 : ℚ) / 7, (-8940560745244798050817071940806606438100000000000 : ℚ) / 3, (48229439222434917712753908935801898652534000000000 : ℚ) / 21, (-597608508253061175937740965352227753270000000000 : ℚ) / 21, (-9928305506085576834205496208952165243488800000000 : ℚ) / 7, (21148960995595155490468026353236454988760600000000 : ℚ) / 21, (1009072235891778954434801212587738509409608000000 : ℚ) / 21, (-1002256480107264551948022999100672114452670000000 : ℚ) / 3, (2140665294839699851133026004066451752242186600000 : ℚ) / 21, (542696182972088516771769375384072146152663000000 : ℚ) / 21, (-463506852982422283458098128745191104516963200000 : ℚ) / 21, (102716969438785181607646727943533157768767000000 : ℚ) / 21, (21610485023445210302423566741402322774133880000 : ℚ) / 21, (-22371203024690661496426310078745737453886100000 : ℚ) / 21, (3711324293565177095890402577337196451544142000 : ℚ) / 21, (552442581610048556871995389038598198675452000 : ℚ) / 7, (-147784758690672326614759063835925620943785440 : ℚ) / 7, (-30614182173855875042342106483847580359534400 : ℚ) / 21, (17087129460082222348041089005522926713667376 : ℚ) / 21, (-1852444971059686122369225077237175153791920 : ℚ) / 21, (-92334647197302994892801283764943139542240 : ℚ) / 7, (82785860106512683369178177220709003393120 : ℚ) / 21, (-3641935205542376610190927077243675919040 : ℚ) / 21, (-520150383975339862476383964186761877288 : ℚ) / 7, (141509755922128054526929131505789615240 : ℚ) / 21, (219460978838900556233541499288908140 : ℚ) / 1, (-3013939541902948308685944168964893610 : ℚ) / 21, (-75390013952956306291069383949582220 : ℚ) / 21, (9126159583778921287866293846528374 : ℚ) / 21, (0 : ℚ) / 1]

def block14Margin0 : ℚ := (1762964925927298693489066799391274508341473243326368926775778676621827510217180272023299047 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_0 : ∀ i : Fin 37, block14Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block14PowerCoefficients
      block14Margin0 (by norm_num) block14_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin1 : ℚ := (210937417499763557482370932469700921492419518059540380262929040925147856343047529 : ℚ) / 350000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_1 : ∀ i : Fin 37, block14Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block14PowerCoefficients
      block14Margin1 (by norm_num) block14_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin2 : ℚ := (684646831054130928124152758912592025834355523095038898393504372106922105111173120851138829 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_2 : ∀ i : Fin 37, block14Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block14PowerCoefficients
      block14Margin2 (by norm_num) block14_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin3 : ℚ := (6418570231939672961875512566667858843488268152831572118855725738781508 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_3 : ∀ i : Fin 37, block14Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block14PowerCoefficients
      block14Margin3 (by norm_num) block14_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin4 : ℚ := (157119341653939751493765939470492027072468900474233036260311670842995153 : ℚ) / 528210987335626942054400000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_4 : ∀ i : Fin 37, block14Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block14PowerCoefficients
      block14Margin4 (by norm_num) block14_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin5 : ℚ := (1230905397765749639012236180163334218517377728256734940861784536049 : ℚ) / 4132070672510939561984

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_5 : ∀ i : Fin 37, block14Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block14PowerCoefficients
      block14Margin5 (by norm_num) block14_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin6 : ℚ := (112041339671367379440890839676278504612931296725651377303142309347605607937348603 : ℚ) / 350000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_6 : ∀ i : Fin 37, block14Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block14PowerCoefficients
      block14Margin6 (by norm_num) block14_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin7 : ℚ := (638947522379298966099838619375610949788578953324515680424238791551022517454845223799279121 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_7 : ∀ i : Fin 37, block14Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block14PowerCoefficients
      block14Margin7 (by norm_num) block14_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block14Margin8 : ℚ := (1324235287312952754125682843803342365282445577576083802637073866555392 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block14_coefficient_bound_8 : ∀ i : Fin 37, block14Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block14PowerCoefficients) i := by
  decide +kernel

theorem block14_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block14Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block14PowerCoefficients
      block14Margin8 (by norm_num) block14_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block14_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block14PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block14_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block14_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block14_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block14_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block14_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block14_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block14_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block14_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block14_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
