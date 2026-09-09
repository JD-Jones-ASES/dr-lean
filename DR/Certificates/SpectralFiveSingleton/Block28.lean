import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (4,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block28PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-164503134080192681495197518467520000000000000000 : ℚ) / 7, (1013171237781622629057071160756162800000000000000 : ℚ) / 7, (-3539111256991961614232706649776138637600000000000 : ℚ) / 7, (7732619948677878678854043768367228606515625000000 : ℚ) / 7, (-1390445293728092450735948981837614985827187500000 : ℚ) / 1, (3086321708106009328098824393668283636564062500000 : ℚ) / 7, (1879265800183067937376758105873253179294687500000 : ℚ) / 1, (-26659384017940980888396136453220698997996875000000 : ℚ) / 7, (3243874279825274265475553704916437992250562500000 : ℚ) / 1, (-3162735726791648264888903148947376293762968750000 : ℚ) / 7, (-11743339418032838465776312592323419837940065625000 : ℚ) / 7, (10275338214677937023153579218540818533437906250000 : ℚ) / 7, (-965679495518416254921831122666438184268768375000 : ℚ) / 7, (-2890590989795837219151227362405906934070273750000 : ℚ) / 7, (1326188511882287043406659685338710065683281325000 : ℚ) / 7, (86726338427026755392810043415512618675549750000 : ℚ) / 7, (-32982239049474422041250142770090128362109575000 : ℚ) / 1, (73735485053937431906043477890650923639993000000 : ℚ) / 7, (4656090012436440866383616133101767494484760000 : ℚ) / 7, (-11587625341626049172182850373737711148404050000 : ℚ) / 7, (2614579121037537600063057623706497047861884000 : ℚ) / 7, (603902599742692456769586652774260373867285000 : ℚ) / 7, (-38369595072193814828163197598562862701785020 : ℚ) / 1, (4463613322977576933673527618743679737320200 : ℚ) / 7, (1216597990385736851628754769433981146428936 : ℚ) / 1, (-1692440372723102380524169326855618771046240 : ℚ) / 7, (-43025228971149859541410329419687277452740 : ℚ) / 7, (51364104245498529031421104053765946165640 : ℚ) / 7, (-5878085157584912758858211471143961588280 : ℚ) / 7, (-83486754540171006451534976572678506904 : ℚ) / 1, (22454671236889386709646836749575791040 : ℚ) / 1, (-442326173840241911303032509556620360 : ℚ) / 1, (-1669288142077711854124372181610103020 : ℚ) / 7, (23807372827249359881390331773552280 : ℚ) / 1, (18252319167557842575732587693056748 : ℚ) / 7, (0 : ℚ) / 1]

def block28Margin0 : ℚ := (5810058170666480431390879422760225733950829753239554547998915315777515895590308844451051987 : ℚ) / 6012954214400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_0 : ∀ i : Fin 37, block28Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block28PowerCoefficients
      block28Margin0 (by norm_num) block28_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin1 : ℚ := (91886167244561236598902019580476220735765617424559585604757981833370044787223587 : ℚ) / 175000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_1 : ∀ i : Fin 37, block28Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block28PowerCoefficients
      block28Margin1 (by norm_num) block28_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin2 : ℚ := (276918379594053022738734835864008320518638999745628890752001480333077460784082950744180487 : ℚ) / 858993459200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_2 : ∀ i : Fin 37, block28Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block28PowerCoefficients
      block28Margin2 (by norm_num) block28_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin3 : ℚ := (5042992651198310215102608566186066726572734998540026246595297249271048 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_3 : ∀ i : Fin 37, block28Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block28PowerCoefficients
      block28Margin3 (by norm_num) block28_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin4 : ℚ := (451584575653151408932085587161172244267084569902923972995594028887231368497 : ℚ) / 1902246770654576640000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_4 : ∀ i : Fin 37, block28Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block28PowerCoefficients
      block28Margin4 (by norm_num) block28_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin5 : ℚ := (70980309548837375196235361977054487942199204506067664664530936821 : ℚ) / 295147905179352825856

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_5 : ∀ i : Fin 37, block28Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block28PowerCoefficients
      block28Margin5 (by norm_num) block28_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin6 : ℚ := (47617816678360603118551357250720196674601393780955165228560036738724569401104809 : ℚ) / 175000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_6 : ∀ i : Fin 37, block28Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block28PowerCoefficients
      block28Margin6 (by norm_num) block28_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin7 : ℚ := (285187901546772785660244569729816476674148993606363831283993238792362554316326063319721363 : ℚ) / 858993459200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_7 : ∀ i : Fin 37, block28Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block28PowerCoefficients
      block28Margin7 (by norm_num) block28_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block28Margin8 : ℚ := (8600110218856800868637450566722945642767433124338849941769595198654464 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block28_coefficient_bound_8 : ∀ i : Fin 37, block28Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block28PowerCoefficients) i := by
  decide +kernel

theorem block28_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block28Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block28PowerCoefficients
      block28Margin8 (by norm_num) block28_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block28_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block28PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block28_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block28_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block28_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block28_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block28_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block28_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block28_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block28_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block28_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
