import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (4,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block29PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-162184313710539261092657876858720000000000000000 : ℚ) / 7, (2963273970704800755145303822639108400000000000000 : ℚ) / 21, (-10232252813995286526887212137392390837800000000000 : ℚ) / 21, (22074400625120637488388628623658505550771875000000 : ℚ) / 21, (-27277503706149341100802970017547777200888515625000 : ℚ) / 21, (7952025547139632567320222484137779721481914062500 : ℚ) / 21, (37251842303000042427804483420124370689099960937500 : ℚ) / 21, (-72557403907953991214548994464042971831665351562500 : ℚ) / 21, (58357810488657025243619682258459640812689351562500 : ℚ) / 21, (-1142775599071271233787412217812252959193304687500 : ℚ) / 7, (-11511316701079145178135919688144597343369206250000 : ℚ) / 7, (26651499836139403475741312716627429557753507031250 : ℚ) / 21, (-94238373949723307518991848890838910479346500000 : ℚ) / 7, (-8531982746373884146862044296294638819366450843750 : ℚ) / 21, (3120015005769910101603576444362933681988603662500 : ℚ) / 21, (179891758737835876102505662404373628809573193750 : ℚ) / 7, (-642239137104783382153303732733146518239671450000 : ℚ) / 21, (54144384731221279123694054509226036938800175000 : ℚ) / 7, (4310047458652554441778911506666838335878821250 : ℚ) / 3, (-10493466963798190790856040992106263145586570000 : ℚ) / 7, (5183441450124100540312675372346884631234639500 : ℚ) / 21, (2175336666543412478408821052967629943293419750 : ℚ) / 21, (-668258171943899662639910683002375688793007920 : ℚ) / 21, (-35390134652871906839458810382085898835313185 : ℚ) / 21, (26548042296792151904379857667590724792225206 : ℚ) / 21, (-166243658409453093463798185586535847835742 : ℚ) / 1, (-500313490764320872570201670120231598694780 : ℚ) / 21, (150643930442038444247197211943183525514985 : ℚ) / 21, (-6569734534545606740575331915282353704680 : ℚ) / 21, (-3192597846236619772851640304586681598304 : ℚ) / 21, (117315265907487842828191757756489860336 : ℚ) / 7, (27976662189624275566379754983124256760 : ℚ) / 21, (-2022217729172736371240543813084635730 : ℚ) / 7, (27544264617602864659367973947357375 : ℚ) / 7, (32139953316786635839876947894295578 : ℚ) / 7, (4563079791889460643933146923264187 : ℚ) / 21]

def block29Margin0 : ℚ := (469361119115403804230998732631679830454740167053372498598365963308048441820386456120201176289 : ℚ) / 481036337152000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_0 : ∀ i : Fin 37, block29Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block29PowerCoefficients
      block29Margin0 (by norm_num) block29_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin1 : ℚ := (3750026367598140313443666983751399189350915444650848676617625036166413522705518009 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_1 : ∀ i : Fin 37, block29Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block29PowerCoefficients
      block29Margin1 (by norm_num) block29_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin2 : ℚ := (22768039397580029606793708854437233280952500777381273734479174736679208977239284399978619447 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_2 : ∀ i : Fin 37, block29Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block29PowerCoefficients
      block29Margin2 (by norm_num) block29_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin3 : ℚ := (25905972653243992045304982574157237090891379467561340396939696993169494 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_3 : ∀ i : Fin 37, block29Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block29PowerCoefficients
      block29Margin3 (by norm_num) block29_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin4 : ℚ := (8779391455856265857562805887821325921723568011041766061825000178888025041347 : ℚ) / 36126147366170394624000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_4 : ∀ i : Fin 37, block29Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block29PowerCoefficients
      block29Margin4 (by norm_num) block29_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin5 : ℚ := (1159724637659394556646890297438324679287506485188943075646899434743 : ℚ) / 4722366482869645213696

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_5 : ∀ i : Fin 37, block29Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block29PowerCoefficients
      block29Margin5 (by norm_num) block29_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin6 : ℚ := (276189486013369816282286612137822364717708910000312215398138864479025169686828167 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_6 : ∀ i : Fin 37, block29Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block29PowerCoefficients
      block29Margin6 (by norm_num) block29_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin7 : ℚ := (23073311058545417844850693148778743863558910182649098300276188181000824757366713751957058887 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_7 : ∀ i : Fin 37, block29Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block29PowerCoefficients
      block29Margin7 (by norm_num) block29_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block29Margin8 : ℚ := (43415297493651714888502357320963349289036004180874695805870944593048064 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block29_coefficient_bound_8 : ∀ i : Fin 37, block29Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block29PowerCoefficients) i := by
  decide +kernel

theorem block29_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block29Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block29PowerCoefficients
      block29Margin8 (by norm_num) block29_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block29_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block29PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block29_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block29_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block29_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block29_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block29_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block29_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block29_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block29_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block29_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
