import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (7,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block51PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-25621360079000711125212812802304000000000000000 : ℚ) / 1, (474143453813090575284820699866001520000000000000 : ℚ) / 3, (-548253510776332963029367651106708853800000000000 : ℚ) / 1, (1179121219324748397927689521838591214746875000000 : ℚ) / 1, (-4326022582040110229802997377005268087244062500000 : ℚ) / 3, (1080241304339987840940519918410251598513750000000 : ℚ) / 3, (6363939678629048361992134596821916324584843750000 : ℚ) / 3, (-12112059939336451625651343858213431518206367187500 : ℚ) / 3, (9532057522388233903121222031065532298843308593750 : ℚ) / 3, (-62313776621496013109906691530008121789691406250 : ℚ) / 1, (-6270271677995724624992186677228441460955000781250 : ℚ) / 3, (4734545529593739934177351068874837937387853906250 : ℚ) / 3, (-30127021431725515261197824643350553730372093750 : ℚ) / 3, (-1657297923366694455216452629720132843910165609375 : ℚ) / 3, (207361712688564598551508343416741072251098943750 : ℚ) / 1, (31249795473454185023650307084704136309392928125 : ℚ) / 1, (-154830190351043310684013918182208190388423725000 : ℚ) / 3, (40521152219309520531900106808490148210554165625 : ℚ) / 3, (13354430487239498688998140118505120043150452500 : ℚ) / 3, (-7875119248249690266218436054288323164928438125 : ℚ) / 3, (126827713873753403015502195701554727031042000 : ℚ) / 1, (573875132574494328315061751990966596769891500 : ℚ) / 3, (-128313277639422343133445465715013887383100960 : ℚ) / 3, (-8614901893519650207766956243817488607053110 : ℚ) / 3, (9052192493540930430513866221409112961227428 : ℚ) / 3, (-653250819645992142753139507047457053965572 : ℚ) / 3, (-178445417927683822349763918252508179638120 : ℚ) / 3, (62609083788238623431245654113672632043250 : ℚ) / 3, (2312552958666705533236761375814079442190 : ℚ) / 3, (-893699913293328259310813080289025804862 : ℚ) / 3, (73891668543854416464081502033909341846 : ℚ) / 1, (33920318836583112229769453894438038190 : ℚ) / 3, (-210665809398906165505751191260946620 : ℚ) / 1, (301551229016937020507589976986903035 : ℚ) / 3, (88880858555064276890523905287928512 : ℚ) / 3, (4563079791889460643933146923264187 : ℚ) / 3]

def block51Margin0 : ℚ := (61064045599765589644544277927187960716182826269171468937380806827429954612909370974862722809 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_0 : ∀ i : Fin 37, block51Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block51PowerCoefficients
      block51Margin0 (by norm_num) block51_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin1 : ℚ := (410268648115699330906547420390563501449436025561459290337225947186475066875564269 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_1 : ∀ i : Fin 37, block51Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block51PowerCoefficients
      block51Margin1 (by norm_num) block51_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin2 : ℚ := (13256562413567082047554033195381481010305527093785994780912981007206819756034464566912941769 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_2 : ∀ i : Fin 37, block51Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block51PowerCoefficients
      block51Margin2 (by norm_num) block51_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin3 : ℚ := (1664206967326393436355271009259168829146910113417247992739573876433374 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_3 : ∀ i : Fin 37, block51Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block51PowerCoefficients
      block51Margin3 (by norm_num) block51_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin4 : ℚ := (2123592812081460201136414177922595771585809255085300619542002237240669127709 : ℚ) / 20381215399870464000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_4 : ∀ i : Fin 37, block51Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block51PowerCoefficients
      block51Margin4 (by norm_num) block51_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin5 : ℚ := (507687494681283418949727361755837921859502814724938498010282191225 : ℚ) / 4722366482869645213696

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_5 : ∀ i : Fin 37, block51Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block51PowerCoefficients
      block51Margin5 (by norm_num) block51_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin6 : ℚ := (138829499991216803683023622782505033794876318373192498950714757193497211098216989 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_6 : ∀ i : Fin 37, block51Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block51PowerCoefficients
      block51Margin6 (by norm_num) block51_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin7 : ℚ := (13394031362005120955663332649466304153567928311104225910782741145994946034688523364187828569 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_7 : ∀ i : Fin 37, block51Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block51PowerCoefficients
      block51Margin7 (by norm_num) block51_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block51Margin8 : ℚ := (3998733860789775963348110848669594865289844910152818663093200071163904 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block51_coefficient_bound_8 : ∀ i : Fin 37, block51Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block51PowerCoefficients) i := by
  decide +kernel

theorem block51_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block51Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block51PowerCoefficients
      block51Margin8 (by norm_num) block51_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block51_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block51PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block51_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block51_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block51_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block51_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block51_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block51_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block51_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block51_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block51_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
