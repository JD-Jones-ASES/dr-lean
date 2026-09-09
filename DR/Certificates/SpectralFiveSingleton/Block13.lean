import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (1,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block13PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-131106184650153021893588214448512000000000000000 : ℚ) / 7, (786484227479881642150769287687797560000000000000 : ℚ) / 7, (-2761456765869177585680134609692158070000000000000 : ℚ) / 7, (6499641458142625280115683816348898400359375000000 : ℚ) / 7, (-10304904530804266275603668931284440344312500000000 : ℚ) / 7, (11185359310021852617645099568146427276296875000000 : ℚ) / 7, (-7905847742100247285939205569461770217730468750000 : ℚ) / 7, (4472832796748822716030220666687337415474414062500 : ℚ) / 7, (-3865295615448079649268534578267480419596289062500 : ℚ) / 7, (4572049956109195606705726499205607593565742187500 : ℚ) / 7, (-1623036012027372625199691002122718543118320312500 : ℚ) / 7, (-2179101670421950388648003378235219145399131250000 : ℚ) / 7, (3035487216674629259455887760402721457298621875000 : ℚ) / 7, (-418335645798608301461036193877873853038701250000 : ℚ) / 7, (-687338089963047413003473334260531530155419375000 : ℚ) / 7, (342732031383133333478859255071081728681032187500 : ℚ) / 7, (181066887024386526068461939157501812005937500 : ℚ) / 7, (-42933543549399754621570712362050702924982562500 : ℚ) / 7, (26169057557959154353933353915759276196378562500 : ℚ) / 7, (339646830669465015012268828450381724892800000 : ℚ) / 1, (-1892591065198932418044882557487172231309000000 : ℚ) / 7, (873246701610786402477028405208758171058584000 : ℚ) / 7, (117270473398836261440219902815271363480652000 : ℚ) / 7, (-76078244192336670707500255124985297053791200 : ℚ) / 7, (799076015630125354656263449382555170168400 : ℚ) / 7, (2467819969621976863942031513084795969741000 : ℚ) / 7, (-349365619747094923563522459736037662437000 : ℚ) / 7, (-25814236060302614041868754174753594781500 : ℚ) / 7, (13948014875249751078192875098832848668300 : ℚ) / 7, (-330931147018252441764534811312009167100 : ℚ) / 7, (-207115960353432200832599829562696109500 : ℚ) / 7, (20492984981355362348551632720103880500 : ℚ) / 7, (2199499065209689359126697569304962500 : ℚ) / 7, (-242386658132502540821401566245224300 : ℚ) / 7, (-19839477356041133234491943144626900 : ℚ) / 7, (0 : ℚ) / 1]

def block13Margin0 : ℚ := (273378486942354500987075128087049586867609274435697787249767809347497598361584598239398871 : ℚ) / 240518168576000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_0 : ∀ i : Fin 37, block13Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block13PowerCoefficients
      block13Margin0 (by norm_num) block13_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin1 : ℚ := (5403188876261354356420264356841585731683006287160023247932134747421037042748801 : ℚ) / 7000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_1 : ∀ i : Fin 37, block13Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block13PowerCoefficients
      block13Margin1 (by norm_num) block13_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin2 : ℚ := (20546922891784841885795231811660424075312868896226285932833575052658132696909965279980211 : ℚ) / 34359738368000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_2 : ∀ i : Fin 37, block13Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block13PowerCoefficients
      block13Margin2 (by norm_num) block13_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin3 : ℚ := (433760410674138652092035493353348657566749529697268604595185588910064 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_3 : ∀ i : Fin 37, block13Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block13PowerCoefficients
      block13Margin3 (by norm_num) block13_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin4 : ℚ := (43714128084522758076544470047458876400113406611390206976897320297200297836829 : ℚ) / 83264729382912000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_4 : ∀ i : Fin 37, block13Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block13PowerCoefficients
      block13Margin4 (by norm_num) block13_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin5 : ℚ := (1096629541889686807890221574436612117800032252717009240833508124975 : ℚ) / 2066035336255469780992

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_5 : ∀ i : Fin 37, block13Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block13PowerCoefficients
      block13Margin5 (by norm_num) block13_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin6 : ℚ := (4017560657521095769340555181287481524643343155359930398118610823987724965456647 : ℚ) / 7000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_6 : ∀ i : Fin 37, block13Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block13PowerCoefficients
      block13Margin6 (by norm_num) block13_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin7 : ℚ := (22622534488957689315484194593901734136528801379168926315680550245762004771310183209049599 : ℚ) / 34359738368000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_7 : ∀ i : Fin 37, block13Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block13PowerCoefficients
      block13Margin7 (by norm_num) block13_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block13Margin8 : ℚ := (646945119233321153609488472720826736609212010346898445668264287649792 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block13_coefficient_bound_8 : ∀ i : Fin 37, block13Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block13PowerCoefficients) i := by
  decide +kernel

theorem block13_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block13Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block13PowerCoefficients
      block13Margin8 (by norm_num) block13_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block13_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block13PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block13_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block13_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block13_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block13_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block13_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block13_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block13_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block13_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block13_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
