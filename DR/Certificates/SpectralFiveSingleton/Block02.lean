import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (0,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block02PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-19126684341627665396422328013568000000000000000 : ℚ) / 1, (328176184566826488467305606925951000000000000000 : ℚ) / 3, (-1090411535457943059081160481949076300000000000000 : ℚ) / 3, (2319584462693075321161594529639563700000000000000 : ℚ) / 3, (-2955546493823007434659301735911459300000000000000 : ℚ) / 3, (1511010406929154147980586785164886700000000000000 : ℚ) / 3, (634044604352573954334943010653359365000000000000 : ℚ) / 1, (-1375295449124166542818198137580166272500000000000 : ℚ) / 1, (2595746909498236405621006715781908906750000000000 : ℚ) / 3, (371414031013101191882050101933096661750000000000 : ℚ) / 1, (-2490953402970386795624609934305495936860000000000 : ℚ) / 3, (948882458264045347434224577138913240715000000000 : ℚ) / 3, (698025169807928856102322487191793954153000000000 : ℚ) / 3, (-514435981412333304309536103512696442378250000000 : ℚ) / 3, (-9426227675615952068639339008287855912625000000 : ℚ) / 1, (88800078616613240629001803791253050710875000000 : ℚ) / 3, (-7002091193830187584667219998690980338200000000 : ℚ) / 1, (-4800929780141834760880677351318771508225000000 : ℚ) / 3, (3031458193009294678750268222749606819235000000 : ℚ) / 3, (-853926740730227094540022374692092810842500000 : ℚ) / 3, (-17418031406112619092606686150398855888950000 : ℚ) / 1, (210377851424768429566724811756498642128900000 : ℚ) / 3, (9411590153029891406950243556974337943580000 : ℚ) / 3, (-3059832129293831315454334214907613026640000 : ℚ) / 1, (197120294217461929431578301265447335600000 : ℚ) / 1, (113496012972979913268169691943283386250000 : ℚ) / 1, (-15340993991573625064920306047324824037500 : ℚ) / 3, (346004476424879611483620050817980117500 : ℚ) / 3, (1805202189748393438778803314485218742500 : ℚ) / 3, (112012195505709726179599848563044962500 : ℚ) / 3, (-1152849926915071968711949534724450000 : ℚ) / 1, (2938154216087586292393814224290662500 : ℚ) / 3, (513801209409760917415008735503570000 : ℚ) / 3, (21564649300044710037491242548507500 : ℚ) / 3, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block02Margin0 : ℚ := (76443407443395959245944416860316704362227122717950941827943883343721299802942529611321 : ℚ) / 68719476736000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_0 : ∀ i : Fin 37, block02Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block02PowerCoefficients
      block02Margin0 (by norm_num) block02_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin1 : ℚ := (2887825985963034317475331484493325720200855043316914410141844827435189290061 : ℚ) / 4000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_1 : ∀ i : Fin 37, block02Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block02PowerCoefficients
      block02Margin1 (by norm_num) block02_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin2 : ℚ := (36069411233933460168174385334146307185338825494266197460173778179392973914000477493729 : ℚ) / 68719476736000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_2 : ∀ i : Fin 37, block02Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block02PowerCoefficients
      block02Margin2 (by norm_num) block02_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin3 : ℚ := (407810570736623993016721255897575545303715556838630461608215329224 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_3 : ∀ i : Fin 37, block02Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block02PowerCoefficients
      block02Margin3 (by norm_num) block02_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin4 : ℚ := (30593399031602091838892038086131820540482992029804764402907515625 : ℚ) / 73786976294838206464

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_4 : ∀ i : Fin 37, block02Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block02PowerCoefficients
      block02Margin4 (by norm_num) block02_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin5 : ℚ := (61184754016501952256924162915033949218071644026772441517473458375 : ℚ) / 147573952589676412928

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_5 : ∀ i : Fin 37, block02Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block02PowerCoefficients
      block02Margin5 (by norm_num) block02_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin6 : ℚ := (1728690593578457569246015244516923728532769273863357940292191546077410487749 : ℚ) / 4000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_6 : ∀ i : Fin 37, block02Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block02PowerCoefficients
      block02Margin6 (by norm_num) block02_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin7 : ℚ := (33174548315654076758429306641210898567178938484678315156823800336461857625553414887689 : ℚ) / 68719476736000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_7 : ∀ i : Fin 37, block02Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block02PowerCoefficients
      block02Margin7 (by norm_num) block02_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block02Margin8 : ℚ := (530392511532969132079952265514606715187268803460358939891421413376 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block02_coefficient_bound_8 : ∀ i : Fin 37, block02Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block02PowerCoefficients) i := by
  decide +kernel

theorem block02_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block02Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block02PowerCoefficients
      block02Margin8 (by norm_num) block02_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block02_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block02PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block02_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block02_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block02_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block02_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block02_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block02_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block02_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block02_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block02_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
