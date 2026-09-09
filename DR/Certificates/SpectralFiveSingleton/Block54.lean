import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (7,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block54PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-24627579920577816666981537827104000000000000000 : ℚ) / 1, (433704312200906634124298301531673520000000000000 : ℚ) / 3, (-481522813420268652157374132837882518800000000000 : ℚ) / 1, (3017705752956247292727167018157964748500000000000 : ℚ) / 3, (-1253461154987516945662603817922139729266250000000 : ℚ) / 1, (1865911064731608380438242727067685129806250000000 : ℚ) / 3, (1987121498406600957757493768110762920723125000000 : ℚ) / 3, (-3404703340788015735611364105673866572956250000000 : ℚ) / 3, (-470013984932926941018388961420997882849171875000 : ℚ) / 3, (1934358084248550400026943175927516171973203125000 : ℚ) / 1, (-5927884546111354063108527493466749065082403125000 : ℚ) / 3, (340491119503315649074095950814823033836740625000 : ℚ) / 1, (2501116001486554648937564944428628861131214625000 : ℚ) / 3, (-1820831372526794857854837483776418596744297500000 : ℚ) / 3, (-20430355082543172793967433822544240529922775000 : ℚ) / 1, (372222993014958865526399408291303795308466000000 : ℚ) / 3, (-171812638460299460311545260284606461717998350000 : ℚ) / 3, (-1602858597646505945852954342002135470756125000 : ℚ) / 3, (36751992871435761045155414810239163650241327500 : ℚ) / 3, (-8113926486790249868132262181066457974672637500 : ℚ) / 3, (-671583034884586900005971123058272247618358000 : ℚ) / 1, (424903564921167733233083446358510851153041000 : ℚ) / 1, (-67478695488430726804415919966852784953786460 : ℚ) / 3, (-56744759183516497327120799679435661180689100 : ℚ) / 3, (5915331158901350829001139790379526796582376 : ℚ) / 1, (237151613804128320396897203997949992491960 : ℚ) / 3, (-694252006351170495072471997227266424403060 : ℚ) / 3, (115938094080515823056850285512621647087460 : ℚ) / 3, (8956622090428709653063058175782075756395 : ℚ) / 2, (-2253113890122797651791777771381186663803 : ℚ) / 2, (182648400206719180920233871802746761135 : ℚ) / 2, (180859437359057940009392890568290346365 : ℚ) / 6, (-1226707507559807330316513281503523385 : ℚ) / 1, (-26363626979385441799012546584934595 : ℚ) / 6, (181134428260655546430911440910443597 : ℚ) / 3, (22815398959447303219665734616320935 : ℚ) / 6]

def block54Margin0 : ℚ := (25066370180748445589027313202306300899322360276581917065518938092807547538538764476591743121 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_0 : ∀ i : Fin 37, block54Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block54PowerCoefficients
      block54Margin0 (by norm_num) block54_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin1 : ℚ := (6820570276743113771399653008912994584218021411455726799137211363719057806497529 : ℚ) / 16000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_1 : ∀ i : Fin 37, block54Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block54PowerCoefficients
      block54Margin1 (by norm_num) block54_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin2 : ℚ := (5267785643840980147083002854959369141976675243229988141750495106107352473972707860930231953 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_2 : ∀ i : Fin 37, block54Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block54PowerCoefficients
      block54Margin2 (by norm_num) block54_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin3 : ℚ := (276406745594620471472996189293796015724847211945271973973134310501151 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_3 : ∀ i : Fin 37, block54Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block54PowerCoefficients
      block54Margin3 (by norm_num) block54_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin4 : ℚ := (339720854084440879154801247709258444219680713351423142232780910313 : ℚ) / 4722366482869645213696

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_4 : ∀ i : Fin 37, block54Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block54PowerCoefficients
      block54Margin4 (by norm_num) block54_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin5 : ℚ := (679617277163002664479502760956434320292084446488167299701777556597 : ℚ) / 9444732965739290427392

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_5 : ∀ i : Fin 37, block54Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block54PowerCoefficients
      block54Margin5 (by norm_num) block54_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin6 : ℚ := (35490827971920884094449989628879681196580945934156456152923294996517998680932281 : ℚ) / 400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_6 : ∀ i : Fin 37, block54Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block54PowerCoefficients
      block54Margin6 (by norm_num) block54_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin7 : ℚ := (714542727616987110953119464181846512115616898594902651386314461716721692867204122964962317 : ℚ) / 5497558138880000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_7 : ∀ i : Fin 37, block54Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block54PowerCoefficients
      block54Margin7 (by norm_num) block54_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block54Margin8 : ℚ := (558337474684549052652223378926105996529155773400003930417697291567104 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block54_coefficient_bound_8 : ∀ i : Fin 37, block54Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block54PowerCoefficients) i := by
  decide +kernel

theorem block54_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block54Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block54PowerCoefficients
      block54Margin8 (by norm_num) block54_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block54_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block54PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block54_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block54_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block54_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block54_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block54_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block54_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block54_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block54_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block54_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
