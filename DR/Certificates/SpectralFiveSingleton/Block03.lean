import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (0,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block03PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-18795424288820033910345236355168000000000000000 : ℚ) / 1, (108483630274431329764834047410703000000000000000 : ℚ) / 1, (-364835814194481526070752991272043818750000000000 : ℚ) / 1, (795703211050066347454131181952533896875000000000 : ℚ) / 1, (-1076540530230575283915086997416604287500000000000 : ℚ) / 1, (733309786638415818890751742703188084375000000000 : ℚ) / 1, (246990388100416238456441699978874923593750000000 : ℚ) / 1, (-932494282647927051652492450054099221250000000000 : ℚ) / 1, (573347558935945305554372379646315948734375000000 : ℚ) / 1, (394200891045059376253087123851744635179687500000 : ℚ) / 1, (-666835080677555657432011010860105698838750000000 : ℚ) / 1, (178877752852659502941545648425291748262187500000 : ℚ) / 1, (258148815745082288096561930582439044318187500000 : ℚ) / 1, (-133886352205308021798557461715155783985375000000 : ℚ) / 1, (-27133408333231987445925108540966600404265625000 : ℚ) / 1, (30972452029293506761941509781354377742195312500 : ℚ) / 1, (-3872848294159293879627870437586396549957812500 : ℚ) / 1, (-2486315587297264649314720427816060061550000000 : ℚ) / 1, (1182235355436520263006170007160728633041875000 : ℚ) / 1, (-118860034483588430717271416854102743976562500 : ℚ) / 1, (-48709329533074094948975639117945301500825000 : ℚ) / 1, (73605440312583874882534327087868529634668750 : ℚ) / 1, (7448994804594754186225580061370202249047500 : ℚ) / 1, (-3906691703958200307305795238028181987172500 : ℚ) / 1, (39639970478198814896618236437299353625000 : ℚ) / 1, (158255939481523385530908838451567416681250 : ℚ) / 1, (-4871403745707543544867493251409407850000 : ℚ) / 1, (-963678378356503032629298767028221515000 : ℚ) / 1, (755235861298341388017367251579729140000 : ℚ) / 1, (59279424001286580889465299877414687500 : ℚ) / 1, (-3560242008526697091391861527961562500 : ℚ) / 1, (1017386394371764995961428061918743750 : ℚ) / 1, (235335955404835748670013125203277500 : ℚ) / 1, (10782324650022355018745621274253750 : ℚ) / 1, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block03Margin0 : ℚ := (154843490954908281853581716553468558365512437915282155276897091257521446151955070669843 : ℚ) / 137438953472000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_0 : ∀ i : Fin 37, block03Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block03PowerCoefficients
      block03Margin0 (by norm_num) block03_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin1 : ℚ := (5969321731164382937356319597574490723275541707775816850519279465336219595123 : ℚ) / 8000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_1 : ∀ i : Fin 37, block03Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block03PowerCoefficients
      block03Margin1 (by norm_num) block03_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin2 : ℚ := (76420828678344180686108906049954424343898477753682939335362016489777261253998960182427 : ℚ) / 137438953472000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_2 : ∀ i : Fin 37, block03Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block03PowerCoefficients
      block03Margin2 (by norm_num) block03_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin3 : ℚ := (441806634163920731845920562351742556625046742182840199168616677276 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_3 : ∀ i : Fin 37, block03Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block03PowerCoefficients
      block03Margin3 (by norm_num) block03_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin4 : ℚ := (110066896231933434007187062521557062914583012659100969160486509573359 : ℚ) / 241467879924858030653440

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_4 : ∀ i : Fin 37, block03Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block03PowerCoefficients
      block03Margin4 (by norm_num) block03_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin5 : ℚ := (67318204286484572274651936379677070120782212434790655834754831875 : ℚ) / 147573952589676412928

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_5 : ∀ i : Fin 37, block03Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block03PowerCoefficients
      block03Margin5 (by norm_num) block03_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin6 : ℚ := (3837342417530858660549816896451960205914151358114026376745202827688358980867 : ℚ) / 8000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_6 : ∀ i : Fin 37, block03Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block03PowerCoefficients
      block03Margin6 (by norm_num) block03_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin7 : ℚ := (73998896795550585641166703078054434786945973066407555602820839362676726826678559954227 : ℚ) / 137438953472000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_7 : ∀ i : Fin 37, block03Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block03PowerCoefficients
      block03Margin7 (by norm_num) block03_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block03Margin8 : ℚ := (593539851773317079141706628687956570534834623144528060744724332544 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block03_coefficient_bound_8 : ∀ i : Fin 37, block03Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block03PowerCoefficients) i := by
  decide +kernel

theorem block03_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block03Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block03PowerCoefficients
      block03Margin8 (by norm_num) block03_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block03_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block03PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block03_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block03_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block03_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block03_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block03_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block03_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block03_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block03_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block03_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
