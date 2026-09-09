import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (1,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block10PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-138062645759113283101207139274912000000000000000 : ℚ) / 7, (806099866198179602658777048573750560000000000000 : ℚ) / 7, (-2721307500867032823980034888255969116250000000000 : ℚ) / 7, (5905517177657127180389661307340903773015625000000 : ℚ) / 7, (-7825942018411003018476273002018838858757812500000 : ℚ) / 7, (4773265055548684161927843348450888106414062500000 : ℚ) / 7, (3262422433384358484012875425096302721476562500000 : ℚ) / 7, (-8789401749227068742625457029659862185487500000000 : ℚ) / 7, (5517245199527252266964894152840562244026562500000 : ℚ) / 7, (437158074464489738796727665770092543845468750000 : ℚ) / 1, (-6075171380981662488849558053258747016929921875000 : ℚ) / 7, (2149495173121788958397744273395385708864618750000 : ℚ) / 7, (1928600303424084435341428019567034932042896875000 : ℚ) / 7, (-194137984838271935029389227686508997285497500000 : ℚ) / 1, (-12504416745887691050195852879665743123721250000 : ℚ) / 1, (273125289837457964778712137985259314461627500000 : ℚ) / 7, (-7913098889135195714089853165129403789364531250 : ℚ) / 1, (-10749378434327575115469333514293134106002093750 : ℚ) / 7, (12664936873819631577426270445222624607606625000 : ℚ) / 7, (-2392197131461902362781179027935503869046962500 : ℚ) / 7, (-393935746701659212262370772746037526238743750 : ℚ) / 7, (92189130424951612653808253424149971244799500 : ℚ) / 1, (5910113653909855421461481124180742665687250 : ℚ) / 7, (-38113814043950734088186706819634668611518700 : ℚ) / 7, (2291566889528664506510954561046224945448700 : ℚ) / 7, (967818421405364270401976082380361434246250 : ℚ) / 7, (-167050375492006161118420602065038203453000 : ℚ) / 7, (-1138348974483668110541873621734913976750 : ℚ) / 7, (6112455058554851426003030244209684492550 : ℚ) / 7, (-254898672348720984777904131948830965050 : ℚ) / 7, (-73323065255167297092309005957669950000 : ℚ) / 7, (10706603448734579563819430781220531250 : ℚ) / 7, (711356205011826444405578059457698250 : ℚ) / 7, (-141032806422292403645192726267239050 : ℚ) / 7, (-9919738678020566617245971572313450 : ℚ) / 7, (0 : ℚ) / 1]

def block10Margin0 : ℚ := (526361317333802810334487013432314725040444753038809632922337427930013204452868305069044111 : ℚ) / 481036337152000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_0 : ∀ i : Fin 37, block10Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block10PowerCoefficients
      block10Margin0 (by norm_num) block10_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin1 : ℚ := (9807613832155325859105410090636904346314107633687699885944210324385336222027421 : ℚ) / 14000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_1 : ∀ i : Fin 37, block10Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block10PowerCoefficients
      block10Margin1 (by norm_num) block10_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin2 : ℚ := (34848730152277543548052670064772953728792111386997155708003306088644055679666257819415291 : ℚ) / 68719476736000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_2 : ∀ i : Fin 37, block10Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block10PowerCoefficients
      block10Margin2 (by norm_num) block10_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin3 : ℚ := (347659598373177588680081593732014705352657018470136521397275943414152 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_3 : ∀ i : Fin 37, block10Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block10PowerCoefficients
      block10Margin3 (by norm_num) block10_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin4 : ℚ := (1199546054424958824063919165887850942116640993806340361505165952787826277 : ℚ) / 2924025108465077714944000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_4 : ∀ i : Fin 37, block10Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block10PowerCoefficients
      block10Margin4 (by norm_num) block10_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin5 : ℚ := (1698369106833770008457942591226317564223393828035895096789070847175 : ℚ) / 4132070672510939561984

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_5 : ∀ i : Fin 37, block10Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block10PowerCoefficients
      block10Margin5 (by norm_num) block10_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin6 : ℚ := (874122855153511284684157538555223718222069698953738136142864894921253525441061 : ℚ) / 2000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_6 : ∀ i : Fin 37, block10Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block10PowerCoefficients
      block10Margin6 (by norm_num) block10_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin7 : ℚ := (34188362506905385594811757835674044896344345090112242594538759132771903242921949148166279 : ℚ) / 68719476736000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_7 : ∀ i : Fin 37, block10Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block10PowerCoefficients
      block10Margin7 (by norm_num) block10_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block10Margin8 : ℚ := (486368804396304216210527943192147766003345194367419312768865271678976 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block10_coefficient_bound_8 : ∀ i : Fin 37, block10Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block10PowerCoefficients) i := by
  decide +kernel

theorem block10_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block10Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block10PowerCoefficients
      block10Margin8 (by norm_num) block10_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block10_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block10PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block10_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block10_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block10_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block10_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block10_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block10_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block10_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block10_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block10_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
