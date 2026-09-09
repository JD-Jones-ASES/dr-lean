import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (3,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block27PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-144095536124899113351169184025984000000000000000 : ℚ) / 7, (854927179329638583474700875125922960000000000000 : ℚ) / 7, (-2945121488702075156151434183492092188800000000000 : ℚ) / 7, (6694477836888820891554769563537000676115625000000 : ℚ) / 7, (-10086868114245716175870737936267257326555312500000 : ℚ) / 7, (10014873219443123585906315364497001062035625000000 : ℚ) / 7, (-6160559007229274461366944205901573357884218750000 : ℚ) / 7, (3829856510102982812532257101657896402789726562500 : ℚ) / 7, (-6083396580737695002774078883867093137114535156250 : ℚ) / 7, (8766117755874809064002939624586867005437332031250 : ℚ) / 7, (-4824712244708754878819852898452389104441419531250 : ℚ) / 7, (-2125602120618739478425179254052291468075639843750 : ℚ) / 7, (659603453856216776270848031241404689486727593750 : ℚ) / 1, (-1509410476949040230061513051514796976750796859375 : ℚ) / 7, (-805177156686448974105638332653037821596190118750 : ℚ) / 7, (569431114381411864350478295835095503872936534375 : ℚ) / 7, (-103622242978536899828244657825517039011079200000 : ℚ) / 7, (-50568280204894093182867887775223835483766896875 : ℚ) / 7, (6595738717825683733594203642804819139919215000 : ℚ) / 1, (-2950816062423848502167901700094728503433738125 : ℚ) / 7, (-3094651541958279658179838203457001127605808000 : ℚ) / 7, (1579696640197212767208267099735025532490480000 : ℚ) / 7, (17634217875843700619787215066154167217575680 : ℚ) / 7, (-115001416453008135396212135942206392961924110 : ℚ) / 7, (12955517095029179532392717494031640166725476 : ℚ) / 7, (2044597667161939110687018304499041473659268 : ℚ) / 7, (-923747633315105024306799325632658685615180 : ℚ) / 7, (46412376051303445471115620226563223781510 : ℚ) / 7, (19930734443402643732902075657303213180970 : ℚ) / 7, (-3550610632253465073912762912390413629834 : ℚ) / 7, (-164610464025682781965870701509468259442 : ℚ) / 7, (66279758795181257603396681081266115310 : ℚ) / 7, (-381764538796762749650397290415207520 : ℚ) / 1, (-820412191888987152187226936958204725 : ℚ) / 7, (30949584675424167845807431305617964 : ℚ) / 7, (4563079791889460643933146923264187 : ℚ) / 7]

def block27Margin0 : ℚ := (512393842484811367838275276611115008254158640603640041378924636876278369353383410834591813467 : ℚ) / 481036337152000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_0 : ∀ i : Fin 37, block27Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block27PowerCoefficients
      block27Margin0 (by norm_num) block27_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin1 : ℚ := (660811187000197524314043816647988252550200091140195300415318507361208303397318761 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_1 : ∀ i : Fin 37, block27Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block27PowerCoefficients
      block27Margin1 (by norm_num) block27_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin2 : ℚ := (32025909560156547399149738693410451409693949546273892450002234759579691461720662054637162941 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_2 : ∀ i : Fin 37, block27Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block27PowerCoefficients
      block27Margin2 (by norm_num) block27_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin3 : ℚ := (39625236921911804211002071677917376626196943749832751061362707115280882 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_3 : ∀ i : Fin 37, block27Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block27PowerCoefficients
      block27Margin3 (by norm_num) block27_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin4 : ℚ := (181531056160866420511680067640573818121032960038068034216955907221631207789 : ℚ) / 481681964882271928320000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_4 : ∀ i : Fin 37, block27Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block27PowerCoefficients
      block27Margin4 (by norm_num) block27_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin5 : ℚ := (12541962853819602003219141744140036742650926904652419077270547536923 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_5 : ∀ i : Fin 37, block27Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block27PowerCoefficients
      block27Margin5 (by norm_num) block27_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin6 : ℚ := (413080529958340975187006168080076191277660246140391297224990684958417196551181801 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_6 : ∀ i : Fin 37, block27Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block27PowerCoefficients
      block27Margin6 (by norm_num) block27_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin7 : ℚ := (33173039048262138976593453874145860025265891020844850799468639630721563580393008893792682061 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_7 : ∀ i : Fin 37, block27Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block27PowerCoefficients
      block27Margin7 (by norm_num) block27_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block27Margin8 : ℚ := (60458340999379157488796231014093831716153484283998991307852133330747392 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block27_coefficient_bound_8 : ∀ i : Fin 37, block27Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block27PowerCoefficients) i := by
  decide +kernel

theorem block27_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block27Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block27PowerCoefficients
      block27Margin8 (by norm_num) block27_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block27_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block27PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block27_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block27_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block27_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block27_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block27_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block27_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block27_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block27_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block27_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
