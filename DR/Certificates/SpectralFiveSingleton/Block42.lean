import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (6,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block42PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-177492485554938772952778488044992000000000000000 : ℚ) / 7, (1123964306540508442392581319957692760000000000000 : ℚ) / 7, (-4016193318576801916764523686016777944000000000000 : ℚ) / 7, (8981471895706941408281343978507453609734375000000 : ℚ) / 7, (-11749526785885376501271948863647887134534375000000 : ℚ) / 7, (4612388742295809527274908309759054848371093750000 : ℚ) / 7, (14358168090633758290451768108816335139082812500000 : ℚ) / 7, (-31546380218155485048717733074857761697096875000000 : ℚ) / 7, (28773195607006029609527877757272448802826250000000 : ℚ) / 7, (-6189605624542032198664296930057864132965703125000 : ℚ) / 7, (-13206794723561256502064045895287292007126453125000 : ℚ) / 7, (13323377889071745291887362131087086955927735937500 : ℚ) / 7, (-2390748405023430515165951299861792038005667031250 : ℚ) / 7, (-3341045678242974746238889734387127981234084062500 : ℚ) / 7, (1959138410540451943330071963020808033323486906250 : ℚ) / 7, (-65775232023397797142102646604989939487305937500 : ℚ) / 7, (-316159951836876299841246623252394427707171468750 : ℚ) / 7, (125757705894394822908234034737673369612760562500 : ℚ) / 7, (3453758822834899731523917653981539496942993750 : ℚ) / 7, (-16869262744519587097749107669854868274042400000 : ℚ) / 7, (3987826596069510289044972066998578636386160000 : ℚ) / 7, (688669926104716812144784901140941353789264000 : ℚ) / 7, (-394441484748459324743064654009524550447734100 : ℚ) / 7, (25354264789116668697281468688538393189583800 : ℚ) / 7, (12938499255308971299130963165375650173839880 : ℚ) / 7, (-2810887817844215178948877631276601384247600 : ℚ) / 7, (49150087651331829132515944255125619740900 : ℚ) / 7, (89659446653556727545833288749316888010600 : ℚ) / 7, (-9798333297493916093234086307771712277400 : ℚ) / 7, (-290029951836847126979915606237431040320 : ℚ) / 7, (354373629903244090036903426092233837200 : ℚ) / 7, (-268993469707286200770603233127557900 : ℚ) / 1, (-1272914961330396209093892800212628050 : ℚ) / 7, (575344843325192863800266351194180100 : ℚ) / 7, (45630797918894606439331469232641870 : ℚ) / 7, (0 : ℚ) / 1]

def block42Margin0 : ℚ := (2178021745198132585674912264759743453083545169783565591049512445768285737356813620415062387 : ℚ) / 2405181685760000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_0 : ∀ i : Fin 37, block42Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block42PowerCoefficients
      block42Margin0 (by norm_num) block42_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin1 : ℚ := (4448120778848215065755203762583889264573540104304087049408163287783363142090541 : ℚ) / 10000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_1 : ∀ i : Fin 37, block42Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block42PowerCoefficients
      block42Margin1 (by norm_num) block42_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin2 : ℚ := (82877097494353702592019093437395779328420892982216340318987598817408122879411066195557287 : ℚ) / 343597383680000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_2 : ∀ i : Fin 37, block42Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block42PowerCoefficients
      block42Margin2 (by norm_num) block42_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin3 : ℚ := (702103211063766049433647472372468978283866954153717024203698158135724 : ℚ) / 4074536263942718505859375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_3 : ∀ i : Fin 37, block42Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block42PowerCoefficients
      block42Margin3 (by norm_num) block42_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin4 : ℚ := (32761354825124321678278060966242766670462278835784542499418482970008618415477 : ℚ) / 197205938012160000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_4 : ∀ i : Fin 37, block42Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block42PowerCoefficients
      block42Margin4 (by norm_num) block42_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin5 : ℚ := (712455981164777027968907105730612689515901945302379720565600447135 : ℚ) / 4132070672510939561984

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_5 : ∀ i : Fin 37, block42Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block42PowerCoefficients
      block42Margin5 (by norm_num) block42_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin6 : ℚ := (14692354501822473036861828410818947668990646141776369432393013120482563375338609 : ℚ) / 70000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_6 : ∀ i : Fin 37, block42Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block42PowerCoefficients
      block42Margin6 (by norm_num) block42_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin7 : ℚ := (93901962115864535936311019581768489186814148978654191843495613017023603443817556359274163 : ℚ) / 343597383680000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_7 : ∀ i : Fin 37, block42Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block42PowerCoefficients
      block42Margin7 (by norm_num) block42_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block42Margin8 : ℚ := (1482756907404115187269280704092017119072841783908250975249970473644032 : ℚ) / 4074536263942718505859375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block42_coefficient_bound_8 : ∀ i : Fin 37, block42Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block42PowerCoefficients) i := by
  decide +kernel

theorem block42_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block42Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block42PowerCoefficients
      block42Margin8 (by norm_num) block42_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block42_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block42PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block42_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block42_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block42_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block42_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block42_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block42_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block42_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block42_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block42_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
