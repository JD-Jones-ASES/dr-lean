import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (4,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block32PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-155227852601578999885038952032320000000000000000 : ℚ) / 7, (2767559756613234022641225668544718400000000000000 : ℚ) / 21, (-9389038385468756925197462311964549987800000000000 : ℚ) / 21, (20233241156367633047193843163551902390931250000000 : ℚ) / 21, (-26331762222407181186544748975866755809527187500000 : ℚ) / 21, (14686108585970051826395328643941428641128437500000 : ℚ) / 21, (13729997708696893752642629113176130955170468750000 : ℚ) / 21, (-31462962610145284481555664193025851785558671875000 : ℚ) / 21, (15764381399935991177393436952733901116435347656250 : ℚ) / 21, (2570584831836583433687116445380683654726519531250 : ℚ) / 3, (-28320424072471825463602626228962093894439122656250 : ℚ) / 21, (3112543016453929407534034306372256406091185156250 : ℚ) / 7, (9193086989789831916577914622394424062456503468750 : ℚ) / 21, (-2547421005481780383473140026545552961827193937500 : ℚ) / 7, (3654857175535917828223491442610443394279918750 : ℚ) / 7, (487786081447683841666235695449012649382260712500 : ℚ) / 7, (-180550411200178998770146737186120688326536900000 : ℚ) / 7, (-7362121908588790677589386544226241394586893750 : ℚ) / 7, (34987780435073851735182173023776170957665760000 : ℚ) / 7, (-24238433459086056447042052568173288477690671250 : ℚ) / 21, (-4264856660623366615237214650967721527849023000 : ℚ) / 21, (4130602370034330706606846819278480531896239000 : ℚ) / 21, (-301000705366891328430651902336945477108575420 : ℚ) / 21, (-230256394297899990196912888747572437869572040 : ℚ) / 21, (41875595404290191766802135933588206226522856 : ℚ) / 21, (1556847747781813532363746592060864676303832 : ℚ) / 21, (-711927884720647396565145969002413073299820 : ℚ) / 7, (206719384830283441488135354040322756091680 : ℚ) / 21, (34658741612843322424894532117015903383300 : ℚ) / 21, (-9733616376390854782015899972290014535764 : ℚ) / 21, (13375629282866289112073323040403307004 : ℚ) / 7, (172756975245066302589482329401273787220 : ℚ) / 21, (-556153088596091191120638479812281980 : ℚ) / 1, (-503664953727685181499008272534973380 : ℚ) / 7, (73802855764473015632310028498012068 : ℚ) / 7, (18252319167557842575732587693056748 : ℚ) / 21]

def block32Margin0 : ℚ := (121053777795116621040292620493710488684909366704463177853335748896615935854120383887377557069 : ℚ) / 120259084288000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_0 : ∀ i : Fin 37, block32Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block32PowerCoefficients
      block32Margin0 (by norm_num) block32_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin1 : ℚ := (143490281293281967712018736053086637744344977444910801400014477286362169993205057 : ℚ) / 250000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_1 : ∀ i : Fin 37, block32Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block32PowerCoefficients
      block32Margin1 (by norm_num) block32_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin2 : ℚ := (6312083887783539828290428389975958642883950717813149609107659590827383726548819047864290227 : ℚ) / 17179869184000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_2 : ∀ i : Fin 37, block32Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block32PowerCoefficients
      block32Margin2 (by norm_num) block32_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin3 : ℚ := (4160526823579348493459560184393370712901679754996239732593443097194608 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_3 : ∀ i : Fin 37, block32Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block32PowerCoefficients
      block32Margin3 (by norm_num) block32_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin4 : ℚ := (183404792800558400944118360896016195622201355924143855075114305956447988713 : ℚ) / 674610285034057236480000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_4 : ∀ i : Fin 37, block32Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block32PowerCoefficients
      block32Margin4 (by norm_num) block32_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin5 : ℚ := (322873872391135441274377247310819129852592017159977109685995252891 : ℚ) / 1180591620717411303424

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_5 : ∀ i : Fin 37, block32Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block32PowerCoefficients
      block32Margin5 (by norm_num) block32_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin6 : ℚ := (529219943983531551628569569947100036567088982026930088754364692357211535962277899 : ℚ) / 1750000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_6 : ∀ i : Fin 37, block32Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block32PowerCoefficients
      block32Margin6 (by norm_num) block32_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin7 : ℚ := (6231529513850087143424832672553683144158297415230094049914150986423895960842942329330277107 : ℚ) / 17179869184000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_7 : ∀ i : Fin 37, block32Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block32PowerCoefficients
      block32Margin7 (by norm_num) block32_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block32Margin8 : ℚ := (46519956856715534852785315682511643950774206688032339514941807704375296 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block32_coefficient_bound_8 : ∀ i : Fin 37, block32Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block32PowerCoefficients) i := by
  decide +kernel

theorem block32_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block32Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block32PowerCoefficients
      block32Margin8 (by norm_num) block32_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block32_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block32PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block32_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block32_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block32_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block32_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block32_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block32_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block32_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block32_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block32_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
