import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (2,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block16PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-146876141866139749232537265672448000000000000000 : ℚ) / 7, (2598695076085311621106560834556336640000000000000 : ℚ) / 21, (-1254423323629375805656379888103470293400000000000 : ℚ) / 3, (56249236262178469798959253976887783853693750000000 : ℚ) / 63, (-23427637872293813523697988930594795806750625000000 : ℚ) / 21, (3148991958623121278433914451870552185989375000000 : ℚ) / 7, (22812999423257623975918030595576771147680625000000 : ℚ) / 21, (-135661484856039996161837879350964623616023750000000 : ℚ) / 63, (95065203387076095716181070466161792046205125000000 : ℚ) / 63, (18510168210344959170377700300917831655636687500000 : ℚ) / 63, (-10926375904715265269448272383679058396935131250000 : ℚ) / 9, (41499726733345976831976302616427371174103287500000 : ℚ) / 63, (1390962703479851830054307378364910413203704750000 : ℚ) / 7, (-18007188880985762718261792440838661486264703500000 : ℚ) / 63, (852638698132171907487662593801229349424040350000 : ℚ) / 21, (2435792709879018485153889246966362202152957300000 : ℚ) / 63, (-1003767384110178649476153436668532111048229975000 : ℚ) / 63, (82370214274591508153161677441225573173928775000 : ℚ) / 63, (15772738660095218771614069351866979499330020000 : ℚ) / 9, (-16067801533385966004394545776309892285684620000 : ℚ) / 21, (2146047280214513515780406423844724551603751000 : ℚ) / 63, (6151117931710168511456889780460270381309889000 : ℚ) / 63, (-712877086721674539345159737709242214414453460 : ℚ) / 63, (-31834548025049212927078089865221831120534040 : ℚ) / 7, (2073176166834742117677827805414126073798568 : ℚ) / 3, (1870116816487007416792199447047728009927928 : ℚ) / 63, (-1857867622593851184942525475045653316773620 : ℚ) / 63, (49441442811245108563516428074028033494500 : ℚ) / 21, (30517477220882406918808420857166966440065 : ℚ) / 63, (-2347994652988591441989807345082347538579 : ℚ) / 21, (-293434016512273988410857119596071494587 : ℚ) / 63, (13682766943151497767801724957791359795 : ℚ) / 9, (-747783435881498351908159182505732540 : ℚ) / 7, (-1761611608516808093873001036601144715 : ℚ) / 63, (-10316528225141389281935810435205988 : ℚ) / 63, (4563079791889460643933146923264187 : ℚ) / 63]

def block16Margin0 : ℚ := (216338106128164715195645638487713202821602148836639803372366252475380844123149001741968684687 : ℚ) / 206158430208000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_0 : ∀ i : Fin 37, block16Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block16PowerCoefficients
      block16Margin0 (by norm_num) block16_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin1 : ℚ := (4451454400002826513137539842871569670119771757996907788591786161447830630167091423 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_1 : ∀ i : Fin 37, block16Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block16PowerCoefficients
      block16Margin1 (by norm_num) block16_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin2 : ℚ := (29939072905102922769901887281602449165950084022321158564895874605480772023065760769745191989 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_2 : ∀ i : Fin 37, block16Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block16PowerCoefficients
      block16Margin2 (by norm_num) block16_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin3 : ℚ := (36057773446215347901597775894414389317413305365001371470672528877016958 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_3 : ∀ i : Fin 37, block16Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block16PowerCoefficients
      block16Margin3 (by norm_num) block16_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin4 : ℚ := (11112211798591462885883558938448821164354616908337832930325341399673061823 : ℚ) / 32895282470232124293120000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_4 : ∀ i : Fin 37, block16Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block16PowerCoefficients
      block16Margin4 (by norm_num) block16_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin5 : ℚ := (11193528478886438615645481482851462903218576295122294819085270047075 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_5 : ∀ i : Fin 37, block16Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block16PowerCoefficients
      block16Margin5 (by norm_num) block16_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin6 : ℚ := (2547626859122602442781148555804389794572676165217558154351340597103648812270445663 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_6 : ∀ i : Fin 37, block16Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block16PowerCoefficients
      block16Margin6 (by norm_num) block16_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin7 : ℚ := (86824728013201947545729533513262687723844009887890776174652011441507864017293685355993948367 : ℚ) / 206158430208000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_7 : ∀ i : Fin 37, block16Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block16PowerCoefficients
      block16Margin7 (by norm_num) block16_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block16Margin8 : ℚ := (7468289988591688557748623691931749560795308617042035186856628344295424 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block16_coefficient_bound_8 : ∀ i : Fin 37, block16Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block16PowerCoefficients) i := by
  decide +kernel

theorem block16_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block16Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block16PowerCoefficients
      block16Margin8 (by norm_num) block16_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block16_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block16PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block16_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block16_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block16_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block16_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block16_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block16_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block16_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block16_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block16_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
