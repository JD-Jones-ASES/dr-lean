import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (1,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block09PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-140381466128766703503746780883712000000000000000 : ℚ) / 7, (349845272655578331858412740219779240000000000000 : ℚ) / 3, (-2736836254118226781699329686989020715000000000000 : ℚ) / 7, (17500297737878821178390717833370591408500000000000 : ℚ) / 21, (-7353964435224058670159687039860167068000000000000 : ℚ) / 7, (10016038553646244672457719866170568518500000000000 : ℚ) / 21, (6008310245981628224199227759308705951375000000000 : ℚ) / 7, (-1757424488914163938951797861506847369400000000000 : ℚ) / 1, (24680870000233574387606450224454325548412500000000 : ℚ) / 21, (7217172665059973103680607148500118603321250000000 : ℚ) / 21, (-7169547208758293961468840050782102116900000000000 : ℚ) / 7, (3371138242369073480577602462603605915774150000000 : ℚ) / 7, (4663965082828674894910239895695283538831950000000 : ℚ) / 21, (-4809964917958806262170386768944816631781010000000 : ℚ) / 21, (286035537434896116818013695521240111377552500000 : ℚ) / 21, (740069168257531013106718792477074255602001250000 : ℚ) / 21, (-76400707122736179043933533503059581721078750000 : ℚ) / 7, (-3267441625437481302197105195752483660393000000 : ℚ) / 21, (30104407000269344872740340336514059091587000000 : ℚ) / 21, (-10678516985022187792931374480697868740874950000 : ℚ) / 21, (77044739144935595633637294573699757588400000 : ℚ) / 21, (1766810009187973080399220514605448874314552000 : ℚ) / 21, (-28066144108626833789179140668959617561176000 : ℚ) / 7, (-28310182614403467476897755701881478080011200 : ℚ) / 7, (8920970486738072846071504464299360312376400 : ℚ) / 21, (1659042469476026504062028341913166137494000 : ℚ) / 21, (-389709854953085335657464519261086846500000 : ℚ) / 21, (6199260438655098348760169644915904541500 : ℚ) / 7, (4082871114201726934174013726715687017300 : ℚ) / 7, (-805468312472891293965683538191132443100 : ℚ) / 21, (-113751766397912332424662912688391065500 : ℚ) / 21, (24367897391474029216419523770003494500 : ℚ) / 21, (297835529022582344300917354059193500 : ℚ) / 7, (-321744567556667073759369338823731900 : ℚ) / 21, (-19839477356041133234491943144626900 : ℚ) / 21, (0 : ℚ) / 1]

def block09Margin0 : ℚ := (259995815843997149426173275594040232204577905883570520097949461088304414450814234908563117 : ℚ) / 240518168576000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_0 : ∀ i : Fin 37, block09Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block09PowerCoefficients
      block09Margin0 (by norm_num) block09_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin1 : ℚ := (679253236270943068914631707597215803204642791072438348668407129625828110383621 : ℚ) / 1000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_1 : ∀ i : Fin 37, block09Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block09PowerCoefficients
      block09Margin1 (by norm_num) block09_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin2 : ℚ := (16522644524703989145494169334503517440684136073857580686080000475398091847588100247283457 : ℚ) / 34359738368000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_2 : ∀ i : Fin 37, block09Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block09PowerCoefficients
      block09Margin2 (by norm_num) block09_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin3 : ℚ := (323396141726662571202085373148955327288581277189989938862583754248848 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_3 : ∀ i : Fin 37, block09Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block09PowerCoefficients
      block09Margin3 (by norm_num) block09_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin4 : ℚ := (997389108018759366598969381081984887176377310854830987791963607683709 : ℚ) / 2641054936678134710272000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_4 : ∀ i : Fin 37, block09Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block09PowerCoefficients
      block09Margin4 (by norm_num) block09_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin5 : ℚ := (780748511036220866854970827809616643435233682341995917465985523125 : ℚ) / 2066035336255469780992

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_5 : ∀ i : Fin 37, block09Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block09PowerCoefficients
      block09Margin5 (by norm_num) block09_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin6 : ℚ := (2798413182153179192635447134695776497066525630057573051584692993805996398656069 : ℚ) / 7000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_6 : ∀ i : Fin 37, block09Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block09PowerCoefficients
      block09Margin6 (by norm_num) block09_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin7 : ℚ := (15607524057170229536961625603337963742325349591634341673770983824472897473901726251427653 : ℚ) / 34359738368000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_7 : ∀ i : Fin 37, block09Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block09PowerCoefficients
      block09Margin7 (by norm_num) block09_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block09Margin8 : ℚ := (443687530559658356091600067940873446398010095529290716526583551688704 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block09_coefficient_bound_8 : ∀ i : Fin 37, block09Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block09PowerCoefficients) i := by
  decide +kernel

theorem block09_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block09Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block09PowerCoefficients
      block09Margin8 (by norm_num) block09_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block09_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block09PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block09_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block09_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block09_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block09_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block09_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block09_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block09_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block09_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block09_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
