import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (7,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block50PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-25952620131808342611289904460704000000000000000 : ℚ) / 1, (489194835008991634889454395729527520000000000000 : ℚ) / 3, (-1729115266024123499139740029464601333900000000000 : ℚ) / 3, (1268094710404876211431415833664763130896875000000 : ℚ) / 1, (-4828775886287904380953988633098690019757734375000 : ℚ) / 3, (515457664761797826732492934909399290097734375000 : ℚ) / 1, (2205188939620170152746317919751398823204648437500 : ℚ) / 1, (-4533325264363968882287930461988446461484492187500 : ℚ) / 1, (23567161664105155251536269416675178067595455078125 : ℚ) / 6, (-1216324655060279376036495705078604299420091796875 : ℚ) / 2, (-12301625050324702472926642064070656382212355078125 : ℚ) / 6, (11227726943103310228069055197198062922200069921875 : ℚ) / 6, (-1441955735748118197375779127880491472815425046875 : ℚ) / 6, (-1588256294825262436486470370865632130737020734375 : ℚ) / 3, (539168068861526960341285292025848552164782028125 : ℚ) / 2, (3336424660987600516540450822169684514397690625 : ℚ) / 1, (-153581331856166992541301795488289153978822678125 : ℚ) / 3, (108476944974025628198623328943976142649498134375 : ℚ) / 6, (7134827481523704631640346410290977094297765000 : ℚ) / 3, (-16332606408623939246621461053748591127020769375 : ℚ) / 6, (392225560889019883055532019409712946324279500 : ℚ) / 1, (425401765378572363313101337688504935602074750 : ℚ) / 3, (-160987288184941069805148707368115741474294335 : ℚ) / 3, (1425950846744293284883750958367754759236990 : ℚ) / 1, (7574926847587196524120899814711453235151278 : ℚ) / 3, (-347068599415251256228663302125027562770472 : ℚ) / 1, (-56237777569225868168148155219050121603140 : ℚ) / 3, (54042085259778666542907783804852241964555 : ℚ) / 3, (-847438071124446259165266355718809202685 : ℚ) / 2, (-250957813984002217947799634536512794443 : ℚ) / 2, (429379460692958175744313191003123951133 : ℚ) / 6, (34391866584955128429922024780063753885 : ℚ) / 6, (-89856375707787384580444734260294365 : ℚ) / 1, (699037303545767119325960919746914625 : ℚ) / 6, (58129668653200520377061393413756817 : ℚ) / 3, (4563079791889460643933146923264187 : ℚ) / 6]

def block50Margin0 : ℚ := (121162063578004183978898104889099718548872542924126009843983700735000746787177667754967022289 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_0 : ∀ i : Fin 37, block50Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block50PowerCoefficients
      block50Margin0 (by norm_num) block50_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin1 : ℚ := (813153350713415629965826206711158529588537729404057055488729829497199969298941009 : ℚ) / 2000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_1 : ∀ i : Fin 37, block50Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block50PowerCoefficients
      block50Margin1 (by norm_num) block50_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin2 : ℚ := (26846548438746663086954111230039376485900529241438580452958560741984542931777609505891458129 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_2 : ∀ i : Fin 37, block50Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block50PowerCoefficients
      block50Margin2 (by norm_num) block50_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin3 : ℚ := (1784928840138269518064455359440566834092380891165104927006911678659247 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_3 : ∀ i : Fin 37, block50Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block50PowerCoefficients
      block50Margin3 (by norm_num) block50_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin4 : ℚ := (329276920063664989843429887476812306486656881921359095540465840675168805166149 : ℚ) / 2854790721699840000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_4 : ∀ i : Fin 37, block50Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block50PowerCoefficients
      block50Margin4 (by norm_num) block50_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin5 : ℚ := (1139623097517335407750565745460270565676084214309256877519377884401 : ℚ) / 9444732965739290427392

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_5 : ∀ i : Fin 37, block50Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block50PowerCoefficients
      block50Margin5 (by norm_num) block50_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin6 : ℚ := (312137699330028552028920900976011882920524550489291954921906061666947314793858169 : ℚ) / 2000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_6 : ∀ i : Fin 37, block50Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block50PowerCoefficients
      block50Margin6 (by norm_num) block50_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin7 : ℚ := (29698721429854962370615971641634456622930713862456925744647033945121140763672114642320190209 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_7 : ∀ i : Fin 37, block50Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block50PowerCoefficients
      block50Margin7 (by norm_num) block50_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block50Margin8 : ℚ := (4374118922575241818636679693098066609637598657433615347076040160940032 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block50_coefficient_bound_8 : ∀ i : Fin 37, block50Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block50PowerCoefficients) i := by
  decide +kernel

theorem block50_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block50Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block50PowerCoefficients
      block50Margin8 (by norm_num) block50_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block50_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block50PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block50_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block50_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block50_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block50_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block50_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block50_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block50_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block50_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block50_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
