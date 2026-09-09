import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (1,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block08PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-142700286498420123906286422492512000000000000000 : ℚ) / 7, (2485035054221663615303722354821282680000000000000 : ℚ) / 21, (-1185697666929804765734603541337193380000000000000 : ℚ) / 3, (17470178741493523580360909755329376996000000000000 : ℚ) / 21, (-1008216839484984071913829705776377172000000000000 : ℚ) / 1, (2257932873103963050459043817752456972000000000000 : ℚ) / 7, (24740235136743701098035182021307143203000000000000 : ℚ) / 21, (-45933650386988874413831596918057802309900000000000 : ℚ) / 21, (31959980643534770863102451123300039914550000000000 : ℚ) / 21, (249344401283889284650582304448851253490000000000 : ℚ) / 1, (-8098967696747927396132746257588242628540000000000 : ℚ) / 7, (1916512010771633609319621925005635392726600000000 : ℚ) / 3, (1200627784900423181050116590648441618770200000000 : ℚ) / 7, (-5466332307010838489754806949057506978665010000000 : ℚ) / 21, (267912767611970992109206764707869247108115000000 : ℚ) / 7, (664900691740009636764544903132026625678495000000 : ℚ) / 21, (-296026704215084568008833157537957026615540000000 : ℚ) / 21, (8196639848131033480831744311626905169119000000 : ℚ) / 7, (1205293315564566271063639285303515942781000000 : ℚ) / 1, (-4620317845537608934608395806734457565137900000 : ℚ) / 7, (1122148731829206430744777074144570609217250000 : ℚ) / 21, (1636279510913119849033921818063858200599252000 : ℚ) / 21, (-59848409013184612083217942847311756743508000 : ℚ) / 7, (-20095645664185893989991060311193477687191200 : ℚ) / 7, (11200647282892483866784560438551249927844200 : ℚ) / 21, (548155344860203918894528207329866997218000 : ℚ) / 21, (-312117204746568797142476347849800301297250 : ℚ) / 21, (12981883645006814609289904623501649059750 : ℚ) / 7, (6958033988236657509224301200040342001150 : ℚ) / 21, (-897973089863346748001315865161165241050 : ℚ) / 21, (-20249288280686571681938644313585343500 : ℚ) / 21, (17633218725689856396227471878958020250 : ℚ) / 21, (-74421674928306653402553785730686250 : ℚ) / 7, (-31484387978065276654737214120820950 : ℚ) / 3, (-9919738678020566617245971572313450 : ℚ) / 21, (0 : ℚ) / 1]

def block08Margin0 : ℚ := (513837673536535445087777979993880259575639700422790621635701697455154593993254282174208357 : ℚ) / 481036337152000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_0 : ∀ i : Fin 37, block08Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block08PowerCoefficients
      block08Margin0 (by norm_num) block08_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin1 : ℚ := (9229137311707055393094438316751487351105785460465700179121780489810826465963967 : ℚ) / 14000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_1 : ∀ i : Fin 37, block08Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block08PowerCoefficients
      block08Margin1 (by norm_num) block08_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin2 : ℚ := (31384013940729410993584375477269626802858315587393140298854624401178556788110476630718537 : ℚ) / 68719476736000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_2 : ∀ i : Fin 37, block08Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block08PowerCoefficients
      block08Margin2 (by norm_num) block08_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin3 : ℚ := (301419013181653474905718797588364612490670048809977342445158015583544 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_3 : ∀ i : Fin 37, block08Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block08PowerCoefficients
      block08Margin3 (by norm_num) block08_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin4 : ℚ := (5756382312793679629177562085165971080423524784168827684812326625445 : ℚ) / 16528282690043758247936

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_4 : ∀ i : Fin 37, block08Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block08PowerCoefficients
      block08Margin4 (by norm_num) block08_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin5 : ℚ := (205603219287623847857566907760409048099030818626350683387044606475 : ℚ) / 590295810358705651712

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_5 : ∀ i : Fin 37, block08Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block08PowerCoefficients
      block08Margin5 (by norm_num) block08_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin6 : ℚ := (5135918108624226402366098475721769968418578048495721185319406262352541893286849 : ℚ) / 14000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_6 : ∀ i : Fin 37, block08Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block08PowerCoefficients
      block08Margin6 (by norm_num) block08_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin7 : ℚ := (28617317223207175969331046328658787442384752710390234074925774441033854900994193746544333 : ℚ) / 68719476736000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_7 : ∀ i : Fin 37, block08Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block08PowerCoefficients
      block08Margin7 (by norm_num) block08_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block08Margin8 : ℚ := (406759646624390620057389071164062907041269427406034037050560807698432 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block08_coefficient_bound_8 : ∀ i : Fin 37, block08Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block08PowerCoefficients) i := by
  decide +kernel

theorem block08_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block08Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block08PowerCoefficients
      block08Margin8 (by norm_num) block08_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block08_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block08PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block08_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block08_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block08_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block08_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block08_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block08_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block08_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block08_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block08_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
