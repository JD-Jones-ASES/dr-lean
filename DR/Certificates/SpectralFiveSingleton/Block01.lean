import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (0,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block01PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-19457944394435296882499419671968000000000000000 : ℚ) / 1, (331687311972945527249005519829168000000000000000 : ℚ) / 3, (-363994638364836734080915609102289600000000000000 : ℚ) / 1, (2275421281535383628904326942297113600000000000000 : ℚ) / 3, (-2743995928523704381195505814942894800000000000000 : ℚ) / 3, (941854657357429777224170152020523600000000000000 : ℚ) / 3, (2901555214549356886786694503118114720000000000000 : ℚ) / 3, (-5305509008443700016390754175276405440000000000000 : ℚ) / 3, (3401765851046284951680176302740236188000000000000 : ℚ) / 3, (1027600737365220792777929635537713980000000000000 : ℚ) / 3, (-2923649134185100279249197983261869312360000000000 : ℚ) / 3, (1327744786454095777136448100777542050120000000000 : ℚ) / 3, (623761887433194228064626672759515623828000000000 : ℚ) / 3, (-617734756711838245289473542301722072566000000000 : ℚ) / 3, (22900555898461986891895222710296227114000000000 : ℚ) / 3, (28435320691470319532327507048553741734000000000 : ℚ) / 1, (-30720674052756701769347345111625789097100000000 : ℚ) / 3, (-2260028618006522945713455209194221081800000000 : ℚ) / 3, (2907533391243540700715472756691760611610000000 : ℚ) / 3, (-1281515835489147403554054248337472917685000000 : ℚ) / 3, (5140285064621547593101965750631132144800000 : ℚ) / 1, (201583035462861491768865322349034722795200000 : ℚ) / 3, (-2433465901705988432750898848339616470920000 : ℚ) / 3, (-2392011161196757530053959990550215548920000 : ℚ) / 1, (343095034243704954206891194772250398825000 : ℚ) / 1, (73655806571873201234264450310911280037500 : ℚ) / 1, (-19005785808143748108437733877477129212500 : ℚ) / 3, (2965422934552831273818006114534276342500 : ℚ) / 3, (460312875325545031906448977671134917500 : ℚ) / 1, (43804183659718806286265389678819300000 : ℚ) / 3, (544716832297627951981525696625162500 : ℚ) / 1, (2689594448934806610812508722796968750 : ℚ) / 3, (321594552605014588819978095397307500 : ℚ) / 3, (10782324650022355018745621274253750 : ℚ) / 3, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block01Margin0 : ℚ := (150993556470594221095024607308235269234227578636372573439377718665700719829865564775441 : ℚ) / 137438953472000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_0 : ∀ i : Fin 37, block01Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block01PowerCoefficients
      block01Margin0 (by norm_num) block01_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin1 : ℚ := (5592664904410940110068581890491776977554207690523278738565468327596764315121 : ℚ) / 8000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_1 : ∀ i : Fin 37, block01Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block01PowerCoefficients
      block01Margin1 (by norm_num) block01_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin2 : ℚ := (68166194088047225479548457885553823807288880891098121858688313354728622779551866792489 : ℚ) / 137438953472000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_2 : ∀ i : Fin 37, block01Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block01PowerCoefficients
      block01Margin2 (by norm_num) block01_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin3 : ℚ := (376731819283475486199721061040469724497751142406711654664057981172 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_3 : ∀ i : Fin 37, block01Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block01PowerCoefficients
      block01Margin3 (by norm_num) block01_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin4 : ℚ := (55651208902678752749527897092470569657317706507515404710200230625 : ℚ) / 147573952589676412928

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_4 : ∀ i : Fin 37, block01Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block01PowerCoefficients
      block01Margin4 (by norm_num) block01_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin5 : ℚ := (90970643838882055375864660166135815301507758876492867103823322595259 : ℚ) / 241467879924858030653440

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_5 : ∀ i : Fin 37, block01Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block01PowerCoefficients
      block01Margin5 (by norm_num) block01_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin6 : ℚ := (3118168323653982342833734866532688756887067548622708757678905359314519720129 : ℚ) / 8000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_6 : ∀ i : Fin 37, block01Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block01PowerCoefficients
      block01Margin6 (by norm_num) block01_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin7 : ℚ := (59591436819145838956820276655378792652548092265147324004290166358467010116854256596529 : ℚ) / 137438953472000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_7 : ∀ i : Fin 37, block01Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block01PowerCoefficients
      block01Margin7 (by norm_num) block01_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block01Margin8 : ℚ := (475177790968028611077582088865933424532287333223686062890662494208 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block01_coefficient_bound_8 : ∀ i : Fin 37, block01Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block01PowerCoefficients) i := by
  decide +kernel

theorem block01_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block01Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block01PowerCoefficients
      block01Margin8 (by norm_num) block01_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block01_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block01PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block01_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block01_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block01_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block01_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block01_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block01_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block01_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block01_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block01_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
