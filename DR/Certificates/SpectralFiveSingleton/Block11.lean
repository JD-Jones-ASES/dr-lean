import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (1,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block11PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-135743825389459862698667497666112000000000000000 : ℚ) / 7, (2393183124238135070206048247369673680000000000000 : ℚ) / 21, (-8160472358834383045994156036737010365000000000000 : ℚ) / 21, (6040278569582122822428487819699107066765625000000 : ℚ) / 7, (-8474984565841269571192283883524817258402343750000 : ℚ) / 7, (19687385403006945335751190828954084801380859375000 : ℚ) / 21, (14629914298561457256876684538580242310546875000 : ℚ) / 7, (-14377017899019366696278840863032833194148046875000 : ℚ) / 21, (7665511525267744284451772692373355551733203125000 : ℚ) / 21, (11036104620716540195780023273317953467241171875000 : ℚ) / 21, (-4803047573260714202760773930151925442643437500000 : ℚ) / 7, (115994169961800382988802274461179977826731250000 : ℚ) / 1, (2312327394115287336604139876765354307951706250000 : ℚ) / 7, (-1085315579242140773394985128539826518539623125000 : ℚ) / 7, (-279655062795636694944786979232247326557036875000 : ℚ) / 7, (898725343134376388618600597424892561341591875000 : ℚ) / 21, (-107181451623652398933397718081678748862144375000 : ℚ) / 21, (-62569545325142377573875242570089810155424250000 : ℚ) / 21, (48844299807371979731433216552280307390537125000 : ℚ) / 21, (-3212004001458485822092445906139536113547450000 : ℚ) / 21, (-867116222517924499867756974372948389254350000 : ℚ) / 7, (2141182113710391553787290065023193917445152000 : ℚ) / 21, (124653331992851046666155315513178908041714000 : ℚ) / 21, (-148359057685669854614344518915328937102953600 : ℚ) / 21, (5112373441023306577517338980765480023190800 : ℚ) / 21, (4278098499066553536778996815486601864046000 : ℚ) / 21, (-647961378781580240638154029780521776468000 : ℚ) / 21, (-26873956215621180895629285431481716360000 : ℚ) / 21, (8424630293736706056098274060747523092800 : ℚ) / 7, (-779658145433803399448786273864355972200 : ℚ) / 21, (-339545245352439572839415073307676072000 : ℚ) / 21, (40888957589878984821343777599932318000 : ℚ) / 21, (166591479005632235273061190066404000 : ℚ) / 1, (-524452270977087348111787018779702400 : ℚ) / 21, (-39678954712082266468983886289253800 : ℚ) / 21, (0 : ℚ) / 1]

def block11Margin0 : ℚ := (133236493770454026738102680861494585113248000229277194154898392756077635393228134482490497 : ℚ) / 120259084288000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_0 : ∀ i : Fin 37, block11Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block11PowerCoefficients
      block11Margin0 (by norm_num) block11_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin1 : ℚ := (2530802316411450641566550515188927081367297421597051335055173977970142530233537 : ℚ) / 3500000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_1 : ∀ i : Fin 37, block11Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block11PowerCoefficients
      block11Margin1 (by norm_num) block11_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin2 : ℚ := (9198159659141368043703859513006539465676229957141583196311539732582982205298599651315917 : ℚ) / 17179869184000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_2 : ∀ i : Fin 37, block11Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block11PowerCoefficients
      block11Margin2 (by norm_num) block11_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin3 : ℚ := (374171995979566771271796561343139099618916898467817907035914270579456 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_3 : ∀ i : Fin 37, block11Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block11PowerCoefficients
      block11Margin3 (by norm_num) block11_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin4 : ℚ := (3559945328688113842274024666360688793008056648443353645188331215727260783 : ℚ) / 7985182965709248921600000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_4 : ∀ i : Fin 37, block11Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block11PowerCoefficients
      block11Margin4 (by norm_num) block11_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin5 : ℚ := (462384912886774128699860104926466534119435972958914050707652912025 : ℚ) / 1033017668127734890496

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_5 : ∀ i : Fin 37, block11Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block11PowerCoefficients
      block11Margin5 (by norm_num) block11_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin6 : ℚ := (1675135550859322575257985131657226662056466131254725119088370961531092977653179 : ℚ) / 3500000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_6 : ∀ i : Fin 37, block11Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block11PowerCoefficients
      block11Margin6 (by norm_num) block11_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin7 : ℚ := (9381753654814217635339193076695988765754829998693627272834509944982206432199608420619313 : ℚ) / 17179869184000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_7 : ∀ i : Fin 37, block11Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block11PowerCoefficients
      block11Margin7 (by norm_num) block11_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block11Margin8 : ℚ := (534631313326970655186681637691679481157432491222495560916155967669248 : ℚ) / 814907252788543701171875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block11_coefficient_bound_8 : ∀ i : Fin 37, block11Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block11PowerCoefficients) i := by
  decide +kernel

theorem block11_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block11Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block11PowerCoefficients
      block11Margin8 (by norm_num) block11_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block11_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block11PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block11_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block11_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block11_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block11_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block11_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block11_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block11_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block11_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block11_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
