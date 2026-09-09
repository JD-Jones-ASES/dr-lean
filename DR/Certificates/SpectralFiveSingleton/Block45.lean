import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (6,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block45PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-170536024445978511745159563218592000000000000000 : ℚ) / 7, (1030144891958983045983079231873319760000000000000 : ℚ) / 7, (-3513022465325560002378562449014782097750000000000 : ℚ) / 7, (7457783878911051004216779695099339319046875000000 : ℚ) / 7, (-9076285834927055057497686241206483887862500000000 : ℚ) / 7, (2709414147148889802554711102787790084757031250000 : ℚ) / 7, (11306825915327202131643617368805518140604296875000 : ℚ) / 7, (-2978024415114646392742442070038443366451171875000 : ℚ) / 1, (2014629332912741491888753341056033877420449218750 : ℚ) / 1, (526605454104501782500513130600781814230488281250 : ℚ) / 1, (-13240700845008696997064741950173449827911824218750 : ℚ) / 7, (7501771892068409202667581978095654629033817968750 : ℚ) / 7, (1801285142470078345639929003835468982343698593750 : ℚ) / 7, (-510308750230115440992673101400473212030479609375 : ℚ) / 1, (764554729625841790837003968000512111196186593750 : ℚ) / 7, (59655464297096297872527077224783039727047484375 : ℚ) / 1, (-305770762518099603597182513927000334697796781250 : ℚ) / 7, (6026886325760446201497376454431865773307187500 : ℚ) / 1, (38465738948755400797003275787546390698597978125 : ℚ) / 7, (-14607328257811171185797260403700923331010753125 : ℚ) / 7, (-562380963001961194697180946502711077650221250 : ℚ) / 7, (1543659999601410950259660510811604696547132125 : ℚ) / 7, (-211520674757223943374643729146742520755574350 : ℚ) / 7, (-107561089547645114817452790305714330782027575 : ℚ) / 14, (20831226680780886010536205972824213583395205 : ℚ) / 7, (-599210813822541533768268054985774759234505 : ℚ) / 7, (-681302474445743094907762228068788349464750 : ℚ) / 7, (262543985198696883702833654414589250457275 : ℚ) / 14, (10023641434830880594387841318761774931500 : ℚ) / 7, (-3416147939489432262739512981884510084670 : ℚ) / 7, (332511381264754570597696295846640439620 : ℚ) / 7, (85505690627725862232096608633464513375 : ℚ) / 7, (-3965691502583569324746506566210310625 : ℚ) / 7, (229514248920537416485378299582533675 : ℚ) / 14, (189467008750192822389398057031186895 : ℚ) / 7, (22815398959447303219665734616320935 : ℚ) / 14]

def block45Margin0 : ℚ := (178844611008702042311144194648671919503362278535636174802814398834778610706242299516799053347 : ℚ) / 192414534860800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_0 : ∀ i : Fin 37, block45Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block45PowerCoefficients
      block45Margin0 (by norm_num) block45_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin1 : ℚ := (1298622470274154887974972143499635685339441124650103902436315453194338475844735267 : ℚ) / 2800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_1 : ∀ i : Fin 37, block45Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block45PowerCoefficients
      block45Margin1 (by norm_num) block45_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin2 : ℚ := (6778253037558443882153510208395932868738501702686644212383308280268046856433005645604254821 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_2 : ∀ i : Fin 37, block45Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block45PowerCoefficients
      block45Margin2 (by norm_num) block45_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin3 : ℚ := (3340090969018949659952213386927153002802709830541201704299783545025051 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_3 : ∀ i : Fin 37, block45Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block45PowerCoefficients
      block45Margin3 (by norm_num) block45_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin4 : ℚ := (2323999402229663547607578594225672593998489262577776261681080183763503878277 : ℚ) / 15413822876232701706240000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_4 : ∀ i : Fin 37, block45Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block45PowerCoefficients
      block45Margin4 (by norm_num) block45_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin5 : ℚ := (10093333965360875369826161161780664884484812082062485800553593801295 : ℚ) / 66113130760175032991744

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_5 : ∀ i : Fin 37, block45Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block45PowerCoefficients
      block45Margin5 (by norm_num) block45_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin6 : ℚ := (72378561143352502495970685963248890351038010100584007314352626705683555039615741 : ℚ) / 400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_6 : ∀ i : Fin 37, block45Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block45PowerCoefficients
      block45Margin6 (by norm_num) block45_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin7 : ℚ := (6490701113599962169353680913972386189716971950738651220511936769159866397406516515069852181 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_7 : ∀ i : Fin 37, block45Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block45PowerCoefficients
      block45Margin7 (by norm_num) block45_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block45Margin8 : ℚ := (6475511995937853130321438725642616716337108967070901889873985733042176 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block45_coefficient_bound_8 : ∀ i : Fin 37, block45Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block45PowerCoefficients) i := by
  decide +kernel

theorem block45_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block45Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block45PowerCoefficients
      block45Margin8 (by norm_num) block45_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block45_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block45PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block45_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block45_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block45_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block45_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block45_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block45_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block45_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block45_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block45_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
