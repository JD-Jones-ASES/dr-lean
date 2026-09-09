import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (6,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block46PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-168217204076325091342619921609792000000000000000 : ℚ) / 7, (3007616932571635296064285882466836280000000000000 : ℚ) / 21, (-3384270624192027435038353260427356399000000000000 : ℚ) / 7, (21456619427007414739451412410231859633250000000000 : ℚ) / 21, (-26555758178917613184411734876701261926681250000000 : ℚ) / 21, (10799755813125436276985030993801919904231250000000 : ℚ) / 21, (7792247885341549011825820245674382010903125000000 : ℚ) / 7, (-14392302559475326093921801625458487007181250000000 : ℚ) / 7, (21147554100061369204006454680730912081645546875000 : ℚ) / 21, (22936524597482243806183698046969031908616640625000 : ℚ) / 21, (-38194534065726381781832325593271135966718109375000 : ℚ) / 21, (14485913433616083400893006079872655569694840625000 : ℚ) / 21, (3492590306080505284976092127052638386133168125000 : ℚ) / 7, (-10821523196226430656535087804571491096681454375000 : ℚ) / 21, (40401190020865415268888686068320696560689625000 : ℚ) / 1, (1785924466055212903204993853480274636047838625000 : ℚ) / 21, (-310954809456185527003495245759040799001149750000 : ℚ) / 7, (40523338970933805243786552780456327485582875000 : ℚ) / 21, (160701663498434597695483350982824084264261418750 : ℚ) / 21, (-43545291430824237861260047346350125515481081250 : ℚ) / 21, (-6456998581583681306533345820973971485796420000 : ℚ) / 21, (5967328434544737366803146910823370891911764500 : ℚ) / 21, (-511027541239784009504707613483160791442219550 : ℚ) / 21, (-86867637139252816341832535865591782004473400 : ℚ) / 7, (26054194062600599889165900708957518411071980 : ℚ) / 7, (72554082543412533337347987443865845447080 : ℚ) / 21, (-3057002739204582595651820900266781596324900 : ℚ) / 21, (484149065511316743257985520215363218453950 : ℚ) / 21, (7380295939774809662846145067881886492450 : ℚ) / 3, (-4995905393960694180303477496508955947370 : ℚ) / 7, (1028709888868699986351433195072622365030 : ℚ) / 21, (358079061073288052650719448575644690050 : ℚ) / 21, (-17610337202211474585659209667179964450 : ℚ) / 21, (-401034302548768237397717754728625250 : ℚ) / 21, (712237237081876683118260758892105710 : ℚ) / 21, (45630797918894606439331469232641870 : ℚ) / 21]

def block46Margin0 : ℚ := (45131660117729261775041804227530400461205858473497255214764110070203601873574317200379101869 : ℚ) / 48103633715200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_0 : ∀ i : Fin 37, block46Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block46PowerCoefficients
      block46Margin0 (by norm_num) block46_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin1 : ℚ := (330341376415970937019464392198567403466793797892607173480013804489152900437340799 : ℚ) / 700000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_1 : ∀ i : Fin 37, block46Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block46PowerCoefficients
      block46Margin1 (by norm_num) block46_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin2 : ℚ := (1723141717314776951280149015843682711418877239034486759803775619886921629959786355943203027 : ℚ) / 6871947673600000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_2 : ∀ i : Fin 37, block46Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block46PowerCoefficients
      block46Margin2 (by norm_num) block46_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin3 : ℚ := (476215489559342770590429129162977686867256933339507316589229505966504 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_3 : ∀ i : Fin 37, block46Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block46PowerCoefficients
      block46Margin3 (by norm_num) block46_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin4 : ℚ := (2929614612090907131173502642184068319674573917721432312836221803848478377 : ℚ) / 19874233159098575093760000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_4 : ∀ i : Fin 37, block46Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block46PowerCoefficients
      block46Margin4 (by norm_num) block46_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin5 : ℚ := (2451930075211354767455684877658673055275640600828168551063321037585 : ℚ) / 16528282690043758247936

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_5 : ∀ i : Fin 37, block46Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block46PowerCoefficients
      block46Margin5 (by norm_num) block46_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin6 : ℚ := (121234342956872757682755175768026323278420458806268837882953598539515036953849699 : ℚ) / 700000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_6 : ∀ i : Fin 37, block46Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block46PowerCoefficients
      block46Margin6 (by norm_num) block46_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin7 : ℚ := (1547204939738601161654359963546714907280040699681213627571861768592186011567684996946956307 : ℚ) / 6871947673600000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_7 : ∀ i : Fin 37, block46Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block46PowerCoefficients
      block46Margin7 (by norm_num) block46_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block46Margin8 : ℚ := (6178016576308920040080178662531394519610121081101575170050074539982848 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block46_coefficient_bound_8 : ∀ i : Fin 37, block46Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block46PowerCoefficients) i := by
  decide +kernel

theorem block46_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block46Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block46PowerCoefficients
      block46Margin8 (by norm_num) block46_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block46_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block46PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block46_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block46_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block46_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block46_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block46_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block46_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block46_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block46_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block46_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
