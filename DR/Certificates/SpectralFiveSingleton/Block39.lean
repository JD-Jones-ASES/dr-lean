import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (5,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block39PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-161722528338952045613829436821056000000000000000 : ℚ) / 7, (2888541069154934462172794915525235200000000000000 : ℚ) / 21, (-465556506981831601325452377819390703000000000000 : ℚ) / 1, (62593411914626495814077150572287926458718750000000 : ℚ) / 63, (-79448286927421107951781162247182874536815625000000 : ℚ) / 63, (38373578397480034163456988489482190039509375000000 : ℚ) / 63, (6177313554613711842023214131715497157284375000000 : ℚ) / 7, (-112053758576375385329095470368311041367723046875000 : ℚ) / 63, (18531826455677586457703880247809572768042148437500 : ℚ) / 21, (6798986340035626935717472007389612554269960937500 : ℚ) / 7, (-99656856681809907313088614392515024848755710937500 : ℚ) / 63, (35712250698798187192857958944041571834231992187500 : ℚ) / 63, (3277948963614140855393625644365949784414789687500 : ℚ) / 7, (-27644486656935351633141699203679527085123430156250 : ℚ) / 63, (177118073952461128914106257397618189121540562500 : ℚ) / 9, (4885898411740850597589476552837211016390459906250 : ℚ) / 63, (-2188592194395529209529121570201036206376837875000 : ℚ) / 63, (13000759258381995333868493930537523179926906250 : ℚ) / 63, (390482569116999987885077463230446556844695462500 : ℚ) / 63, (-33274653929546399817627672065350061229118306250 : ℚ) / 21, (-5103557400511342446583077678567502881475280000 : ℚ) / 21, (2140953045104586535960861289480847373430117500 : ℚ) / 9, (-1262199782570404303674975278252182790657779600 : ℚ) / 63, (-105605820865093593151091645686824897697435600 : ℚ) / 9, (176776934017723275310179327509894756338657280 : ℚ) / 63, (1894447253745608698732079955624682963998160 : ℚ) / 63, (-124096540013731575161379413956761511386100 : ℚ) / 1, (143443167423432835959215499497199803491700 : ℚ) / 9, (122952539294014310368372515180229479624500 : ℚ) / 63, (-37741386211662060982280188160219021671820 : ℚ) / 63, (153822572610556517248743990658100836340 : ℚ) / 7, (758857812150936812485812691393159327600 : ℚ) / 63, (-15721014860685717183036423264570973300 : ℚ) / 21, (-3503116639429006780266054082121670700 : ℚ) / 63, (186491087146786652404224265559492860 : ℚ) / 9, (91261595837789212878662938465283740 : ℚ) / 63]

def block39Margin0 : ℚ := (70170967992823011511147742376115961691141880543321892980728805961103927997628256549121580069 : ℚ) / 72155450572800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_0 : ∀ i : Fin 37, block39Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block39PowerCoefficients
      block39Margin0 (by norm_num) block39_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin1 : ℚ := (26159733514227597485034725214248105691100559864200637343765854546775226993416519 : ℚ) / 50000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_1 : ∀ i : Fin 37, block39Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block39PowerCoefficients
      block39Margin1 (by norm_num) block39_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin2 : ℚ := (1063536634146804355697550029205207532950687458547127356456340355246507939812677712786004409 : ℚ) / 3435973836800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_2 : ∀ i : Fin 37, block39Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block39PowerCoefficients
      block39Margin2 (by norm_num) block39_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin3 : ℚ := (4592285218025963182493123754580545323513907497447830635559405970036752 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_3 : ∀ i : Fin 37, block39Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block39PowerCoefficients
      block39Margin3 (by norm_num) block39_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin4 : ℚ := (7319749515130541295174364510683508863468893412368367759504842233592541817 : ℚ) / 34779908028422506414080000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_4 : ∀ i : Fin 37, block39Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block39PowerCoefficients
      block39Margin4 (by norm_num) block39_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin5 : ℚ := (1750121678386925868782886089756988094091257632206207409693426619395 : ℚ) / 8264141345021879123968

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_5 : ∀ i : Fin 37, block39Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block39PowerCoefficients
      block39Margin5 (by norm_num) block39_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin6 : ℚ := (11945512491948212385182174420526687676390506568957542678994828984678576981448019 : ℚ) / 50000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_6 : ∀ i : Fin 37, block39Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block39PowerCoefficients
      block39Margin6 (by norm_num) block39_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin7 : ℚ := (3044775982289977770213302471634678068364993075587895725403485211625318814098668985178204107 : ℚ) / 10307921510400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_7 : ∀ i : Fin 37, block39Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block39PowerCoefficients
      block39Margin7 (by norm_num) block39_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block39Margin8 : ℚ := (7780600902055946977267441407118119576796579669184239168917762755346432 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block39_coefficient_bound_8 : ∀ i : Fin 37, block39Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block39PowerCoefficients) i := by
  decide +kernel

theorem block39_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block39Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block39PowerCoefficients
      block39Margin8 (by norm_num) block39_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block39_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block39PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block39_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block39_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block39_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block39_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block39_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block39_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block39_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block39_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block39_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
